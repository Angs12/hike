(* Hike_stack_model — THE PURE STACK MODEL (architecture review
   2026-09-02, candidate #1 part 2): the decision functions
   ([regions_of_sub], [split_plan], [frame_escapes],
   [abi_visibility_of]), their shared rules ([is_abi_visible],
   [region_bytes], the escape analyses, the tag-coverage checks) and
   the helpers they own.  This was [hike_stack_to_locals]'s first
   800 lines — the model, not the pass: it reads NO KB, no Project,
   no pass state; its inputs are the sub, the target, and the
   computed [Convutils.vsa_info].  The REWRITE PASS
   ([stack_to_locals] — the Exp.mapper conversion) stays in
   [hike_stack_to_locals] and imports this module; [hike_vsa]'s
   [offsets_of_sub] composes this whole chain (the ONE producer of
   the record). *)

open Bap.Std
open Bap.Std.Bil.Types
open Bap_core_theory
module Abi = Hike_abi

let fp_of (target : Theory.Target.t) : var option =
  if Theory.Target.is_unknown target then None
  else
    match Abi.fp target with
    | v -> Some v
    | exception _ -> None

let is_sp_or_fp (sp : var) (target : Theory.Target.t) (v : var) : bool =
  Var.same (Var.base v) (Var.base sp)
  ||
  match fp_of target with
  | Some fp -> Var.same (Var.base v) (Var.base fp)
  | None -> false

let addr_of_rhs (e : exp) : (exp * Size.t) option =
  match e with
  | Bil.Load (_, a, _, s) | Bil.Store (_, a, _, _, s) -> Some (a, s)
  | Bil.Cast (_, _, Bil.Load (_, a, _, s))
  | Bil.Cast (_, _, Bil.Store (_, a, _, _, s)) -> Some (a, s)
  | _ -> None

(* The stored data of a (possibly cast-wrapped) store rhs, with the
   wrapper that rebuilds the enclosing cast around the rewritten
   store. *)
let store_data_of_rhs (e : exp) : (exp * (exp -> exp)) option =
  match e with
  | Bil.Store (_, _, data, _, _) -> Some (data, fun x -> x)
  | Bil.Cast (c, w, Bil.Store (_, _, data, _, _)) ->
      Some (data, fun x -> Bil.Cast (c, w, x))
  | _ -> None

let slot_of (lo : int64) (bits : int) : var =
  Var.create ~is_virtual:false ~fresh:false
    (Printf.sprintf "slot_%Ld" (Int64.abs lo))
    (Type.Imm bits)

let arr_of (lo : int64) (hi : int64) : var =
  Var.create ~is_virtual:false ~fresh:false
    (Printf.sprintf "arr_%Ld_%Ld" lo hi)
    (Type.Mem (Size.addr_of_int_exn 64, Size.of_int_exn 8))

(* Defs that save incoming register args; keep them in memory so va_arg pointer reads alias correctly. *)
let saves_incoming_reg (abi : Abi.t) (d : def term) : bool =
  let param_regs = abi.Abi.int_param_regs @ abi.Abi.vector_param_regs in
  match Def.rhs d with
  | Bil.Store (_, _, data, _, _) -> (
      match data with
      | Bil.Var v ->
          Base.List.exists param_regs
            ~f:(fun r -> Var.same r (Var.base v))
      | _ -> false)
  | _ -> false

(* Compute stack regions: S1 coarser (ADR 0004) — maximal overlap components with
   rlo=min lo, rhi=max hi. Convertible if every member has lo<0 and is not an
   incoming-register save; overlapping Ranges merge (not identical). Infinite
   tags excluded from normal regions — S2 caps them to one big stack_rN in the
   emitter; VLA excluded. *)
let is_real_call (j : jmp term) : bool =
  match Jmp.kind j with
  | Call c -> (
      match Call.target c with
      | Direct _ -> true
      | Indirect _ -> Option.is_some (Call.return c))
  | _ -> false

(* [sp_escaped sp target sub]: does a stack-frame ADDRESS escape the
   sub? See the SP-ESCAPE RULE comment below. *)
let sp_escaped (sp : var) (target : Theory.Target.t) (sub : sub term) :
  bool =
  let base_var v = Var.base v in
  let sp_base = base_var sp in
  let fp_bases =
    match fp_of target with Some fp -> [ base_var fp ] | None -> []
  in
  (* [derived]: the vars whose values are sp/fp-derived — SP, FP (when the
     target declares one) and every temp defined from them through
     every temp defined from them through ARITHMETIC (BinOp/Cast/
     Extract/Concat); a LOAD's result is NOT derived (a value read
     from memory is not an address expression on the frame), and a
     memory side-effect's lhs ([mem]) is not derived. Computed as a
     block-local fixpoint via the def chain (the -O0 shape computes
     the address in one def; the closure covers multi-def chains). *)
  let derived : Var.Set.t ref =
    ref (Var.Set.of_list (sp_base :: fp_bases))
  in
  let is_memory_shape (e : exp) : bool =
    (* a Load/Store anywhere in the rhs makes the def a memory
       access — its lhs is a loaded value or the mem var, never an
       address computation (visitor-based, per Principle 8). *)
    let vis =
      object
        inherit [ bool ] Exp.visitor
        method! visit_load ~mem:_ ~addr:_ _ _ acc = acc || true
        method! visit_store ~mem:_ ~addr:_ ~exp:_ _ _ acc = acc || true
      end
    in
    vis#visit_exp e false
  in
  let rec grow () =
    let changed = ref false in
    Term.enum blk_t sub
    |> Seq.iter ~f:(fun blk ->
        Term.enum def_t blk
        |> Seq.iter ~f:(fun d ->
            let rhs = Def.rhs d in
            if not (is_memory_shape rhs) then begin
              let uses = Exp.free_vars rhs in
              if
                Core.Set.exists uses ~f:(fun v ->
                    Core.Set.mem !derived (base_var v))
              then begin
                let lhs = base_var (Def.lhs d) in
                if not (Core.Set.mem !derived lhs) then (
                  derived := Core.Set.add !derived lhs;
                  changed := true)
              end
            end));
    if !changed then grow () else ()
  in
  grow ();
  (* an sp/fp-derived value ESCAPES when it is (a) assigned to a
     register in a CALL BLOCK (the -O0 arg setup: [RDI := RBP - 0x30]
     right before [call] — the callee receives the frame address),
     (b) stored as a memory store's DATA (the escaped-pointer
     record), or (c) an indirect call's target. The push lane
     ([RSP := RSP - 8], [mem[RSP] := retaddr]) is excluded: it is
     dead model traffic (the lifted callee returns via a real LLVM
     ret, never popping the model RSP). *)
  (* [value_free_vars e]: the free vars of the VALUE [e] computes —
     a Load/Store contributes NOTHING (the loaded/stored value is
     not an address expression on the frame: [mem[RBP-8] + 1] as a
     stored data has NO sp-derived vars — the RBP in the load's
     ADDRESS is not part of the VALUE); a Store-as-value contributes
     its data's vars (the store's value semantics is the data). *)
  let rec value_free_vars (e : exp) : Var.Set.t =
    let vis =
      object
        inherit [ Var.Set.t ] Exp.visitor
        method! visit_var v acc = Core.Set.add acc (base_var v)
        method! visit_load ~mem:_ ~addr:_ _ _ acc = acc
        method! visit_store ~mem:_ ~addr:_ ~exp:data _ _ acc =
          Core.Set.union acc (value_free_vars data)
      end
    in
    vis#visit_exp e Var.Set.empty
  in
  let exp_escapes (e : exp) : bool =
    Core.Set.exists (value_free_vars e) ~f:(fun v ->
        Core.Set.mem !derived (base_var v))
  in
  let call_arg_escapes =
    (* only the ARGUMENT-REGISTER defs count (the SysV param regs —
       [RDI/RSI/RDX/RCX/R8/R9] + the YMM FP args): a derived value
       reaching an arg register is a frame address passed to the
       callee. The push/pop FLAG defs ([OF := high:1[(#t ^ 8) &
       (#t ^ RSP)]] of [RSP := RSP - 8]) reference derived temps
       and sit in the same call block — they are dead model traffic,
       never an escape. *)
    let is_arg_reg (v : var) : bool =
      Base.List.exists (Abi.param_regs target)
        ~f:(fun r -> Var.same r (base_var v))
    in
    Term.enum blk_t sub
    |> Seq.exists ~f:(fun blk ->
        let has_call =
          Term.enum jmp_t blk
          |> Seq.exists ~f:is_real_call
        in
        if not has_call then false
        else
          Term.enum def_t blk
          |> Seq.exists ~f:(fun d ->
              is_arg_reg (Def.lhs d)
              && not (is_memory_shape (Def.rhs d))
              && exp_escapes (Def.rhs d))
          || (Term.enum jmp_t blk
              |> Seq.exists ~f:(fun j ->
                  match Jmp.kind j with
                  | Call c -> (
                      match Call.target c with
                      | Indirect e -> exp_escapes e
                      | _ -> false)
                  | _ -> false)))
  in
  let store_data_escapes =
    Term.enum blk_t sub
    |> Seq.exists ~f:(fun blk ->
        Term.enum def_t blk
        |> Seq.exists ~f:(fun d ->
            match store_data_of_rhs (Def.rhs d) with
            | Some (data, _) ->
                if exp_escapes data then
                  match addr_of_rhs (Def.rhs d) with
                  | Some (addr, _) ->
                      let bare_sp =
                        match addr with
                        | Bil.Var v -> Var.same (base_var v) sp_base
                        | _ -> false
                      in
                      not bare_sp
                  | None -> false
                else false
            | None -> false))
  in
  call_arg_escapes || store_data_escapes

(* [regions_of_sub sp target sub info ~frame_escaped]: merge [info]'s
   overlapping access ranges into Stack Regions, flagging each one's
   convertibility.

   [~frame_escaped] is the ESCAPE verdict for the sub (see
   [frame_escapes] below), passed in rather than recomputed: it is a
   per-region convertibility rule ([stack_to_locals] consults
   [convertible] even on the fallback path) while [frame_escapes] itself
   is defined later in the file. *)
let regions_of_sub (sp : var) (target : Theory.Target.t) (sub : sub term)
    (info : Convutils.vsa_info) ~(frame_escaped : bool) :
    Convutils.region list =
  (* [offsets]/[k_ranges] are MAPS: [k_of] is the record's own field (no
     refold), and [ranges] filters [offsets] in one pass. *)
  let k_of = info.Convutils.k_ranges in
  let ranges : (int64 * int64) Tid.Map.t =
    Core.Map.filter_map info.Convutils.offsets ~f:(fun kind ->
      match kind with
      | Convutils.Range (lo, hi) -> Some (lo, hi)
      | Convutils.Infinite _ | Convutils.Unbounded | Convutils.Dead | Convutils.VLA _ -> None)
  in
  let abi =
    (* TOTAL: the unit fixtures analyze [Theory.Target.unknown], which has
       no convention record — fall back to the x86_64 record's vars (the
       fixture sp is the "RSP"-named var either way). *)
    Option.value (Abi.of_target_opt target) ~default:Abi.x86_64_sysv
  in
  let overlap (lo1 : int64) (hi1 : int64) (lo2 : int64) (hi2 : int64) :
      bool =
    Int64.compare lo1 hi2 <= 0 && Int64.compare lo2 hi1 <= 0
  in
  let ranges_overlap ((lo1, hi1) : int64 * int64)
      ((lo2, hi2) : int64 * int64) : bool =
    overlap lo1 hi1 lo2 hi2
  in
  let def_of_tid : def term Tid.Map.t =
    Term.enum blk_t sub
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun m blk ->
           Term.enum def_t blk
           |> Seq.fold ~init:m ~f:(fun m d ->
                  Core.Map.set m ~key:(Term.tid d) ~data:d))
  in
  let def_width : int Tid.Map.t =
    Term.enum blk_t sub
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun m blk ->
           Term.enum def_t blk
           |> Seq.fold ~init:m ~f:(fun m d ->
                  match addr_of_rhs (Def.rhs d) with
                  | Some (_, s) ->
                      Core.Map.set m ~key:(Term.tid d) ~data:(Size.in_bits s)
                  | None -> m))
  in
  (* The CALL-TAIL OUTGOING-ARG SET: in a call block, the stack defs from
     the block's LAST stack def back to the retaddr push ([RSP := RSP - 8;
     mem[RSP] := retaddr] — the lifter's final action before the call
     edge) are the OUTGOING-ARG AREA: the callee reads them at
     [hike_stack + (k+8)] (its entry-RSP view of the caller's arg slots).
     They belong to the CALLER-CALLEE ABI LANE, which the callee reads
     through the [hike_stack] pointer into the CALLER's model frame —
     they must NOT convert to private stack_rN allocas (the callee would
     read a different storage — the factorial inc(…) crash class), and a
     sub with outgoing stack traffic cannot be region split at all (the
     write-closed rule at sub granularity: the callee-facing lane
     coheres in the model frame). The retaddr push itself is dead
     traffic on the model lane (the lifted callee returns via a real
     LLVM ret, never popping the model RSP) — it stays convertible. *)
  (* [is_real_call j]: a call edge that passes outgoing stack args —
     a DIRECT-target call (any return mode: a tail call still passes
     its args) or an INDIRECT call WITH a return (a computed callee
     that returns). The RETURN EPILOGUE ([#t := mem[RSP]; RSP :=
     RSP + 8; call #t with noreturn] — the DCE lane's target) is a
     noreturn INDIRECT call: it passes NO arguments (it is the
     return continuation), so an epilogue block is NOT a call block
     (the prologue push inside it must not land in any tail). *)
  let outgoing_tail_tids : Tid.Set.t =
    Term.enum blk_t sub
    |> Seq.fold ~init:Tid.Set.empty ~f:(fun acc blk ->
           if
             Term.enum jmp_t blk
             |> Seq.exists ~f:is_real_call
           then
             let defs = Term.enum def_t blk |> Seq.to_list in
             let is_stack d = Term.has_attr d Hike_vsa_relevance.stack_access in
             let last =
               Base.List.foldi defs ~init:None ~f:(fun i acc d ->
                   if is_stack d then Some i else acc)
             in
             match last with
             | Some i ->
                 Base.List.take defs i
                 |> Base.List.fold_left ~init:acc ~f:(fun acc d ->
                         Core.Set.add acc (Term.tid d))
             | None -> acc
           else acc)
  in
   (* [has_outgoing_stack_args]: does the sub have ANY call-tail stack
      store (the ABI lane with real callee-visible traffic)? — the sub
      granularity gate for region splitting. Only RSP-relative STORES
      count: the tail also holds the caller's own RBP-relative
      arg-setup LOADS (reads of its locals feeding the register args),
      which are ordinary convertible accesses. The retaddr push is NOT
      counted: it is the call block's LAST stack def, which the tail
      set already excludes (an Int-literal store at RSP inside the
      tail is the 7th-arg STORE — real outgoing traffic, e.g.
      [mem[RSP] := 1] of [inc(...,1)]). *)
  (* [is_outgoing_store]: the RSP-relative stack STORE with a NEGATIVE
     k-range (below the ENTRY rsp — the pushed outgoing-arg cell the
     callee reads at [hike_stack + |k|]). The k-sign discriminates the
     push/pop lane from the arg lane: the retaddr push sits AT the
     current rsp (k = 0 — dead model traffic, the lifted callee
     returns via a real LLVM ret), the 7th-arg store sits BELOW the
     entry rsp (k < 0 — real callee-visible traffic, the
     [inc(...,1)] class). *)
  let is_outgoing_store (d : def term) : bool =
    match store_data_of_rhs (Def.rhs d) with
    | Some (_data, _) -> (
        match addr_of_rhs (Def.rhs d) with
        | Some (addr, _) ->
            let rsp_rel =
              Exp.free_vars addr
              |> Core.Set.exists ~f:(Abi.is_sp_t target)
            in
            (* the tag's ENTRY-relative offset lo < 0 (below the
               entry rsp — the pushed outgoing-arg cell, e.g. the
               7th-arg store [mem[RSP] := 1] of [inc(...,1)] whose
               tag is Range(-40,-40)) plus the k-range k >= 0 (AT
               the current rsp — the pushed-arg shape). The
               prologue push ([mem[RSP] := RBP]) also has lo<0
               k>=0 — the discriminator is the TAIL membership: the
               prologue is not in any call block's tail. *)
            let lo_neg =
              match Core.Map.find ranges (Term.tid d) with
              | Some (lo, _) -> Int64.compare lo 0L < 0
              | None -> false
            in
            let k_pos =
              match Core.Map.find k_of (Term.tid d) with
              | Some (klo, _) -> Int64.compare klo 0L >= 0
              | None -> false
            in
            rsp_rel && lo_neg && k_pos
        | None -> false)
    | None -> false
  in
  (* LAZY: the whole-sub call-tail scan only matters when a region's
     member rules admit conversion, and [regions_of_sub] runs once per
     sub in the vsa pass. Computed at most once per call. *)
  let has_outgoing_stack_args : bool lazy_t =
    lazy
      (Term.enum blk_t sub
      |> Seq.exists ~f:(fun blk ->
             if
               Term.enum jmp_t blk
               |> Seq.exists ~f:is_real_call
             then
               Term.enum def_t blk
               |> Seq.exists ~f:(fun d ->
                      Core.Set.mem outgoing_tail_tids (Term.tid d)
                      && is_outgoing_store d)
             else false))
  in
  (* THE SP-ESCAPE RULE (the rec_struct class): a stack-frame address
     ([RBP - 0x30] — the address of the caller's local struct) that
     ESCAPES (is passed as a call argument or stored as data into
     memory) makes the frame addressable from OUTSIDE the sub — the
     callee (or a later dereference) reads the slot THROUGH the model
     frame address, so the slot it points into must stay in the model
     frame (converting it to a private stack_rN alloca would rebind
     the storage the escaped pointer still points into — the callee
     reads garbage). [escaped_addr_tids]: the defs of the sub whose
     stack STORE stores an address-bearing value that derives from
     SP/FP (the escaped-pointer WRITES — [cur.next := RBP-0x30-class]
     is a plain spill of an escaped address and stays convertible;
     what must stay memory is what the ADDRESS ESCAPE makes reachable),
     and the defs whose STACK ADDRESS is passed as a call arg. Both
     compute to: ANY stack traffic escapes when an sp/fp-derived
     expression reaches a call argument or a memory store's DATA —
     conservative, sound, no precision loss for the common case (no
     program that never takes a frame address ever trips it). *)
  (* [is_direct_const_addr addr]: is the access address a DIRECT
     constant-offset frame access — [sp/fp ± const] (or a bare const),
     with NO index var and NO derived temp: the address the VSA proved
     a constant offset ([RBP - 4]), the shape the per-cell conversion
     rewrites. An INDEXED ([RBP + i*4 - 0x70]) or DYNAMIC ([RAX] of
     [RAX := RBP - 0x30]) address reads/writes through the MODEL
     FRAME at emission even when its VSA range is a singleton — the
     write-closed rule needs the region's EVERY member direct. *)
  let rec is_direct_const_addr ~(sp : var) ~(target : Theory.Target.t) (addr : exp) : bool =
    let base_var v = Var.base v in
    let is_base v = is_sp_or_fp sp target (base_var v) in
    match addr with
    | Bil.Int _ -> true
    | Bil.Var v -> is_base v
    | Bil.BinOp ((Bil.PLUS | Bil.MINUS), Bil.Var v, Bil.Int _)
    | Bil.BinOp ((Bil.PLUS | Bil.MINUS), Bil.Int _, Bil.Var v) ->
        is_base v
    | Bil.Cast (_, _, e) -> is_direct_const_addr ~sp ~target e
    | _ -> false
  in
  let components : (tid * (int64 * int64)) list list =
    let items : (tid * (int64 * int64)) list = Core.Map.to_alist ranges in
    (* Maximal overlap components: iterative merge of overlapping singles
       until fixpoint. Two components overlap if any member of one overlaps
       any member of the other (transitive closure). *)
    let components_overlap (c1 : (tid * (int64 * int64)) list)
        (c2 : (tid * (int64 * int64)) list) : bool =
      Base.List.exists c1 ~f:(fun (_, r1) ->
          Base.List.exists c2 ~f:(fun (_, r2) -> ranges_overlap r1 r2))
    in
    let rec merge_loop comps =
      let n = List.length comps in
      let rec find_pair i =
        if i >= n then None
        else
          let ci = List.nth comps i in
          let rec find_j j =
            if j >= n then find_pair (i + 1)
            else if i = j then find_j (j + 1)
            else
              let cj = List.nth comps j in
              if components_overlap ci cj then Some (i, j) else find_j (j + 1)
          in
          find_j (i + 1)
      in
      match find_pair 0 with
      | None -> comps
      | Some (i, j) ->
          let ci = List.nth comps i and cj = List.nth comps j in
          let merged = ci @ cj in
          let comps' =
            Base.List.filteri comps ~f:(fun k _ -> k <> i && k <> j)
          in
          merge_loop (merged :: comps')
    in
    let init = Base.List.map items ~f:(fun x -> [ x ]) in
    merge_loop init
  in
  Base.List.foldi components ~init:[] ~f:(fun i acc members ->
      let span =
        match members with
        | [] -> (0L, 0L)
        | (_, (lo0, hi0)) :: rest ->
            Base.List.fold_left rest ~init:(lo0, hi0)
              ~f:(fun (l, h) (_, (lo, hi)) ->
                (Int64.min l lo, Int64.max h hi))
      in
      let convertible =
        match members with
        | [] -> false
        | _ ->
            let res = Base.List.for_all members ~f:(fun (mtid, (lo, _)) ->
                Int64.compare lo 0L < 0
                && (match Core.Map.find def_of_tid mtid with
                    | Some md -> not (saves_incoming_reg abi md)
                    | None -> true)
                (* the member's own access must be DIRECT-CONSTANT
                   ([mem[RBP - 4]]): an INDEXED/DYNAMIC address
                   ([mem[RBP + i*4 - 0x70]], [mem[RAX]] with
                   [RAX := RBP - 0x30]) reads/writes the MODEL FRAME
                   at emission (the dynamic-inttoptr path) — if the
                   same cell's direct accesses converted to the
                   private alloca, the storage splits (the
                   write-closed rule: together or not at all). The
                   member-level tail exclusion is NOT needed: the ABI
                   lane's k<0 RSP-relative stores already force the
                   whole sub big-frame ([has_outgoing_stack_args]);
                   the tail's other members (the arg-setup loads —
                   reads of the caller's own locals) are ordinary
                   convertible accesses. *)
                && (match Core.Map.find def_of_tid mtid with
                    | Some md ->
                        (match addr_of_rhs (Def.rhs md) with
                         | Some (addr, _) ->
                             let ok = is_direct_const_addr ~sp ~target addr in
                             if not ok && Sys.getenv_opt "HIKE_VSA_DEBUG" <> None then
                               Printf.eprintf "hike:   member %s NOT direct: addr=%s\n"
                                 (Tid.name mtid)
                                 (Format.asprintf "%a" Exp.pp addr);
                             ok
                         | None -> true)
                    | None -> true)) in
            if not res && Sys.getenv_opt "HIKE_VSA_DEBUG" <> None then (
              let lo0, hi0 = span in
              Printf.eprintf "hike: region %d span=(%Ld,%Ld) NOT convertible: members=%d\n" i lo0 hi0 (List.length members);
              Printf.eprintf "hike:   (sub %s)\n" (Sub.name sub);
              Base.List.iter members ~f:(fun (mtid, (lo, hi)) ->
                  let k_str = match Core.Map.find k_of mtid with Some (klo, khi) -> Printf.sprintf "(%Ld,%Ld)" klo khi | None -> "None" in
                  let saves = match Core.Map.find def_of_tid mtid with Some md -> saves_incoming_reg abi md | None -> false in
                  Printf.eprintf "hike:   member %s (%Ld,%Ld) k=%s saves=%b\n" (Tid.name mtid) lo hi k_str saves);
            );
            res
            && not (Lazy.force has_outgoing_stack_args)
            (* The ESCAPE gate is a PER-REGION convertibility rule (it
               belongs to [regions_of_sub], whose [convertible] flag
               [stack_to_locals] consults even on the fallback path —
               the cells it converts there must respect it too), NOT a
               whole-sub rule of [split_plan]. The unified escape
               analysis ([frame_escapes] — the value-escape half plus the
               frame-address-alias half) is what replaced the two
               analyses that used to disagree. *)
            && not frame_escaped
      in
      let max_width =
        Base.List.fold_left members ~init:0 ~f:(fun m (mtid, _) ->
            Int.max m
              (Option.value ~default:64 (Core.Map.find def_width mtid)))
      in
      {
        Convutils.id = i;
        Convutils.span = span;
        Convutils.members = members;
        Convutils.convertible = convertible;
        Convutils.max_width = max_width;
      }
      :: acc)
  |> Base.List.rev

(* [is_abi_visible sp ~tag_of ~k_of d]: THE ABI-VISIBILITY rule — does this
   access touch storage the CALLER or CALLEE can see, so it must stay in
   real memory (never a private [stack_rN] alloca)?

   [lo >= 0] is the incoming-arg area (entry-relative) — the callee's own
   view of the args its caller pushed. [lo < 0] with [k >= 0] on an
   SP-relative address is the OUTGOING-arg cell (the 7th-arg store of
   [inc(...,1)] — the callee reads it at [hike_stack + |k|]). Local stack
   slots are [lo < 0, k < 0].

   Finding 1: this rule had TWO copies (here and in [Bil2llvm]); the
   emitter now calls this one. [sp] is the target's stack pointer. *)
let is_abi_visible (sp : var)
    ~(tag_of : Convutils.vsa_kind Tid.Map.t)
    ~(k_of : (int64 * int64) Tid.Map.t) (d : def term) : bool =
  match Core.Map.find tag_of (Term.tid d) with
  | Some (Convutils.Range (lo, _)) when Int64.compare lo 0L >= 0 -> true
  | Some (Convutils.Range (lo, _)) -> (
      match Core.Map.find k_of (Term.tid d) with
      | Some (klo, _) when Int64.compare klo 0L >= 0 -> (
          match addr_of_rhs (Def.rhs d) with
          | Some (addr, _) ->
              Exp.free_vars addr
              |> Core.Set.exists ~f:(fun v ->
                     Var.same (Var.base v) (Var.base sp))
          | None -> false)
      | _ -> false)
  | _ -> false

(* [abi_visibility_of sp info]: the [is_abi_visible] closure over one
   sub's [vsa_info] — the form the emitter uses. *)
let abi_visibility_of (sp : var) (info : Convutils.vsa_info) :
    def term -> bool =
  is_abi_visible sp ~tag_of:info.Convutils.offsets ~k_of:info.Convutils.k_ranges

(* ------------------------------------------------------------------ *)
(* THE STACK MODEL DECISION — the single producer ([split_plan]).       *)
(*                                                                     *)
(* Ported here from [Bil2llvm.region_split_plan] (Finding 1). Every     *)
(* rule below is a WHOLE-SUB rule: it either admits the sub's stack to  *)
(* be split into per-region [stack_rN] allocas, or forces the sound     *)
(* fallback (one big [%frame] alloca, correct but unoptimized). The      *)
(* per-region [convertible] flag comes from [regions_of_sub] above.     *)
(* ------------------------------------------------------------------ *)

(* [region_bytes r]: the alloca size of region [r] — its span's cells at
   [max_width] bits, 16-aligned, at least one byte. *)
let region_bytes (r : Convutils.region) : int64 =
  let lo, hi = r.Convutils.span in
  let span_len = Int64.add (Int64.sub hi lo) 1L in
  let raw = Int64.div (Int64.mul span_len (Int64.of_int r.Convutils.max_width)) 8L in
  let raw = if Int64.compare raw 0L <= 0 then 1L else raw in
  let r = Int64.rem raw 16L in
  if Int64.equal r 0L then raw else Int64.add raw (Int64.sub 16L r)

(* [region_size_ok r]: the alloca size guard — positive and below the
   64 MiB cap (an absurd span means the VSA did not converge; the
   fallback frame covers it). *)
let region_size_ok (r : Convutils.region) : bool =
  let b = region_bytes r in
  Int64.compare b 0L > 0 && Int64.compare b 67108864L <= 0

(* [is_stack_mem sp target e]: is [e] a stack-memory access — a
   (possibly cast-wrapped) Load/Store whose ADDRESS derives from SP/FP? *)

(* [exp_contains_sp sp target e]: does [e] reference the stack or frame
   pointer? (The memory-node form: a Load/Store's ADDRESS only — the
   loaded value is not an address expression.) *)
let rec exp_contains_sp (sp : var) (target : Theory.Target.t) (e : exp) :
    bool =
  match e with
  | Bil.Var v -> is_sp_or_fp sp target v
  | Bil.BinOp (_, a, b) ->
      exp_contains_sp sp target a || exp_contains_sp sp target b
  | Bil.UnOp (_, a) -> exp_contains_sp sp target a
  | Bil.Cast (_, _, a) -> exp_contains_sp sp target a
  | Bil.Extract (_, _, a) -> exp_contains_sp sp target a
  | Bil.Concat (a, b) ->
      exp_contains_sp sp target a || exp_contains_sp sp target b
  | Bil.Let (_, a, b) ->
      exp_contains_sp sp target a || exp_contains_sp sp target b
  | Bil.Ite (c, a, b) ->
      exp_contains_sp sp target c
      || exp_contains_sp sp target a
      || exp_contains_sp sp target b
  | Bil.Load (_, a, _, _) | Bil.Store (_, a, _, _, _) ->
      exp_contains_sp sp target a
  | _ -> false

let is_stack_mem (sp : var) (target : Theory.Target.t) (e : exp) : bool =
  match e with
  | Bil.Load (_, a, _, _)
  | Bil.Store (_, a, _, _, _)
  | Bil.Cast (_, _, Bil.Load (_, a, _, _))
  | Bil.Cast (_, _, Bil.Store (_, a, _, _, _)) ->
      exp_contains_sp sp target a
  | _ -> false

let frame_value_def (sp : var) (target : Theory.Target.t) (d : def term) :
    bool =
  let lhs = Def.lhs d in
  (not (Convutils.is_mem lhs))
  && (not (is_sp_or_fp sp target lhs))
  && exp_contains_sp sp target (Def.rhs d)

let rec var_maybe_addr (env : exp Var.Map.t) (sp : var)
    (target : Theory.Target.t) (v : var) (e : exp) : bool =
  match e with
  | Bil.Var w ->
      (is_sp_or_fp sp target w && is_sp_or_fp sp target v)
      || Var.same (Var.base w) (Var.base v)
      ||
      (match Core.Map.find env (Var.base w) with
      | Some e' -> var_maybe_addr env sp target v e'
      | None -> false)
  | Bil.Ite (_, t, f) ->
      var_maybe_addr env sp target v t
      || var_maybe_addr env sp target v f
  | Bil.Let (x, e1, e2) ->
      let env' = Core.Map.set env ~key:x ~data:e1 in
      var_maybe_addr env' sp target v e2
  | Bil.Cast (_, _, e') | Bil.Extract (_, _, e') ->
      var_maybe_addr env sp target v e'
  | _ -> false

(* [frame_addr_alias sp target sub]: does some memory access in [sub]
   read/write through a materialized frame pointer (the [v := RSP; t :=
   mem[v]] class)? Then the frame is addressable through that value and
   the sub keeps the model frame (the storage the alias points into must
   not move to a private alloca). *)
let frame_addr_alias (sp : var) (target : Theory.Target.t) (sub : sub term) :
    bool =
  let defs =
    Term.enum blk_t sub |> Seq.concat_map ~f:(Term.enum def_t) |> Seq.to_list
  in
  Base.List.exists defs ~f:(fun d ->
      frame_value_def sp target d
      &&
      let v = Def.lhs d in
      Base.List.exists defs ~f:(fun d2 ->
          match addr_of_rhs (Def.rhs d2) with
          | Some (addr, _) -> var_maybe_addr Var.Map.empty sp target v addr
          | None -> false))

(* [vla_overlaps_convertible info convertible]: does the sub's dynamic
   allocation overlap a convertible region? The VLA's real storage is a
   runtime [alloca] (it cannot live in the static frame), so a region
   that overlaps it must not split (the write-closed rule — the storage
   would straddle two allocations). *)
let vla_overlaps_convertible (info : Convutils.vsa_info)
    (convertible : Convutils.region list) : bool =
  Core.Map.exists info.Convutils.vla_bounds ~f:(fun (_lo, hi) ->
      let max_size = hi in
      if Int64.compare max_size 0L <= 0 then false
      else
        let vla_lo = Int64.neg max_size in
        let vla_hi = -1L in
        Base.List.exists convertible ~f:(fun r ->
            let rlo, rhi = r.Convutils.span in
            not (Int64.compare vla_hi rlo < 0 || Int64.compare vla_lo rhi > 0)))

(* [has_vla_dynamic_alloc sub]: does the sub carry a [dynamic_alloc]
   def (a runtime-sized SP decrement)? An unbounded VLA (no VSA bound)
   overlaps everything by definition. *)
let has_vla_dynamic_alloc (sub : sub term) : bool =
  Term.enum blk_t sub
  |> Seq.exists ~f:(fun blk ->
         Term.enum def_t blk
         |> Seq.exists ~f:(fun d -> Term.has_attr d Hike_vsa_relevance.dynamic_alloc))

(* [has_unbounded_access sub info]: does the sub have a stack memory
   access the VSA could NOT bound — untagged, [Infinite], [Unbounded] or
   [VLA]? Such an access has no sized storage: it stays in the model
   frame, and (the write-closed rule) a sub with one cannot split at all
   (its storage would straddle the private alloca and the frame). *)
let has_unbounded_access (sp : var) (target : Theory.Target.t) (sub : sub term)
    (info : Convutils.vsa_info) : bool =
  (* the record's own map (see [regions_of_sub]). *)
  let tag_of = info.Convutils.offsets in
  Term.enum blk_t sub
  |> Seq.exists ~f:(fun blk ->
         Term.enum def_t blk
         |> Seq.exists ~f:(fun d ->
                is_stack_mem sp target (Def.rhs d)
                &&
                match Core.Map.find tag_of (Term.tid d) with
                | None -> true
                | Some (Convutils.Infinite _) -> true
                | Some Convutils.Unbounded -> true
                | Some (Convutils.VLA _) -> true
                | Some Convutils.Dead -> false
                | Some (Convutils.Range _) -> false))

(* [tags_inside_or_disjoint info convertible]: does EVERY tagged access
   resolve inside a convertible region — or, for the positive
   (incoming-arg) offsets, lie wholly disjoint from all of them (those
   read the CALLER's frame through [hike_stack], never a [stack_rN])?
   An access the plan's regions do not cover would read the wrong
   storage, so it forces the fallback. *)
let tags_inside_or_disjoint (info : Convutils.vsa_info)
    (convertible : Convutils.region list) : bool =
  Core.Map.for_all
    (* the record's own map (see [regions_of_sub]). *)
    info.Convutils.offsets
    ~f:(fun kind ->
      match kind with
      | Convutils.Infinite _ | Convutils.Unbounded -> false
      | Convutils.Dead -> true
      | Convutils.VLA _ -> false
      | Convutils.Range (lo, hi) ->
          let inside =
            Base.List.exists convertible ~f:(fun r ->
                let rlo, rhi = r.Convutils.span in
                Int64.compare lo rlo >= 0 && Int64.compare hi rhi <= 0)
          in
          let disjoint =
            Base.List.for_all convertible ~f:(fun r ->
                let rlo, rhi = r.Convutils.span in
                Int64.compare hi rlo < 0 || Int64.compare lo rhi > 0)
          in
          if Int64.compare lo 0L < 0 then inside else inside || disjoint)

(* [frame_escapes sp target sub]: is the sub's frame ADDRESSABLE FROM
   OUTSIDE, so its stack must stay in the one model frame?

   Finding 1: this is the UNIFIED rule. It replaces the two analyses
   that previously disagreed in both directions — [sp_escaped] (the
   stack-to-locals rule: a derived value reaching a call argument or a
   stored data value) and the emitter's [has_frame_ptr] (a derived value
   reaching a memory ADDRESS, the bare-copy class). Either one makes the
   frame reachable from outside the sub, and a sub whose frame is
   reachable cannot split: a private [stack_rN] alloca would rebind the
   storage an outside pointer still points into. *)
let frame_escapes (sp : var) (target : Theory.Target.t) (sub : sub term) :
    bool =
  sp_escaped sp target sub || frame_addr_alias sp target sub

(* [split_plan sp target sub info]: THE stack model decision — the
   convertible regions that become per-region [stack_rN] allocas, or
   [[]] for the sound single-frame fallback.

   The whole-sub rules, in order:
   1. a degraded / non-convergent VSA falls back (no tags to trust);
   2. an untagged / [Infinite] / [Unbounded] / [VLA] stack access has
      no bound — its storage cannot be a sized alloca (the write-closed
      rule: a sub with one cannot split at all);
      (the ESCAPE rule is NOT a whole-sub rule: it is a PER-REGION
      convertibility rule — see [regions_of_sub]. [stack_to_locals]
      consults [convertible] even on the fallback path, so the escape
      gate must live with the region flag, not here.)
   3. no convertible region means nothing to split;
   4. a VLA overlapping a convertible region splits the storage;
   5. every tagged access must lie INSIDE a convertible region (or,
      for the positive/incoming-arg offsets, be disjoint from all of
      them — those read the caller's frame through [hike_stack]);
   6. the region alloca sizes must be sane. *)
let split_plan (sp : var) (target : Theory.Target.t) (sub : sub term)
    (info : Convutils.vsa_info) : Convutils.split_plan =
  if info.Convutils.degraded then []
  else if has_unbounded_access sp target sub info then []
  else
    let regions = info.Convutils.regions in
    let convertible =
      Base.List.filter regions ~f:(fun r -> r.Convutils.convertible)
    in
    if convertible = [] then []
    else
      let should_degrade_vla =
        vla_overlaps_convertible info convertible
        || (has_vla_dynamic_alloc sub
           && Core.Map.is_empty info.Convutils.vla_bounds)
      in
      if should_degrade_vla then []
      else if not (tags_inside_or_disjoint info convertible) then []
      else if not (Base.List.for_all convertible ~f:region_size_ok) then []
      else convertible

(* [is_precise info]: does [info]'s sub use the split (per-region
   alloca) model? — the consumer-side read of [split_plan] (the dce and
   emitter gates). *)
let is_precise (info : Convutils.vsa_info) : bool = info.Convutils.stack_plan <> []

(* The stored data of a (possibly cast-wrapped) store rhs, with the
   wrapper that rebuilds the enclosing cast around the rewritten store. *)
