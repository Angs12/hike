(* Stack-to-locals: converts stack accesses to local variables, and OWNS
   THE STACK MODEL DECISION ([split_plan] — see Finding 1).

   [split_plan sp target sub info] is the single producer of the answer to
   "does this sub's stack split into per-region [stack_rN] allocas, or fall
   back to one big [%frame]?" Its consumers are this module's rewrite,
   [Hike_dce.is_precise_sub] and [Bil2llvm] (which allocates the plan's
   regions and resolves every stack access against them). The decision was
   previously made three times — here, in [Bil2llvm.region_split_plan] and
   again in [Bil2llvm.create_def]'s arms — with two different escape
   analyses and two copies of each rule; it now has ONE producer. *)

open Bap.Std
open Bap.Std.Bil.Types
open Bap_core_theory
module Abi = Hike_abi

(* Target-derived SP/FP: the sole origin for stack derivation (AGENTS.md
   Principle 8 — never hardcode a register name). [sp] is passed in by the
   passes; [fp_of] derives the frame pointer the same way, and returns
   [None] for a target that declares none ([Theory.Target.unknown] — the
   unit fixtures): such a target has SP-derived addresses only, which is
   the sound (narrower) seed for the derivation closure below. *)
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

(* MEM-FISSION (2026-09-02) — the per-region mem vars.

   [region_mem id]: the region's OWN memory — every Load/Store whose
   address lies in region [id] reads/writes THIS var.  The emitter's
   name-keyed dispatch routes it to the region alloca; the two-tier DCE
   (load-roots only) sees a var whose ONLY uses are Load mem-operands —
   a never-loaded region's stores die in one sweep round (the retaddr
   push cells: dead model traffic, deleted naturally).

   [region_base id]: the region's cell-0 address var (Imm 64 in BIL;
   ptr-bound at emission to the alloca).  The fission rewrite moves the
   ADDRESS into region-relative coordinates: [mem[RBP + i*4 - 0x70]]
   becomes [Load(stack_rN_mem, stack_rN_base + i*4 - 0x70)] — BOTH
   operands name the region, closing the store/load cell-split class
   (the many_args bug: one path's frame GEP vs another's raw lane for
   the same cell).  The base var is entry-bound (see bil2llvm's region
   binding + the definedness closure's name rule). *)
let region_mem (id : int) : var =
  Var.create ~is_virtual:false ~fresh:false
    (Printf.sprintf "stack_r%d_mem" id)
    (Type.Mem (Size.addr_of_int_exn 64, Size.of_int_exn 8))

let region_base (id : int) : var =
  Var.create ~is_virtual:false ~fresh:false
    (Printf.sprintf "stack_r%d_base" id) (Type.Imm 64)

(* The RECOGNIZERS of the fission vars — the name convention is THIS
   module's implementation detail: the two producers above mint the names,
   these predicates read them back, and every consumer (the DCE lane's
   two-tier keep, the emitter's fission dispatch and its φ-lane name rule)
   imports them instead of re-typing the string grammar (one fact, one
   home — the three hand-typed parsers that previously drifted
   independently are gone).  The grammar is deliberately the loose
   prefix/suffix form the consumers always used — this is a
   single-sourcing, not a semantic change. *)
let is_region_mem (v : var) : bool =
  Base.String.is_prefix (Var.name v) ~prefix:"stack_r"
  && Base.String.is_suffix (Var.name v) ~suffix:"_mem"

let is_region_base (v : var) : bool =
  Base.String.is_prefix (Var.name v) ~prefix:"stack_r"
  && Base.String.is_suffix (Var.name v) ~suffix:"_base"

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

(* Compute stack regions: maximal overlap components with rlo=min lo,
   rhi=max hi (the coarser-hull merge). Convertible if every member has
   lo<0 and is not an incoming-register save; overlapping Ranges merge
   (not identical). Infinite tags excluded from normal regions — the
   emitter caps them to one big stack_rN; VLA excluded. *)
let is_real_call (j : jmp term) : bool =
  match Jmp.kind j with
  | Call c -> (
      match Call.target c with
      | Direct _ -> true
      | Indirect _ -> Option.is_some (Call.return c))
  | _ -> false

(* [sp_escaped sp target sub]: does a stack-frame ADDRESS escape the
   sub? See the SP-ESCAPE RULE comment below. *)

(* MEM-FISSION (2026-09-02) — [last_push_tids_of sub]: the call block's
   LAST stack def per block with a real call — THE RETADDR PUSH's tids
   (the same positional fact the exclusive tail-take excludes).  These
   defs are the BAP call expansion's [RSP := RSP - 8; mem[RSP] :=
   retaddr] pair: dead model traffic in the lifted world (the callee's
   epilogue pop dies with [ret_replacement]; the lifted callee returns
   via a real LLVM ret).  Consumed by [is_abi_visible]'s exemption —
   exempting the push store lets its cell form its own never-loaded
   region, which the fission gives a [stack_rN_mem] var with ZERO
   Load-roots, and the two-tier DCE (load-roots only) deletes the store
   chain naturally.  The ONE positional rule of the fission design, and
   it reuses [is_real_call]'s own walk. *)
let last_push_tids_of (sub : sub term) : Tid.Set.t =
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
               Core.Set.add acc (Term.tid (Base.List.nth_exn defs i))
           | None -> acc
         else acc)

let sp_escaped (sp : var) (target : Theory.Target.t) (sub : sub term) :
  bool =
  let base_var v = Var.base v in
  let sp_base = base_var sp in
  let fp_bases =
    match fp_of target with Some fp -> [ base_var fp ] | None -> []
  in
  (* [derived]: the vars whose values are sp/fp-derived — SP, FP (when the
     target declares one) and every temp defined from them through
     ARITHMETIC (BinOp/Cast/Extract/Concat); a LOAD's result is NOT
     derived (a value read
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
  let k_of = info.Convutils.k_ranges in
  let ranges : (int64 * int64) Tid.Map.t =
    Core.Map.filter_map info.Convutils.offsets
      ~f:(fun (kind : Convutils.vsa_kind) ->
        match kind with
        | Convutils.Range (lo, hi) -> Some (lo, hi)
        | Convutils.Infinite _ | Convutils.Unbounded | Convutils.Dead
        | Convutils.VLA _ -> None)
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
  (* MEM-FISSION: the exemption is consumed at CONVERSION time
     ([stack_to_locals]'s is_abi_visible) — the region planner's own
     member rules (the direct-const address test) keep the push store's
     region convertible or not on their own merits. *)
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
     reads garbage). Implemented as two existential checks over the
     sub ([call_arg_escapes], [store_data_escapes] below): ANY stack
     traffic escapes when an sp/fp-derived expression reaches a call
     argument or a memory store's DATA — conservative, sound, no
     precision loss for the common case (no program that never takes
     a frame address ever trips it).  A plain spill of an escaped
     address ([cur.next := RBP-0x30]) stays convertible: what must
     stay memory is what the ADDRESS ESCAPE makes reachable. *)
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
   emitter now calls this one. [sp] is the target's stack pointer.

   The [?last_push_tids] set exempts the RETADDR PUSH (the call-tail's
   last stack def — [last_push_tids_of]): dead model traffic in the
   lifted world (the callee's epilogue pop dies with [ret_replacement];
   the lifted callee returns via a real LLVM ret), so its cell fissions
   into a never-loaded region and the two-tier DCE deletes the store.
   The REAL outgoing-arg stores (the 7th-arg pushes, EARLIER in the
   tail) stay ABI-visible.  The set defaults to empty: [abi_visibility_of]
   (the emitter's form) does NOT thread it — in the production pipeline
   the pass ORDER carries the exemption (hike-stack-to-locals runs
   before hike-dce and hike-convlir: the push defs the fission rewrote
   are region-mem stores the DCE load-roots rule deletes, and the ones
   that stayed Slot-converted are already REWRITTEN to ordinary slot
   defs, so neither kind reaches the emitter as a stack access; a
   caller that runs emission WITHOUT those passes gets the conservative
   ABI-visible answer, which is sound). *)
let is_abi_visible ?(last_push_tids = Tid.Set.empty) (sp : var)
    ~(tag_of : Convutils.vsa_kind Tid.Map.t)
    ~(k_of : (int64 * int64) Tid.Map.t) (d : def term) : bool =
  if Core.Set.mem last_push_tids (Term.tid d) then false
  else
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
   sub's [vsa_info] — the form the emitter uses.  The maps ARE the
   record's precomputed fields now (arch C2: no fold). *)
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
  Base.List.exists info.Convutils.vla_bounds ~f:(fun (_, (_lo, hi)) ->
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
  Term.enum blk_t sub
  |> Seq.exists ~f:(fun blk ->
         Term.enum def_t blk
         |> Seq.exists ~f:(fun d ->
                is_stack_mem sp target (Def.rhs d)
                &&
                match Core.Map.find info.Convutils.offsets (Term.tid d) with
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
  Core.Map.for_all info.Convutils.offsets ~f:(fun (kind : Convutils.vsa_kind) ->
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
   old stack-to-locals rule: a derived value reaching a call argument
   or a stored data value) and the emitter's DELETED has_frame_ptr
   check (a derived value reaching a memory ADDRESS, the bare-copy
   class; removed with the emitter's old region-split plan in the
   Finding-1 commit). Either one makes the
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
           && Base.List.is_empty info.Convutils.vla_bounds)
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
let stack_to_locals (target : Theory.Target.t) (sp : var) (sub : sub term) :
    sub term =
  let info =
    Core.Map.find (Hike_kb.vsa_info ()) (Term.tid sub)
    |> Base.Option.value
         ~default:
           (Convutils.mk_vsa_info ~offsets:[] ~k_ranges:[] ~regions:[]
              ~stack_plan:[] ~degraded:false ~vla_bounds:[])
  in
  (* The tag/k index maps ARE the record's fields (arch C2 — no folds):
     [info.offsets] is [tag_of], [info.k_ranges] is [k_of]. *)
  let tag_of = info.Convutils.offsets in
  (* lo >= 0 means the access is in the incoming-arg area (entry-relative
     offset); keep it in memory. Local stack slots have lo < 0. For
     outgoing stack args (mem[RSP] stores for 7th+ args), lo <0 but they
     are still ABI-visible (they must remain in memory for the callee's
     hike_stack+offset loads), so we also keep RSP-relative stores with
     k >=0. *)
  let k_of = info.Convutils.k_ranges in
  (* MEM-FISSION: the retaddr-push exemption — the same positional rule
     the region planner uses.  With the push store exempt from ABI
     visibility, its cell converts with its region and the fission gives
     it a never-loaded mem var; the two-tier DCE deletes the store. *)
  let last_push_tids = last_push_tids_of sub in
  (* ONE ABI-visibility rule (Finding 1) — the module-level
     [is_abi_visible], the same one the emitter calls. *)
  let is_abi_visible = is_abi_visible sp ~tag_of ~k_of ~last_push_tids in
  (* The regions come from the VSA result (computed once on the
     PRE-rewrite sub) — never recomputed here (Finding 1: one producer).
     The fallback covers a caller that runs stack-to-locals without the
     vsa pass (a standalone [--pass=hike-stack-to-locals] run). *)
  let regions =
    if info.Convutils.regions <> [] then info.Convutils.regions
    else
      regions_of_sub sp target sub info
        ~frame_escaped:(frame_escapes sp target sub)
  in
  let region_by_tid : Convutils.region Tid.Map.t =
    Base.List.fold_left regions ~init:Tid.Map.empty ~f:(fun m r ->
        Base.List.fold_left r.Convutils.members ~init:m ~f:(fun m (dtid, _) ->
            Core.Map.set m ~key:dtid ~data:r))
  in
  let region_convertible (dtid : tid) : bool =
    match Core.Map.find region_by_tid dtid with
    | Some r -> r.Convutils.convertible
    | None -> false
  in
  let region_max_width (dtid : tid) : int =
    match Core.Map.find region_by_tid dtid with
    | Some r -> r.Convutils.max_width
    | None -> 64
  in
  (* MEM-FISSION (2026-09-02): the conversion table is (addr, shape)
     where shape is [Slot var] (the singleton degenerate — today's
     load-free slot var, kept bit-identical) or [Region (id, base_exp)]
     (the ranged fission — the member reads/writes [region_mem id] at
     [region_base id + <the original index arithmetic, base-substituted>];
     base_exp is the sp/fp-derived BASE sub-expression of the member's
     address — the part the region-base substitution replaces). *)
  (* [base_exp_of addr]: the sp/fp-derived BASE sub-expression of a
     ranged member's address ([RBP + i*4 - 0x70] -> [RBP]; [RSP - k] ->
     [RSP]) — the part the fission substitutes with [Var stack_rN_base].
     Structural: a BinOp's operand that is a bare sp/fp Var (or a Cast
     of one); the whole-address-scan below replaces every occurrence of
     exactly this sub-expression with the region base var. *)
  let base_exp_of (addr : exp) : exp =
    let is_sf (e : exp) : bool =
      match e with
      | Bil.Var v ->
          Abi.is_stack_reg (Abi.of_target target) (Var.base v)
      | Bil.Cast (_, _, Bil.Var v) ->
          Abi.is_stack_reg (Abi.of_target target) (Var.base v)
      | _ -> false
    in
    let rec go (e : exp) : exp option =
      match e with
      | Bil.BinOp (_, a, b) ->
          (match go a with Some x -> Some x | None -> go b)
      | Bil.Cast (_, _, a) -> go a
      | _ -> if is_sf e then Some e else None
    in
    match go addr with Some b -> b | None -> addr
  in
  let cells =
    Term.enum blk_t sub
    |> Seq.fold ~init:[] ~f:(fun acc blk ->
        Term.enum def_t blk
        |> Seq.fold ~init:acc ~f:(fun acc d ->
            if
              not (Term.has_attr d Hike_vsa_relevance.stack_access)
              || is_abi_visible d
            then acc
            else
              match
                ( Core.Map.find tag_of (Term.tid d),
                  addr_of_rhs (Def.rhs d) )
              with
              | Some (Convutils.Range (lo, hi)), Some (addr, s)
                when Int64.equal lo hi && region_convertible (Term.tid d) -> (
                  match Core.Map.find region_by_tid (Term.tid d) with
                  | Some r when Int64.equal (fst r.Convutils.span) (snd r.Convutils.span) ->
                      (addr, `Slot (slot_of lo (region_max_width (Term.tid d)))) :: acc
                  | Some r ->
                      (addr, `Region (r.Convutils.id, base_exp_of addr)) :: acc
                  | None -> (addr, `Slot (slot_of lo (region_max_width (Term.tid d)))) :: acc)
              | Some (Convutils.Range _), Some (addr, _)
                when region_convertible (Term.tid d) -> (
                  match Core.Map.find region_by_tid (Term.tid d) with
                  | Some r ->
                      let rlo, rhi = r.Convutils.span in
                      if Int64.equal rlo rhi then
                        (addr, `Slot (slot_of rlo (region_max_width (Term.tid d)))) :: acc
                      else (addr, `Region (r.Convutils.id, base_exp_of addr)) :: acc
                  | None -> acc)
              | _ -> acc))
  in

  (* [shape_of_addr]: the conversion SHAPE bound to a converted cell's
     address — [`Slot var] (the singleton degenerate) or [`Region (id,
     base)] (the fission). *)
  let shape_of_addr (addr : exp) :
      [> `Slot of var | `Region of int * exp ] option =
    Base.List.find_map cells ~f:(fun (a, shape) ->
        if Exp.equal a addr then Some shape else None)
  in
  (* [fission_addr id base addr]: the ranged member's address with its
     sp/fp-derived BASE sub-expression substituted by the region base
     var — [mem[RBP + i*4 - 0x70]] becomes [stack_rN_base + i*4 - 0x70]
     (the SAME index arithmetic; the base names the region's alloca).
     Both operands of the access now name the region — the store/load
     cell-split class closes by construction. *)
  let fission_addr (id : int) (base : exp) (addr : exp) : exp =
    let sub =
      object
        inherit Exp.mapper
        method! map_exp e = if Exp.equal e base then Bil.Var (region_base id) else e
      end
    in
    sub#map_exp addr
  in
  (* THE MAP SOLUTION: one [Exp.mapper] over the def rhs mapping ONLY the
     memory nodes, in the conversion's three-way shape:
     - [`Slot] (the singleton degenerate): a scalar (Imm-typed) local
       read of width smaller than the slot is wrapped in
       [Cast (LOW, bits, Var local)] so the load width survives; stores
       narrower than the scalar slot splice via the read-modify-write
       shim (keep the untouched high bytes);
     - [`Region (id, base)] (mem-fission): BOTH operands are rewritten —
       the mem var becomes [region_mem id], the address's sp/fp-derived
       base becomes [region_base id];
     - everything else: untouched.
     ALL enclosing structure (casts, binops, ites, lets) is preserved:
     the emitter's [create_cast] / [coerce_to_same_type] produce the
     widening at exactly the BIL type boundaries — no emitter-side
     promotion, no whole-rhs replacement. *)
  let map_exp_cells (e : exp) : exp =
    let v =
      object
        inherit Exp.mapper
        method! map_load ~mem ~addr e s =
          (* MEM-FISSION: the three-way shape.  [`Slot] keeps today's
             singleton rewrite verbatim (the load-free slot var).  [`Region]
             fissions BOTH operands: the mem var becomes [region_mem id]
             and the address's base sub-expression becomes
             [region_base id] — a load from the region's own memory at
             the region-relative address. *)
          match shape_of_addr addr with
          | Some (`Slot local) -> (
              (* slot_of is Imm-only — the catch-all is unreachable. *)
              match Var.typ local with
              | Type.Imm w ->
                  let bits = Size.in_bits s in
                  if bits < w then Bil.Cast (Bil.LOW, bits, Bil.Var local)
                  else Bil.Var local
              | Type.Unk | Type.Mem _ -> Bil.Var local)
          | Some (`Region (id, base)) ->
              Bil.Load
                ( Bil.Var (region_mem id),
                  fission_addr id base addr,
                  e, s )
          | None -> Bil.Load (mem, addr, e, s)
        method! map_store ~mem ~addr ~exp:data e s =
          (* MEM-FISSION: the same three-way split.  [`Slot] keeps the
             singleton shim verbatim.  [`Region] fissions BOTH operands:
             the store writes [region_mem id] at the region-relative
             address — and the DEF-LHS REBIND below turns the whole def
             into [stack_rN_mem := stack_rN_mem with [...]] so the store
             chain is rooted ONLY by loads from the same var (the
             two-tier DCE's load-roots rule). *)
          match shape_of_addr addr with
          | Some (`Slot local) -> (
              match Var.typ local with
              | Type.Imm w ->
                  let bits = Size.in_bits s in
                  if bits < w then
                    (* the read-modify-write shim: keep the untouched high
                       bytes of the slot, splice the stored width in. *)
                    let mask =
                      let low =
                        Word.sub
                          (Word.lshift (Word.one w) (Word.of_int ~width:w bits))
                          (Word.one w)
                      in
                      Word.lnot low
                    in
                    Bil.Store (mem, addr,
                      Bil.BinOp (Bil.OR,
                        Bil.BinOp (Bil.AND, Bil.Var local, Bil.Int mask),
                        Bil.Cast (Bil.UNSIGNED, w, data)), e, s)
                  else Bil.Store (mem, addr, data, e, s)
              | Type.Unk | Type.Mem _ -> Bil.Store (mem, addr, data, e, s))
          | Some (`Region (id, base)) ->
              Bil.Store
                ( Bil.Var (region_mem id),
                  fission_addr id base addr,
                  data, e, s )
          | None -> Bil.Store (mem, addr, data, e, s)
      end
    in
    v#map_exp e
  in
  (* [map_rhs d]: every def's rhs gets the cell mapping — the enclosing
     structure is preserved (the mapper touches only the matching
     load/store nodes). *)
  let map_rhs (d : def term) : exp = map_exp_cells (Def.rhs d) in
  (* [v_map e]: the same mapping for a bare expression (the stored DATA
     of the rebind below may itself read converted cells). *)
  let v_map (e : exp) : exp = map_exp_cells e in
  (* The def rewrite: a def whose ENTIRE rhs is a converted memory
     access AND whose lhs is the frame-carrying mem var rebinds the lhs
     to the cell's local and REPLACES the store with its VALUE — the
     scalar slot becomes the storage itself ([slot := data], or the
     read-modify-write splice when the stored width is narrower than the
     slot), NEVER a Store node (a Store expression evaluated as a value
     is the void store instruction — the badref chain). A Mem-typed
     (array) local keeps the mapped Store form ([arr := arr with
     [addr] <- data]). Every other def keeps its own lhs and gets the
     mapped rhs — the nested loads inside it are rewritten, the
     enclosing expression untouched. *)
  let rewrite_def (d : def term) : def term =
    let whole_access =
      match (addr_of_rhs (Def.rhs d), Convutils.is_mem (Def.lhs d)) with
      | Some (addr, s), true -> (
          match shape_of_addr addr with
          | Some (`Slot local) -> Some (s, `Slot local)
          | Some (`Region (id, _)) -> Some (s, `Region id)
          | None -> None)
      | _ -> None
    in
    match whole_access with
    | Some (s, `Region id) ->
        (* MEM-FISSION: the whole-rhs ranged store rebinds its lhs to the
           region mem var — [stack_rN_mem := stack_rN_mem with
           [region_addr] <- data] (the mapper already rewrote the
           operands; [map_rhs] re-runs it on the way through).  The
           store chain's ONLY roots are loads from the same var — the
           two-tier DCE's load-roots rule. *)
        Def.with_rhs (Def.with_lhs d (region_mem id)) (map_rhs d)
    | Some (s, `Slot local) -> (
        match Var.typ local with
        | Type.Imm w -> (
            match store_data_of_rhs (Def.rhs d) with
            | Some (data, wrap) ->
                let bits = Size.in_bits s in
                (* the stored DATA is mapped as well — the increment's
                   inner load ([mem := mem with [RBP-4] <- mem[RBP-4]+1])
                   reads the SAME cell and must read the local, not the
                   frame (the store is gone: a frame read would freeze
                   the counter at its init value — the infinite loop). *)
                let data = v_map data in
                let value =
                  if bits >= w then data
                  else
                    (* the read-modify-write shim: keep the untouched
                       high bytes of the slot, splice the stored width
                       in. *)
                    let mask =
                      let low =
                        Word.sub
                          (Word.lshift (Word.one w) (Word.of_int ~width:w bits))
                          (Word.one w)
                      in
                      Word.lnot low
                    in
                    Bil.BinOp
                      (Bil.OR,
                       Bil.BinOp (Bil.AND, Bil.Var local, Bil.Int mask),
                       Bil.Cast (Bil.UNSIGNED, w, data))
                in
                Def.with_rhs (Def.with_lhs d local) (wrap value)
            | None ->
                (* a load as a mem-lhs def's rhs does not occur; the
                   mapped rhs is the sound answer. *)
                Def.with_rhs d (map_rhs d))
        | Type.Unk | Type.Mem _ -> Def.with_rhs d (map_rhs d))
    | None -> Def.with_rhs d (map_rhs d)
  in
  let sub' = Term.map blk_t sub ~f:(fun blk ->
      Term.map def_t blk ~f:rewrite_def) in
  (* Zero-initialize every converted SLOT at the entry block (the
     singleton degenerate — an Imm-typed local needs an init def for its
     first read).  Region mems are NOT initialized: their cells' content
     rides the region alloca (the fission's memory semantics — the
     alloca holds the lifted frame's original bytes). *)
  let slots : var list =
    Base.List.fold_left cells ~init:[] ~f:(fun acc (_, shape) ->
        match shape with
        | `Slot local when not (Base.List.exists acc ~f:(Var.equal local)) ->
            local :: acc
        | _ -> acc)
  in
  match Term.first blk_t sub' with
  | None -> sub'
  | Some blk ->
    let w_of (slot : var) : int =
      match Var.typ slot with
      | Type.Imm w -> w
      | _ -> 64
    in
    let blk' =
      Base.List.fold_left slots ~init:blk ~f:(fun blk slot ->
          Term.prepend def_t blk
            (Def.create slot (Bil.Int (Word.zero (w_of slot)))))
    in
    Term.update blk_t sub' blk'
