(* Stack-to-locals: converts stack accesses to local variables. Uses VSA tags to identify stack slots; groups overlapping ranges into regions. Singleton ranges become scalar slots, intervals become local arrays. Second pass rewrites nested loads that read converted cells. *)

open Bap.Std

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
let saves_incoming_reg (d : def term) : bool =
  match Def.rhs d with
  | Bil.Store (_, _, data, _, _) -> (
      match data with
      | Bil.Var v ->
          Base.List.exists Calling_conventions.x86_64_sysv.param_regs
            ~f:(fun r -> Var.same r (Var.base v))
      | _ -> false)
  | _ -> false

(* Compute stack regions: S1 coarser (ADR 0004) — maximal overlap components with
   rlo=min lo, rhi=max hi. Convertible if every member has lo<0 and is not an
   incoming-register save; overlapping Ranges merge (not identical). Infinite
   tags excluded from normal regions — S2 caps them to one big stack_rN in the
   emitter; VLA excluded. *)
let regions_of_sub (sp : var) (sub : sub term) (info : Convutils.vsa_info) :
    Convutils.region list =
  let k_of =
    Base.List.fold info.Convutils.k_ranges ~init:Tid.Map.empty
      ~f:(fun m (dtid, klo, khi) ->
        Core.Map.set m ~key:dtid ~data:(klo, khi))
  in
  let ranges : (int64 * int64) Tid.Map.t =
    Base.List.fold_left info.Convutils.offsets ~init:Tid.Map.empty
      ~f:(fun m (dtid, kind) ->
        match kind with
        | Convutils.Range (lo, hi) ->
            Core.Map.set m ~key:dtid ~data:(lo, hi)
        | Convutils.Infinite _ | Convutils.Unbounded | Convutils.Dead | Convutils.VLA _ -> m)
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
  let is_real_call (j : jmp term) : bool =
    match Jmp.kind j with
    | Call c -> (
        match Call.target c with
        | Direct _ -> true
        | Indirect _ -> Option.is_some (Call.return c))
    | _ -> false
  in
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
              |> Core.Set.exists ~f:(fun v ->
                     String.equal (Var.name v) "RSP")
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
  let has_outgoing_stack_args : bool =
    Term.enum blk_t sub
    |> Seq.exists ~f:(fun blk ->
        if
          Term.enum jmp_t blk
          |> Seq.exists ~f:is_real_call
        then
          Term.enum def_t blk
          |> Seq.exists ~f:(fun d ->
              Core.Set.mem outgoing_tail_tids (Term.tid d)
              && is_outgoing_store d)
        else false)
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
  let rec is_direct_const_addr (addr : exp) : bool =
    let base_var v = Var.base v in
    let spv = Var.create ~is_virtual:false ~fresh:false "RSP" (Type.Imm 64) in
    let fpv = Var.create ~is_virtual:false ~fresh:false "RBP" (Type.Imm 64) in
    match addr with
    | Bil.Int _ -> true
    | Bil.Var v -> Var.same (base_var v) spv || Var.same (base_var v) fpv
    | Bil.BinOp ((Bil.PLUS | Bil.MINUS), Bil.Var v, Bil.Int _)
    | Bil.BinOp ((Bil.PLUS | Bil.MINUS), Bil.Int _, Bil.Var v) ->
        Var.same (base_var v) spv || Var.same (base_var v) fpv
    | Bil.Cast (_, _, e) -> is_direct_const_addr e
    | _ -> false
  in
  let sp_escaped (sp : var) : bool =
    let base_var v = Var.base v in
    let fpv = Var.create ~is_virtual:false ~fresh:false "RBP" (Type.Imm 64) in    let sp_base = base_var sp in
    (* [derived]: the vars whose values are sp/fp-derived — RSP, RBP and
       every temp defined from them through ARITHMETIC (BinOp/Cast/
       Extract/Concat); a LOAD's result is NOT derived (a value read
       from memory is not an address expression on the frame), and a
       memory side-effect's lhs ([mem]) is not derived. Computed as a
       block-local fixpoint via the def chain (the -O0 shape computes
       the address in one def; the closure covers multi-def chains). *)
    let derived : Var.Set.t ref =
      ref (Core.Set.union (Var.Set.singleton sp_base) (Var.Set.singleton fpv))
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
        Base.List.exists Calling_conventions.x86_64_sysv.param_regs
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
                    | Some md -> not (saves_incoming_reg md)
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
                             let ok = is_direct_const_addr addr in
                             if not ok && Sys.getenv_opt "HIKE_VSA_DEBUG" <> None then
                               Printf.eprintf "hike:   member %s NOT direct: addr=%s\n"
                                 (Tid.name mtid)
                                 (Format.asprintf "%a" Exp.pp addr);
                             ok
                         | None -> true)
                    | None -> true)) in
            if not res && Sys.getenv_opt "HIKE_VSA_DEBUG" <> None then (
              let lo0, hi0 = span in
              Printf.eprintf "hike: region %d span=(%Ld,%Ld) NOT convertible: members=%d outgoing=%b escaped=%b\n" i lo0 hi0 (List.length members) has_outgoing_stack_args (sp_escaped sp);
              Printf.eprintf "hike:   (sub %s)\n" (Sub.name sub);
              Base.List.iter members ~f:(fun (mtid, (lo, hi)) ->
                  let k_str = match Core.Map.find k_of mtid with Some (klo, khi) -> Printf.sprintf "(%Ld,%Ld)" klo khi | None -> "None" in
                  let saves = match Core.Map.find def_of_tid mtid with Some md -> saves_incoming_reg md | None -> false in
                  Printf.eprintf "hike:   member %s (%Ld,%Ld) k=%s saves=%b\n" (Tid.name mtid) lo hi k_str saves);
            );
            res && not has_outgoing_stack_args && not (sp_escaped sp)
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

(* The stored data of a (possibly cast-wrapped) store rhs, with the
   wrapper that rebuilds the enclosing cast around the rewritten store. *)
let stack_to_locals (sp : var) (sub : sub term) : sub term =
  let info =
    Core.Map.find (Hike_kb.vsa_info ()) (Term.tid sub)
    |> Base.Option.value
         ~default:
           { Convutils.offsets = []; k_ranges = []; regions = []; degraded = false;
             call_stack_args = []; vla_bounds = [] }
  in
  let tag_of =
    Base.List.fold info.Convutils.offsets ~init:Tid.Map.empty
      ~f:(fun m (dtid, kind) -> Core.Map.set m ~key:dtid ~data:kind)
  in
  (* lo >= 0 means the access is in the incoming-arg area (entry-relative
     offset); keep it in memory. Local stack slots have lo < 0. For
     outgoing stack args (mem[RSP] stores for 7th+ args), lo <0 but they
     are still ABI-visible (they must remain in memory for the callee's
     hike_stack+offset loads), so we also keep RSP-relative stores with
     k >=0. *)
  let k_of =
    Base.List.fold info.Convutils.k_ranges ~init:Tid.Map.empty
      ~f:(fun m (dtid, klo, khi) -> Core.Map.set m ~key:dtid ~data:(klo, khi))
  in
  let is_abi_visible (d : def term) : bool =
    match Core.Map.find tag_of (Term.tid d) with
    | Some (Convutils.Range (lo, _)) when Int64.compare lo 0L >= 0 -> true
    | Some (Convutils.Range (lo, _)) ->
      (match Core.Map.find k_of (Term.tid d) with
       | Some (klo, _) when Int64.compare klo 0L >= 0 ->
         (match addr_of_rhs (Def.rhs d) with
          | Some (addr, _) ->
            Exp.free_vars addr |> Core.Set.exists ~f:(fun v -> String.equal (Var.name v) "RSP")
          | None -> false)
       | _ -> false)
    | _ -> false
  in
  let regions =
    if info.Convutils.regions <> [] then info.Convutils.regions
    else regions_of_sub sp sub info in
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
  (* Map from address expression to the local that replaces it.
     S1 coarser: overlapping Ranges share one region with span rlo/rhi;
     all members of a convertible region share the same LLVM alloca
     (slot or array sized to the region's hull), so the BIL local is
     derived from the region's span, not the tag's own interval. *)
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
                      (addr, slot_of lo (region_max_width (Term.tid d))) :: acc
                  | Some r ->
                      let rlo, rhi = r.Convutils.span in
                      (addr, arr_of rlo rhi) :: acc
                  | None -> (addr, slot_of lo (region_max_width (Term.tid d))) :: acc)
              | Some (Convutils.Range _), Some (addr, _)
                when region_convertible (Term.tid d) -> (
                  match Core.Map.find region_by_tid (Term.tid d) with
                  | Some r ->
                      let rlo, rhi = r.Convutils.span in
                      if Int64.equal rlo rhi then
                        (addr, slot_of rlo (region_max_width (Term.tid d))) :: acc
                      else (addr, arr_of rlo rhi) :: acc
                  | None -> acc)
              | _ -> acc))
  in
  (* [local_of_addr]: the local bound to a converted cell's address. *)
  let local_of_addr (addr : exp) : var option =
    Base.List.find_map cells ~f:(fun (a, local) ->
        if Exp.equal a addr then Some local else None)
  in
  (* THE MAP SOLUTION: one [Exp.mapper] over the def rhs mapping ONLY the
     memory nodes — every load/store whose address matches a converted
     cell becomes a read/write of the cell's local, and ALL enclosing
     structure (casts, binops, ites, lets) is preserved: the emitter's
     [create_cast] / [coerce_to_same_type] then produce the widening at
     exactly the BIL type boundaries — no emitter-side promotion, no
     whole-rhs replacement. A scalar (Imm-typed) local read of width
     smaller than the slot is wrapped in [Cast (LOW, bits, Var local)] so
     the load width survives; a Mem-typed (array) local keeps the
     Load/Store form with the local as the memory base. Stores narrower
     than the scalar slot splice via the read-modify-write shim (keep the
     untouched high bytes). *)
  let map_exp_cells (e : exp) : exp =
    let v =
      object
        inherit Exp.mapper
        method! map_load ~mem ~addr e s =
          match local_of_addr addr with
          | Some local -> (
              match Var.typ local with
              | Type.Mem _ -> Bil.Load (Bil.Var local, addr, e, s)
              | Type.Imm w ->
                  let bits = Size.in_bits s in
                  if bits < w then Bil.Cast (Bil.LOW, bits, Bil.Var local)
                  else Bil.Var local
              | Type.Unk -> Bil.Var local)
          | None -> Bil.Load (mem, addr, e, s)
        method! map_store ~mem ~addr ~exp:data e s =
          match local_of_addr addr with
          | Some local -> (
              match Var.typ local with
              | Type.Mem _ -> Bil.Store (Bil.Var local, addr, data, e, s)
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
              | Type.Unk -> Bil.Store (mem, addr, data, e, s))
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
      | Some (addr, s), true ->
          Base.Option.map (local_of_addr addr) ~f:(fun local -> (s, local))
      | _ -> None
    in
    match whole_access with
    | Some (s, local) -> (
        match Var.typ local with
        | Type.Mem _ ->
            Def.with_rhs (Def.with_lhs d local) (map_rhs d)
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
        | Type.Unk -> Def.with_rhs d (map_rhs d))
    | None -> Def.with_rhs d (map_rhs d)
  in
  let sub' = Term.map blk_t sub ~f:(fun blk ->
      Term.map def_t blk ~f:rewrite_def) in
  (* Zero-initialize every converted slot at the entry block. *)
  let slots : var list =
    Base.List.fold_left cells ~init:[] ~f:(fun acc (_, local) ->
        match Var.typ local with
        | Type.Imm _ when not (Base.List.exists acc ~f:(Var.equal local)) ->
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
