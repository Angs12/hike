(* Stack-to-locals — THE REWRITE PASS (architecture review #1 part 2):
   the [Exp.mapper] conversion of stack accesses to local variables.
   The DECISION functions ([regions_of_sub]/[split_plan]/
   [frame_escapes]/[abi_visibility_of] and their rules) moved to
   [hike_stack_model] — the pure model this pass consumes; see that
   module's header.  The stack model decision still has ONE producer
   ([Hike_stack_model.split_plan] — Finding 1); this pass and the
   emitter and [Hike_dce] read it. *)

open Bap.Std
open Bap.Std.Bil.Types
open Bap_core_theory
module Abi = Hike_abi
module Model = Hike_stack_model

let stack_to_locals (target : Theory.Target.t) (sp : var) (sub : sub term) :
    sub term =
  let info =
    Core.Map.find (Hike_kb.vsa_info ()) (Term.tid sub)
    |> Base.Option.value
         ~default:
           Convutils.empty_vsa_info
  in
  (* the record's own maps (see [Model.regions_of_sub]). *)
  let tag_of = info.Convutils.offsets in
  (* lo >= 0 means the access is in the incoming-arg area (entry-relative
     offset); keep it in memory. Local stack slots have lo < 0. For
     outgoing stack args (mem[RSP] stores for 7th+ args), lo <0 but they
     are still ABI-visible (they must remain in memory for the callee's
     hike_stack+offset loads), so we also keep RSP-relative stores with
     k >=0. *)
  let k_of = info.Convutils.k_ranges in
  (* ONE ABI-visibility rule (Finding 1) — the module-level
     [Model.is_abi_visible], the same one the emitter calls. *)
  let is_abi_visible = Model.is_abi_visible sp ~tag_of ~k_of in
  (* The regions come from the VSA result (computed once on the
     PRE-rewrite sub) — never recomputed here (Finding 1: one producer).
     The fallback covers a caller that runs stack-to-locals without the
     vsa pass (a standalone [--pass=hike-stack-to-locals] run). *)
  let regions =
    if info.Convutils.regions <> [] then info.Convutils.regions
    else
      Model.regions_of_sub sp target sub info
        ~frame_escaped:(Model.frame_escapes sp target sub)
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
                  Model.addr_of_rhs (Def.rhs d) )
              with
              | Some (Convutils.Range (lo, hi)), Some (addr, s)
                when Int64.equal lo hi && region_convertible (Term.tid d) -> (
                  match Core.Map.find region_by_tid (Term.tid d) with
                  | Some r when Int64.equal (fst r.Convutils.span) (snd r.Convutils.span) ->
                      (addr, Model.slot_of lo (region_max_width (Term.tid d))) :: acc
                  | Some r ->
                      let rlo, rhi = r.Convutils.span in
                      (addr, Model.arr_of rlo rhi) :: acc
                  | None -> (addr, Model.slot_of lo (region_max_width (Term.tid d))) :: acc)
              | Some (Convutils.Range _), Some (addr, _)
                when region_convertible (Term.tid d) -> (
                  match Core.Map.find region_by_tid (Term.tid d) with
                  | Some r ->
                      let rlo, rhi = r.Convutils.span in
                      if Int64.equal rlo rhi then
                        (addr, Model.slot_of rlo (region_max_width (Term.tid d))) :: acc
                      else (addr, Model.arr_of rlo rhi) :: acc
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
      match (Model.addr_of_rhs (Def.rhs d), Convutils.is_mem (Def.lhs d)) with
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
            match Model.store_data_of_rhs (Def.rhs d) with
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
