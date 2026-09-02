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
  let last_push_tids = Model.last_push_tids_of sub in
  (* ONE ABI-visibility rule (Finding 1) — the module-level
     [Model.is_abi_visible] (the split moved it; the emitter calls the
     same one), with the fission's push-exemption parameter. *)
  let is_abi_visible = Model.is_abi_visible sp ~tag_of ~k_of ~last_push_tids in
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
  (* MEM-FISSION (2026-09-02): the conversion table is (addr, shape)
     where shape is [Slot var] (the singleton degenerate — today's
     load-free slot var, kept bit-identical) or [Region (id, base_exp)]
     (the ranged fission — the member reads/writes [Model.region_mem id] at
     [Model.region_base id + <the original index arithmetic, base-substituted>];
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
                  Model.addr_of_rhs (Def.rhs d) )
              with
              | Some (Convutils.Range (lo, hi)), Some (addr, s)
                when Int64.equal lo hi && region_convertible (Term.tid d) -> (
                  match Core.Map.find region_by_tid (Term.tid d) with
                  | Some r when Int64.equal (fst r.Convutils.span) (snd r.Convutils.span) ->
                      (addr, `Slot (Model.slot_of lo (region_max_width (Term.tid d)))) :: acc
                  | Some r ->
                      (addr, `Region (r.Convutils.id, base_exp_of addr)) :: acc
                  | None -> (addr, `Slot (Model.slot_of lo (region_max_width (Term.tid d)))) :: acc)
              | Some (Convutils.Range _), Some (addr, _)
                when region_convertible (Term.tid d) -> (
                  match Core.Map.find region_by_tid (Term.tid d) with
                  | Some r ->
                      let rlo, rhi = r.Convutils.span in
                      if Int64.equal rlo rhi then
                        (addr, `Slot (Model.slot_of rlo (region_max_width (Term.tid d)))) :: acc
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
        method! map_exp e = if Exp.equal e base then Bil.Var (Model.region_base id) else e
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
       the mem var becomes [Model.region_mem id], the address's sp/fp-derived
       base becomes [Model.region_base id];
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
             fissions BOTH operands: the mem var becomes [Model.region_mem id]
             and the address's base sub-expression becomes
             [Model.region_base id] — a load from the region's own memory at
             the region-relative address. *)
          match shape_of_addr addr with
          | Some (`Slot local) -> (
              (* Model.slot_of is Imm-only — the catch-all is unreachable. *)
              match Var.typ local with
              | Type.Imm w ->
                  let bits = Size.in_bits s in
                  if bits < w then Bil.Cast (Bil.LOW, bits, Bil.Var local)
                  else Bil.Var local
              | Type.Unk | Type.Mem _ -> Bil.Var local)
          | Some (`Region (id, base)) ->
              Bil.Load
                ( Bil.Var (Model.region_mem id),
                  fission_addr id base addr,
                  e, s )
          | None -> Bil.Load (mem, addr, e, s)
        method! map_store ~mem ~addr ~exp:data e s =
          (* MEM-FISSION: the same three-way split.  [`Slot] keeps the
             singleton shim verbatim.  [`Region] fissions BOTH operands:
             the store writes [Model.region_mem id] at the region-relative
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
                ( Bil.Var (Model.region_mem id),
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
      match (Model.addr_of_rhs (Def.rhs d), Convutils.is_mem (Def.lhs d)) with
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
        Def.with_rhs (Def.with_lhs d (Model.region_mem id)) (map_rhs d)
    | Some (s, `Slot local) -> (
        match Var.typ local with
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
