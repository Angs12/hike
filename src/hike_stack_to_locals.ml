(* Rewrites stack accesses to locals per the stack plan. *)

open Bap.Std
open Bap.Std.Bil.Types
open Bap_core_theory
module Abi = Hike_abi
module Model = Hike_stack_model

let stack_to_locals (target : Theory.Target.t) (sp : var) (sub : sub term) :
    sub term =
  let info = Hike_kb.info_of_sub (Term.tid sub) in

  let tag_of = info.Model.offsets in
  (* Incoming and outgoing arg accesses stay in memory: the cross-sub
     consistency rule, read from the two record facts. *)
  let is_abi_visible = Model.is_abi_visible ~tag_of in
  (* The record IS the regions (autonomy: consume the producer's output,
     never recompute). *)
  let regions = info.Model.regions in
  let region_by_tid : Model.region Tid.Map.t =
    Base.List.fold_left regions ~init:Tid.Map.empty ~f:(fun m r ->
        Base.List.fold_left r.Model.members ~init:m ~f:(fun m (dtid, _) ->
            Core.Map.set m ~key:dtid ~data:r))
  in
  let region_max_width (dtid : tid) : int =
    match Core.Map.find region_by_tid dtid with
    | Some r -> r.Model.max_width
    | None -> 64
  in
  (* Conversion table: address -> slot or region shape. *)
  (* Returns the address base the region base replaces.  Callers reach it
     only for TAGGED, convertible region members (the tag IS the
     frame-residency proof, and any provable base counts — the -O0
     [RBP - k] shape, a hand-asm R12 frame pointer, anything the VSA
     proved); the old sp/fp-by-name test was dead conservatism. *)
  let base_exp_of (addr : exp) : exp =
    let vis =
      object
        inherit [ exp option ] Exp.visitor
        method! visit_var v acc =
          Base.Option.first_some acc (Some (Bil.Var v))
      end
    in
    Base.Option.value (vis#visit_exp addr None) ~default:addr
  in
  let cells =
    Term.enum blk_t sub
    |> Seq.fold ~init:[] ~f:(fun acc blk ->
        Term.enum def_t blk
        |> Seq.fold ~init:acc ~f:(fun acc d ->
            (* Conversion candidates carry a [vsa_info] tag (spec §2.2). *)
            if is_abi_visible d then acc
            else
              match
                ( Core.Map.find tag_of (Term.tid d),
                  Model.addr_of_rhs (Def.rhs d) )
              with
              | Some (Model.Range _), Some (addr, _) -> (
                  match Core.Map.find region_by_tid (Term.tid d) with
                  | Some r when r.Model.convertible ->
                      let rlo, rhi = r.Model.span in
                      if Int64.equal rlo rhi then begin
                          let w = region_max_width (Term.tid d) in
                          (addr, `Slot (Model.slot_of rlo w, w)) :: acc
                        end
                      else (addr, `Region (r.Model.id, base_exp_of addr)) :: acc
                  | _ -> acc)
              | _ -> acc))
  in

  (* Looks up a cell's conversion shape (the slot's width travels with it —
     [slot_of] mints [Imm] by construction). *)
  let shape_of_addr (addr : exp) :
      [> `Slot of var * int | `Region of int * exp ] option =
    Base.List.find_map cells ~f:(fun (a, shape) ->
        if Exp.equal a addr then Some shape else None)
  in
  (* Substitutes the address base with the region base. *)
  let fission_addr (id : int) (base : exp) (addr : exp) : exp =
    let sub =
      object
        inherit Exp.mapper
        method! map_exp e = if Exp.equal e base then Bil.Var (Model.region_base id) else e
      end
    in
    sub#map_exp addr
  in
  (* Maps only matching memory nodes, preserving enclosing structure. *)
  let map_exp_cells (e : exp) : exp =
    let v =
      object (self)
        inherit Exp.mapper
        method! map_load ~mem ~addr e s =
          (* Fissions both load operands for regions. *)
          match shape_of_addr addr with
          | Some (`Slot (local, w)) ->
              let bits = Size.in_bits s in
              if bits < w then Bil.Cast (Bil.LOW, bits, Bil.Var local)
              else Bil.Var local
          | Some (`Region (id, base)) ->
              Bil.Load
                ( Bil.Var (Model.region_mem id),
                  fission_addr id base addr,
                  e, s )
          | None -> Bil.Load (self#map_exp mem, self#map_exp addr, e, s)
        method! map_store ~mem ~addr ~exp:data e s =
          let data = self#map_exp data in
          (* Fissions both store operands for regions. *)
          match shape_of_addr addr with
          | Some (`Slot (local, w)) ->
              let bits = Size.in_bits s in
              if bits < w then
                (* Splices the stored width into the slot. *)
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
          | Some (`Region (id, base)) ->
              Bil.Store
                ( Bil.Var (Model.region_mem id),
                  fission_addr id base addr,
                  data, e, s )
          | None -> Bil.Store (self#map_exp mem, self#map_exp addr, data, e, s)
      end
    in
    v#map_exp e
  in
  (* Maps a def rhs. *)
  let map_rhs (d : def term) : exp = map_exp_cells (Def.rhs d) in
  (* Rebinds whole-access defs to their cell; maps nested loads elsewhere. *)
  let rewrite_def (d : def term) : def term =
    let whole_access =
      match (Model.addr_of_rhs (Def.rhs d), Model.is_mem (Def.lhs d)) with
      | Some (addr, s), true -> (
          match shape_of_addr addr with
          | Some (`Slot local) -> Some (s, `Slot local)
          | Some (`Region (id, _)) -> Some (s, `Region id)
          | None -> None)
      | _ -> None
    in
    match whole_access with
    | Some (s, `Region id) ->
        (* Rebinds ranged stores to their region mem. *)
        Def.with_rhs (Def.with_lhs d (Model.region_mem id)) (map_rhs d)
    | Some (s, `Slot (local, w)) -> (
        match Model.store_data_of_rhs (Def.rhs d) with
        | Some (data, wrap) ->
            let bits = Size.in_bits s in
            (* Stored data reads converted cells too. *)
            let data = map_exp_cells data in
            let value =
              if bits >= w then data
              else
                (* Splices the stored width into the slot. *)
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
        | None -> Def.with_rhs d (map_rhs d))
    | None -> Def.with_rhs d (map_rhs d)
  in
  let sub' = Term.map blk_t sub ~f:(fun blk ->
      Term.map def_t blk ~f:rewrite_def) in
  (* Zero-initializes converted slots at entry (the width travels with the
     cell). *)
  let slots : (var * int) list =
    Base.List.fold_left cells ~init:[] ~f:(fun acc (_, shape) ->
        match shape with
        | `Slot (local, w) when not (Base.List.exists acc ~f:(fun (l, _) -> Var.equal l local)) ->
            (local, w) :: acc
        | _ -> acc)
  in
  match Term.first blk_t sub' with
  | None -> sub'
  | Some blk ->
    let blk' =
      Base.List.fold_left slots ~init:blk ~f:(fun blk (slot, w) ->
          Term.prepend def_t blk
            (Def.create slot (Bil.Int (Word.zero w))))
    in
    Term.update blk_t sub' blk'
