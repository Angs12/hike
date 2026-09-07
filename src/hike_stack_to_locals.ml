(* Rewrites stack accesses to locals per the stack plan. *)

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
  
  let tag_of = info.Convutils.offsets in
  (* Incoming and outgoing arg accesses stay in memory. *)
  let k_of = info.Convutils.k_ranges in
  (* The retaddr push stays convertible. Stack-ness is [vsa_info]
     membership (spec §2.2). *)
  let last_push_tids =
    Model.last_push_tids_of sub ~is_stack:(fun d ->
        Core.Map.mem tag_of (Term.tid d))
  in
  let is_abi_visible = Model.is_abi_visible sp ~tag_of ~k_of ~last_push_tids in
  (* ABI record, resolved once: the per-node check below runs on every
     address expression of every converted def. *)
  let abi = Abi.of_target target in
  (* Regions come from the VSA result. *)
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
  (* Conversion table: address -> slot or region shape. *)
  (* Returns the address base the region base replaces. *)
  let base_exp_of (addr : exp) : exp =
    let is_stack_reg v = Abi.is_stack_reg abi (Var.base v) in
    let is_sf (e : exp) : bool =
      match e with
      | Bil.Var v -> is_stack_reg v
      | Bil.Cast (_, _, Bil.Var v) -> is_stack_reg v
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
            (* Conversion candidates carry a [vsa_info] tag (spec §2.2). *)
            if is_abi_visible d then acc
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

  (* Looks up a cell's conversion shape. *)
  let shape_of_addr (addr : exp) :
      [> `Slot of var | `Region of int * exp ] option =
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
      object
        inherit Exp.mapper
        method! map_load ~mem ~addr e s =
          (* Fissions both load operands for regions. *)
          match shape_of_addr addr with
          | Some (`Slot local) -> (
              
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
          (* Fissions both store operands for regions. *)
          match shape_of_addr addr with
          | Some (`Slot local) -> (
              match Var.typ local with
              | Type.Imm w ->
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
  (* Maps a def rhs. *)
  let map_rhs (d : def term) : exp = map_exp_cells (Def.rhs d) in
  (* Rebinds whole-access defs to their cell; maps nested loads elsewhere. *)
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
        (* Rebinds ranged stores to their region mem. *)
        Def.with_rhs (Def.with_lhs d (Model.region_mem id)) (map_rhs d)
    | Some (s, `Slot local) -> (
        match Var.typ local with
        | Type.Imm w -> (
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
            | None ->
                
                Def.with_rhs d (map_rhs d))
        | Type.Unk | Type.Mem _ -> Def.with_rhs d (map_rhs d))
    | None -> Def.with_rhs d (map_rhs d)
  in
  let sub' = Term.map blk_t sub ~f:(fun blk ->
      Term.map def_t blk ~f:rewrite_def) in
  (* Zero-initializes converted slots at entry. *)
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
