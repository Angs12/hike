(* The synth-value lane: one home for every synthetic variable's LLVM
   value.  [build] enumerates the vocabulary once and binds each
   module-lifetime var — a module address through the address map, a
   component var to its global and native origin; [value] resolves a
   var at the use site, reading those per-run bindings, the
   per-sub/block SSA bindings, or the environment cell.  The
   classification is Hike_synth's; the LLVM object a kind denotes is
   the emitter's. *)

open Bap.Std
open Bil2llvm_env

module Section = Bil2llvm_section

(* The per-run bindings: the values and the component origins. *)
type bindings = {
  values : Llvm.llvalue Var.Map.t;
  origins : int64 Var.Map.t;
}

let add key data m = Core.Map.set m ~key ~data

(* The component globals and their native origins, from the one owner
   tiling: a component's base var and memory var share its global. *)
let build_components ~addr_bits (sections : section list) : bindings =
  Base.List.fold sections ~init:{ values = Var.Map.empty; origins = Var.Map.empty }
    ~f:(fun acc section ->
      Base.List.fold section.owners ~init:acc ~f:(fun acc o ->
          match o.own_id with
          | None -> acc
          | Some id ->
            let mem = Hike_stack_model.sec_comp_mem ~addr_bits id in
            let ptr = Hike_stack_model.sec_comp_ptr ~addr_bits id in
            { values = acc.values |> add mem o.base |> add ptr o.base;
              origins = acc.origins |> add mem o.own_lo |> add ptr o.own_lo }))

(* The module-address vars: one value per distinct address. *)
let build_addrs ctx (acc : bindings) : bindings =
  let ty = Llvm.integer_type ctx.llvm_ctx ctx.addr_bits in
  Base.List.fold (Hike_synth.bindings ctx.synth) ~init:acc
    ~f:(fun acc (v, c) ->
      match c with
      | Hike_synth.Module_addr a ->
        let value =
          match
            Section.remap_native ctx ctx.llvm_ctx ctx.llvm_module a
              ~finish:Fun.id
          with
          | Some ptr -> Llvm.const_ptrtoint ptr ty
          | None -> Llvm.const_of_int64 ty a false
        in
        { acc with values = add v value acc.values }
      | _ -> acc)

(* The per-run bindings, built before any body emits. *)
let build ctx : bindings =
  build_addrs ctx (build_components ~addr_bits:ctx.addr_bits ctx.sections)

(* The per-sub storage bindings: each storage var names its alloca and
   entry-line base. *)
let bind_storage scope v base rel =
  scope.Bil2llvm_env.storages :=
    WVarMap.add (wvar_of v) (base, rel) !(scope.storages)

let storage_base scope v : (Llvm.llvalue * int64) option =
  WVarMap.find_opt (wvar_of v) !(scope.storages)

let storage_base_of_id scope ~addr_bits id : (Llvm.llvalue * int64) option =
  storage_base scope (Hike_stack_model.region_mem ~addr_bits id)

(* A memory var's storage global, without the block context. *)
let memory_value ctx v : Llvm.llvalue option =
  Base.Option.bind (Hike_synth.memory_var ctx.synth ~addr_bits:ctx.addr_bits v)
    ~f:(fun mv -> Core.Map.find !(ctx.synth_vals) mv)

(* A storage var's native byte origin, from the component bindings. *)
let storage_origin ctx v : int64 option =
  Core.Map.find !(ctx.synth_origins) v

(* The one resolution: the classification picks the home.  [None] is
   the caller's undef arm.  A module address is its integer word; a
   storage's bytes are its base pointer. *)
let value ctx scope llvm_builder blk_tid v : Bil2llvm_value.t option =
  let classified = Hike_synth.classify ctx.synth v in
  match classified with
  | Some (Hike_synth.Thread_addr off) ->
    let ty = Llvm.integer_type ctx.llvm_ctx ctx.addr_bits in
    let p = Bil2llvm_env.tls_addr ctx llvm_builder ~off in
    Some (Bil2llvm_value.Int (Llvm.build_ptrtoint p ty "tls_value" llvm_builder))
  | Some (Hike_synth.Module_addr a) ->
    let ty = Llvm.integer_type ctx.llvm_ctx ctx.addr_bits in
    Some
      (Bil2llvm_value.Int
         (match Core.Map.find !(ctx.synth_vals) v with
          | Some value -> value
          | None ->
            Base.Option.value
              (Section.remap_native ctx ctx.llvm_ctx ctx.llvm_module a
                 ~finish:(fun ptr -> Llvm.const_ptrtoint ptr ty))
              ~default:(Llvm.const_of_int64 ty a false)))
  | _ -> (
    match resolve_ssa scope blk_tid v with
    | Some value -> Some value
    | None -> (
      match classified with
      | Some (Hike_synth.Env_register _) ->
        Some (Bil2llvm_value.Int (load_env_reg ctx llvm_builder v))
      | Some (Hike_synth.Bytes _) ->
        Base.Option.map ~f:(fun p -> Bil2llvm_value.Ptr p)
          (match storage_base scope v with
           | Some (base, _) -> Some base
           | None -> memory_value ctx v)
      | _ -> None))

(* A ptr value's real address (D6/D7): the storage's base GEP'd at the
   entry-line offset minus the storage's own base.  The window's base IS
   the entry line ([rel = 0]). *)
let materialize ctx scope llvm_builder blk_tid
    (storage : Hike_stack_model.ptr_storage) (off : Llvm.llvalue) :
    Llvm.llvalue =
  let addr_bits = ctx.addr_bits in
  let entry =
    match !(scope.cur_frame) with
    | Some fr -> fr.entry_line
    | None ->
        failwith
          "hike-emit: pointer materialization has no active sub frame"
  in
  let entry_rel () = Llvm.build_sub off entry "entry_rel" llvm_builder in
  let rel_off rel =
    let d = entry_rel () in
    if Stdlib.Int64.equal rel 0L then d
    else
      Llvm.build_sub d (Llvm.const_of_int64 (ctx.i64_ty) rel false) ""
        llvm_builder
  in
  let off_ptr () = Bil2llvm_int.to_ptr llvm_builder off in
  let region_ptr id =
    match storage_base_of_id scope ~addr_bits id with
    | Some (base, rel) ->
      Bil2llvm_ptr.offset ~addr_bits llvm_builder base (rel_off rel)
    | None when Int.equal id Hike_stack_model.residue_id ->
        (* The caller window has no local residue in a frame that never
           names one; keep the entry-line pointer bridge. *)
        off_ptr ()
    | None ->
        failwith
          (Printf.sprintf
             "hike-emit: pointer materialization has no storage for region %d"
             id)
  in
  match storage with
  | Hike_stack_model.Ptr_region id -> region_ptr id
  | Hike_stack_model.Ptr_residue -> region_ptr Hike_stack_model.residue_id
  | Hike_stack_model.Ptr_window -> (
      let wv = Hike_stack_model.hike_window_var ~word:ctx.abi.Hike_abi.word in
      match resolve_ssa scope blk_tid wv with
      | Some wp ->
          Bil2llvm_ptr.offset ~addr_bits llvm_builder
            (Bil2llvm_value.as_ptr llvm_builder wp) (entry_rel ())
      | None ->
          failwith
            "hike-emit: window pointer materialization has no window value")
