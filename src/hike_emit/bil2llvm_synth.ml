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

(* A memory var's storage global, without the block context. *)
let memory_value ctx v : Llvm.llvalue option =
  Base.Option.bind (Hike_synth.memory_var ~addr_bits:ctx.addr_bits v)
    ~f:(fun mv -> Core.Map.find !(ctx.synth_vals) mv)

(* A storage var's native byte origin, from the component bindings. *)
let storage_origin ctx v : int64 option =
  Core.Map.find !(ctx.synth_origins) v

(* The one resolution: the classification picks the home.  [None] is
   the caller's undef arm. *)
let value ctx scope llvm_builder blk_tid v : Llvm.llvalue option =
  let classified = Hike_synth.classify ctx.synth v in
  match classified with
  | Some (Hike_synth.Module_addr a) ->
    let ty = Llvm.integer_type ctx.llvm_ctx ctx.addr_bits in
    Some
      (match Core.Map.find !(ctx.synth_vals) v with
       | Some value -> value
       | None ->
         Base.Option.value
           (Section.remap_native ctx ctx.llvm_ctx ctx.llvm_module a
              ~finish:(fun ptr -> Llvm.const_ptrtoint ptr ty))
           ~default:(Llvm.const_of_int64 ty a false))
  | _ -> (
    match
      Base.Option.first_some (get_ssaval scope v) (get_local scope blk_tid v)
    with
    | Some value -> Some value
    | None -> (
      match classified with
      | Some (Hike_synth.Env_register _) ->
        Some (load_env_reg ctx llvm_builder v)
      | Some (Hike_synth.Bytes _) -> memory_value ctx v
      | _ -> None))
