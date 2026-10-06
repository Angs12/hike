(* The synth-value lane: one home for every synthetic variable's LLVM
   value.  [build] enumerates the vocabulary once and binds each
   module-lifetime var — a module address through the address map, a
   component var to its global; [value] resolves a var at the use site,
   reading those per-run bindings, the per-sub/block SSA bindings, or
   the environment cell.  The classification is Hike_synth's; the LLVM
   object a kind denotes is the emitter's. *)

open Bap.Std
open Bil2llvm_env

module Section = Bil2llvm_section

(* The per-run bindings, built before any body emits. *)
let build ctx : Llvm.llvalue Var.Map.t =
  Base.List.fold (Hike_synth.bindings ctx.synth) ~init:Var.Map.empty
    ~f:(fun acc (v, c) ->
      match c with
      | Hike_synth.Module_addr a ->
        let ty = Llvm.integer_type ctx.llvm_ctx ctx.addr_bits in
        let value =
          match
            Section.remap_native ctx ctx.llvm_ctx ctx.llvm_module a
              ~finish:Fun.id
          with
          | Some ptr -> Llvm.const_ptrtoint ptr ty
          | None -> Llvm.const_of_int64 ty a false
        in
        Core.Map.set acc ~key:v ~data:value
      | Hike_synth.Storage (Hike_synth.Global i)
      | Hike_synth.Bytes (Hike_synth.Global i) -> (
        let mv =
          Hike_stack_model.sec_comp_mem ~addr_bits:ctx.addr_bits i
        in
        match Core.Map.find !(ctx.sec_comps) mv with
        | Some (base, _) -> Core.Map.set acc ~key:v ~data:base
        | None -> acc)
      | _ -> acc)

(* A memory var's storage global, without the block context. *)
let memory_value ctx v : Llvm.llvalue option =
  Base.Option.bind (Hike_synth.memory_var ~addr_bits:ctx.addr_bits v)
    ~f:(fun mv ->
      match Core.Map.find !(ctx.synth_vals) mv with
      | Some base -> Some base
      | None -> Base.Option.map (Core.Map.find !(ctx.sec_comps) mv) ~f:fst)

(* A storage var's native byte origin, when the component map knows it. *)
let storage_origin ctx v : int64 option =
  Base.Option.map (Core.Map.find !(ctx.sec_comps) v) ~f:snd

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
