(* Address-based LLVM memory operations. *)

open Bap.Std
open Bil2llvm_env
open Bil2llvm_section

let load_ptr ?(name = "") llvm_builder ty ptr =
  Llvm.build_load ty ptr name llvm_builder

let store_ptr llvm_builder value ptr =
  let _ : Llvm.llvalue = Llvm.build_store value ptr llvm_builder in
  value

let component_ptr ctx llvm_builder v index =
  match Hike_synth.memory_var ~addr_bits:ctx.addr_bits v with
  | Some mv ->
    Base.Option.map (Core.Map.find !(ctx.sec_comps) mv) ~f:(fun (base, _) ->
        Llvm.build_gep (Llvm.i8_type ctx.llvm_ctx) base [| index |] ""
          llvm_builder)
  | None -> None

let const_load_in ctx llvm_builder section addr size =
  let base = resolve_addr_in ctx llvm_builder section addr in
  load_ptr llvm_builder (Llvm.integer_type ctx.llvm_ctx size) base

let const_load ctx llvm_builder addr size ~fallback =
  match section_of_addr ctx.sections addr with
  | Some section -> const_load_in ctx llvm_builder section addr size
  | None -> fallback ()

(* The section-owner pointer of a constant address: the atomic path's
   target (the store path's own resolution, without the value). *)
let const_addr_ptr ctx llvm_builder addr_i64 ~fallback =
  let w = Word.of_int64 ~width:64 addr_i64 in
  match section_of_addr ctx.sections w with
  | Some section -> resolve_addr_in ctx llvm_builder section w
  | None -> fallback ()

let const_store ctx llvm_builder addr ~data ~fallback =
  match section_of_addr ctx.sections addr with
  | Some section ->
      let base = resolve_addr_in ctx llvm_builder section addr in
      store_ptr llvm_builder (data ()) base
  | None -> fallback ()

let load ctx llvm_builder (addr, size) =
  match Llvm.int64_of_const addr with
  | Some v ->
      const_load ctx llvm_builder (Word.of_int64 ~width:64 v) size
        ~fallback:(fun () ->
          let ptr = create_addr_ptr ctx llvm_builder addr in
          load_ptr llvm_builder (Llvm.integer_type ctx.llvm_ctx size) ptr)
  | None ->
      let ptr = create_addr_ptr ctx llvm_builder addr in
      load_ptr llvm_builder (Llvm.integer_type ctx.llvm_ctx size) ptr

let store ctx llvm_builder (value, addr) =
  match Llvm.int64_of_const addr with
  | Some v ->
      const_store ctx llvm_builder (Word.of_int64 ~width:64 v)
        ~data:(fun () -> value)
        ~fallback:(fun () ->
          let ptr = create_addr_ptr ctx llvm_builder addr in
          store_ptr llvm_builder value ptr)
  | None ->
      let ptr = create_addr_ptr ctx llvm_builder addr in
      store_ptr llvm_builder value ptr
