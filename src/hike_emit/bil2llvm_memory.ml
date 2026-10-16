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
  Base.Option.map (Bil2llvm_synth.memory_value ctx v) ~f:(fun base ->
      Llvm.build_gep (Llvm.i8_type ctx.llvm_ctx) base [| index |] ""
        llvm_builder)

let const_load ctx llvm_builder addr ty ~fallback =
  match section_of_addr ctx.address addr with
  | Some section ->
      load_ptr llvm_builder ty (resolve_addr_in ctx llvm_builder section addr)
  | None -> fallback ()

(* The section-owner pointer of a constant address: the atomic path's
   target (the store path's own resolution, without the value). *)
let const_addr_ptr ctx llvm_builder addr_i64 ~fallback =
  let w = Word.of_int64 ~width:ctx.addr_bits addr_i64 in
  match section_of_addr ctx.address w with
  | Some section -> resolve_addr_in ctx llvm_builder section w
  | None -> fallback ()

let const_store ctx llvm_builder addr ~data ~fallback =
  match section_of_addr ctx.address addr with
  | Some section ->
      let base = resolve_addr_in ctx llvm_builder section addr in
      store_ptr llvm_builder (data ()) base
  | None -> fallback ()

(* A raw access: a pointer address is the cell; an integer address
   resolves through the sections when constant, else is the cell's
   pointer. *)
let load ctx llvm_builder (addr : Bil2llvm_value.t) ty =
  let raw () = load_ptr llvm_builder ty (Bil2llvm_value.as_ptr llvm_builder addr) in
  match addr with
  | Bil2llvm_value.Int a -> (
    match Llvm.int64_of_const a with
    | Some v ->
      const_load ctx llvm_builder (Word.of_int64 ~width:ctx.addr_bits v) ty
        ~fallback:raw
    | None -> raw ())
  | Bil2llvm_value.Ptr _ -> raw ()

let store ctx llvm_builder (value : Llvm.llvalue) (addr : Bil2llvm_value.t) =
  let raw () = store_ptr llvm_builder value (Bil2llvm_value.as_ptr llvm_builder addr) in
  match addr with
  | Bil2llvm_value.Int a -> (
    match Llvm.int64_of_const a with
    | Some v ->
      const_store ctx llvm_builder (Word.of_int64 ~width:ctx.addr_bits v)
        ~data:(fun () -> value) ~fallback:raw
    | None -> raw ())
  | Bil2llvm_value.Ptr _ -> raw ()
