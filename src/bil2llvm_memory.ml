(* Address-based LLVM memory operations. *)

open Bap.Std
open Bil2llvm_env
open Bil2llvm_section

let load_ptr ?(name = "") llvm_builder ty ptr =
  Llvm.build_load ty ptr name llvm_builder

let store_ptr llvm_builder value ptr =
  let _ : Llvm.llvalue = Llvm.build_store value ptr llvm_builder in
  value

let const_load_in ctx llvm_builder section addr addr_i64 size =
  let base = resolve_addr_in ctx llvm_builder section addr in
  if Base.List.exists ctx.copy_relocs ~f:(Int64.equal addr_i64) then begin
    let p = load_ptr llvm_builder (Llvm.i64_type ctx.llvm_ctx) base in
    let pp = Llvm.build_inttoptr p (Llvm.pointer_type ctx.llvm_ctx) "" llvm_builder in
    load_ptr llvm_builder (Llvm.integer_type ctx.llvm_ctx size) pp
  end else load_ptr llvm_builder (Llvm.integer_type ctx.llvm_ctx size) base

let const_load ctx llvm_builder addr size ~fallback =
  match section_of_addr ctx.sections addr with
  | Some section ->
      let v = Word.to_int64_exn addr in
      const_load_in ctx llvm_builder section addr v size
  | None -> fallback ()

(* The section-owner pointer of a constant address: the atomic path's
   target (the store path's own resolution, without the value). *)
let const_addr_ptr ctx llvm_builder addr_i64 ~fallback =
  let w = Word.of_int64 ~width:64 addr_i64 in
  match section_of_addr ctx.sections w with
  | Some section ->
    let base = resolve_addr_in ctx llvm_builder section w in
    if Base.List.exists ctx.copy_relocs ~f:(Int64.equal addr_i64) then begin
      let p = load_ptr llvm_builder ctx.i64_ty base in
      Llvm.build_inttoptr p (Llvm.pointer_type ctx.llvm_ctx) "" llvm_builder
    end else base
  | None -> fallback ()

let const_store ctx llvm_builder addr ~data ~fallback =
  match section_of_addr ctx.sections addr with
  | Some section ->
      let base = resolve_addr_in ctx llvm_builder section addr in
      let value = data () in
      if Base.List.exists ctx.copy_relocs ~f:(Int64.equal (Word.to_int64_exn addr)) then begin
        let p = load_ptr llvm_builder ctx.i64_ty base in
        let pp = Llvm.build_inttoptr p (Llvm.pointer_type ctx.llvm_ctx) "" llvm_builder in
        store_ptr llvm_builder value pp
      end else store_ptr llvm_builder value base
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
