(* Emitter memory lane: tag dispatch, fission markers, region accesses. *)

open Bap.Std
open Bap.Std.Bil.Types
module Abi = Hike_abi
open Bil2llvm_env
open Bil2llvm_exp
open Bil2llvm_section

let find_def_tag (def : def term) : Hike_stack_model.Tag.t option =
  Hike_def_slots.sec_tag def

(* Runtime-sized allocas: the def's value is the post-event SP, so
   the alloca size is (old SP − new SP) however the size was spelled. *)
let create_dynamic_alloc ctx scope llvm_builder blk_tid (def : def term) exp =
  (* The SP in scope before this def: the block's entry version (the
     def's own lhs is a fresh SSA version, bound only by it). *)
  let old_sp =
    match
      Base.Option.bind (entry_version scope blk_tid ctx.sp)
        ~f:(get_ssaval scope)
    with
    | Some v -> v
    | None ->
        create_exp ctx scope llvm_builder blk_tid
          (Bil.Var (Var.base (Def.lhs def)))
  in
  let new_sp = create_exp ctx scope llvm_builder blk_tid exp in
  let size = Llvm.build_sub old_sp new_sp "vla_size" llvm_builder in
  let vla =
    Llvm.build_array_alloca (Llvm.i8_type ctx.llvm_ctx) size "vla"
      llvm_builder
  in
  Llvm.set_alignment Hike_abi.stack_align vla;
  Llvm.build_ptrtoint vla (ctx.i64_ty) "vla_i64"
    llvm_builder

(* Region/window access emission lives in [Bil2llvm_exp]. *)

(* Dispatches an access by its tag: Dead is poison, the return-address
   cell is undef, and everything else emits through the generic exp
   path — whose own arms route region/window/section-component mem
   vars to their storages before any raw emission. *)
let mem_access ctx scope llvm_builder blk_tid sub_tid def_tag
    (def : def term) (exp : exp) =
  let var = Def.lhs def in
  match def_tag with
  | Some Hike_stack_model.Tag.Dead ->
      if not !(scope.dead_warned) then begin
        scope.dead_warned := true;
        (* Warning text is a grepped contract. *)
        Hike_diag.warn
          "guarded: sub %s: stack access classified Dead (empty range): def %s rhs=%s"
          (Tid.name sub_tid) (Var.name var) (Format.asprintf "%a" Exp.pp exp)
      end;
      Llvm.poison (typ_lltype ctx (Var.typ var))
  | Some def_tag when Hike_stack_model.is_return_address_tag def_tag -> (
      match find_mem_node (Def.rhs def) with
      | Some (`Load (addr, size))
        when Size.in_bits size <= Hike_abi.word_bits ctx.abi
             && Base.Option.is_none
                  (Hike_stack_model.store_data_of_rhs (Def.rhs def)) ->
          let marker = marker_of_size size in
          let emit () =
            Llvm.undef
              (Llvm.integer_type ctx.llvm_ctx (Size.in_bits size))
          in
          let rewrite marker = rewrite_mem_node exp addr size marker in
          emit_with_marker ctx scope llvm_builder blk_tid marker ~emit ~rewrite
      | _ -> create_exp ctx scope llvm_builder blk_tid exp)
  | _ -> create_exp ctx scope llvm_builder blk_tid exp

let create_def ctx scope blk_tid llvm_builder sub_tid _fr def =
  let var = Def.lhs def in
  let exp = Def.rhs def in
  let def_tag = find_def_tag def in
  let res =
    if Hike_def_slots.def_is_dyn_alloc def then
      create_dynamic_alloc ctx scope llvm_builder blk_tid def exp
    else if Hike_def_slots.def_is_rip_relative def then
      create_rip_relative_addr ctx scope llvm_builder blk_tid exp
    else mem_access ctx scope llvm_builder blk_tid sub_tid def_tag def exp
  in
  insert_local scope blk_tid var res;
  (* An SSA version has one def: its value is valid wherever the def
     dominates, so the binding is sub-wide. *)
  if Var.index var > 0 then bind_ssaval scope var res
