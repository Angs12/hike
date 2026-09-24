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
  let old_sp =
    create_exp ctx scope llvm_builder blk_tid (Bil.Var (Def.lhs def))
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

(* The mem node's region/window var, when the rewrite re-pointed it. *)
let region_mem_of (e : exp) : var option =
  match Hike_stack_model.mem_node_where Hike_stack_model.is_region_mem e with
  | Some (`Load (Bil.Var v, _, _)) | Some (`Store (Bil.Var v, _, _, _)) ->
    Some v
  | _ -> None

let window_mem_of (e : exp) : var option =
  match Hike_stack_model.mem_node_where Hike_stack_model.is_window_mem e with
  | Some (`Load (Bil.Var v, _, _)) | Some (`Store (Bil.Var v, _, _, _)) ->
    Some v
  | _ -> None

(* Dispatches an access: region/window mems to their storage, Dead
   to poison, the return-address cell to undef; everything else
   emits raw. *)
let mem_access ctx scope llvm_builder blk_tid sub_tid fr def_tag
    (def : def term) (exp : exp) =
  let var = Def.lhs def in
  match region_mem_of exp with
  | Some mv -> region_mem_access ctx scope llvm_builder blk_tid fr mv exp
  | None -> (
    match window_mem_of exp with
    | Some mv -> window_mem_access ctx scope llvm_builder blk_tid fr mv exp
    | None -> (
      match def_tag with
      | Some Hike_stack_model.Tag.Dead ->
          if not (Core.Set.mem !(scope.dead_warned) sub_tid) then begin
            scope.dead_warned := Core.Set.add !(scope.dead_warned) sub_tid;
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
      | _ -> create_exp ctx scope llvm_builder blk_tid exp))

let create_def ctx scope blk_tid llvm_builder sub_tid fr def =
  let var = Def.lhs def in
  let exp = Def.rhs def in
  let def_tag = find_def_tag def in
  let res =
    if Hike_def_slots.def_is_dyn_alloc def then
      create_dynamic_alloc ctx scope llvm_builder blk_tid def exp
    else if Hike_def_slots.def_is_rip_relative def then
      create_rip_relative_addr ctx scope llvm_builder blk_tid exp
    else mem_access ctx scope llvm_builder blk_tid sub_tid fr def_tag def exp
  in
  (* A def whose value lives at/above the entry line addresses the
     caller's window: re-base from this sub's anchor to the
     hike_window parameter.  Memory-node defs are skipped — their
     value is loaded data, not an address. *)
  let res =
    if Hike_def_slots.def_is_window_value def then
      let w_i64 =
        let wv = Hike_stack_model.hike_window_var ~word:ctx.abi.Abi.word in
        match get_local scope blk_tid wv with
        | Some v ->
            Llvm.build_ptrtoint v (ctx.i64_ty) "" llvm_builder
        | None -> Llvm.undef (ctx.i64_ty)
      in
      let stack0 = frame_stack0 fr in
      let rel = Llvm.build_sub res stack0 "" llvm_builder in
      Llvm.build_add w_i64 rel "" llvm_builder
    else res
  in
  insert_local scope blk_tid var res
