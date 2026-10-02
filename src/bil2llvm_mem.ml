(* Emitter memory lane: dynamic allocation and the per-def access
   dispatch.  A stack/VLA address is a real pointer; the emitter lowers
   it mechanically. *)

open Bap.Std
open Bap.Std.Bil.Types
module Abi = Hike_abi
open Bil2llvm_env
open Bil2llvm_ptr
open Bil2llvm_exp
open Bil2llvm_section

let find_def_tag (def : def term) : Hike_stack_model.Tag.t option =
  Hike_def_slots.sec_tag def

(* Runtime-sized allocas: the def's value is the post-event SP; the
   alloca size is (old SP − new SP) in the model offset world.  The
   [%vla] pointer IS the post-VLA SP's value. *)
let create_dynamic_alloc ctx scope llvm_builder blk_tid (def : def term) exp =
  let entry_off =
    Llvm.const_of_int64 (ctx.i64_ty) Hike_stack_model.segment_base false
  in
  let old_off =
    match entry_version scope blk_tid ctx.sp with
    | Some v -> Base.Option.value (get_ptr_offset scope v) ~default:entry_off
    | None -> entry_off
  in
  let new_off =
    match create_offset ctx scope llvm_builder blk_tid exp with
    | Some o -> o
    | None ->
        as_integer ctx llvm_builder
          (create_exp ctx scope llvm_builder blk_tid exp)
  in
  let size = Llvm.build_sub old_off new_off "vla_size" llvm_builder in
  let vla =
    Llvm.build_array_alloca (Llvm.i8_type ctx.llvm_ctx) size "vla" llvm_builder
  in
  Llvm.set_alignment Hike_abi.stack_align vla;
  (* The allocation's storage base var binds to its %vla pointer; a
     rewritten VLA address def's value GEPs it directly. *)
  let pv =
    Hike_stack_model.vla_ptr ~addr_bits:ctx.addr_bits (Term.tid def)
  in
  insert_local scope blk_tid pv vla;
  bind_ssaval scope pv vla;
  vla

(* The access's value: a memory node's load/store, or an arithmetic
   pointer rebased to its storage. *)
let access_value ?want ctx scope llvm_builder blk_tid sub_tid def exp =
  match Hike_stack_model.mem_node_of exp with
  | None -> (
      match want with
      | Some _ -> (
          match Hike_def_slots.def_ptr_storage def with
          | Some storage -> (
              match create_offset ctx scope llvm_builder blk_tid exp with
              | Some off ->
                  insert_ptr_offset scope (Def.lhs def) off;
                  Bil2llvm_ptr.materialize ctx scope llvm_builder blk_tid
                    storage off
              | None -> create_exp ?want ctx scope llvm_builder blk_tid exp)
          | None -> create_exp ?want ctx scope llvm_builder blk_tid exp)
      | None -> create_exp ctx scope llvm_builder blk_tid exp)
  | Some node ->
      let mv =
        match node with
        | `Load (Bil.Var mv, _, _) -> Some mv
        | `Store (Bil.Var mv, _, _, _) -> Some mv
        | _ -> None
      in
      let region_or_window =
        match mv with
        | Some mv ->
            Hike_stack_model.is_region_mem mv
            || Hike_stack_model.is_window_mem mv
        | None -> false
      in
      let sec_comp =
        match mv with
        | Some mv -> Hike_stack_model.is_sec_comp_mem mv
        | None -> false
      in
      (* The attribution's rewrite re-pointed the memory node at the
         owning storage's mem var: the def's own alloca is the region it
         names (the residue included), never the address operand's. *)
      let storage =
        match mv with
        | Some mv -> (
            match Hike_stack_model.region_id_of_mem mv with
            | Some id -> Some (Hike_stack_model.Ptr_region id)
            | None ->
                if Hike_stack_model.is_window_mem mv then
                  Some Hike_stack_model.Ptr_window
                else Hike_def_slots.def_ptr_storage def)
        | None -> Hike_def_slots.def_ptr_storage def
      in
      (match mv, sec_comp, region_or_window, node with
      | Some mv, true, _, `Load (_, addr, size) ->
          sec_comp_access ?want ctx scope llvm_builder blk_tid ~store:false
            mv addr ~data:None (Size.in_bits size)
      | Some mv, true, _, `Store (_, addr, data, size) ->
          sec_comp_access ?want ctx scope llvm_builder blk_tid ~store:true mv
            addr ~data:(Some data) (Size.in_bits size)
      | _, _, true, `Load (_, addr, size) ->
          let is_window =
            match mv with
            | Some mv -> Hike_stack_model.is_window_mem mv
            | None -> false
          in
          storage_access ?want ~is_window ~storage ctx scope llvm_builder
            blk_tid (`Load (addr, size)) exp
      | _, _, true, `Store (_, addr, data, size) ->
          let is_window =
            match mv with
            | Some mv -> Hike_stack_model.is_window_mem mv
            | None -> false
          in
          storage_access ?want ~is_window ~storage ctx scope llvm_builder
            blk_tid (`Store (addr, data, size)) exp
      | _ -> create_exp ?want ctx scope llvm_builder blk_tid exp)

let mem_access ?want ctx scope llvm_builder blk_tid sub_tid def_tag def exp =
  let var = Def.lhs def in
  let fallback_ty =
    match want with Some t -> t | None -> typ_lltype ctx (Var.typ var)
  in
  match def_tag with
  | Some Hike_stack_model.Tag.Dead ->
      if not !(scope.dead_warned) then begin
        scope.dead_warned := true;
        (* Warning text is a grepped contract. *)
        Hike_diag.warn
          "guarded: sub %s: stack access classified Dead (empty range): def %s rhs=%s"
          (Tid.name sub_tid) (Var.name var) (Format.asprintf "%a" Exp.pp exp)
      end;
      Llvm.poison fallback_ty
  | Some def_tag when Hike_stack_model.is_return_address_tag def_tag -> (
      match Hike_stack_model.mem_node_of exp with
      | Some (`Load (_, addr, size))
        when Size.in_bits size <= Hike_abi.word_bits ctx.abi
             && Base.Option.is_none
                  (Hike_stack_model.store_data_of_rhs (Def.rhs def)) ->
          let marker = marker_of_size size in
          let emit () = Llvm.undef fallback_ty in
          let rewrite marker = rewrite_mem_node exp addr size marker in
          emit_with_marker ?want ctx scope llvm_builder blk_tid marker ~emit
            ~rewrite
      | _ -> access_value ?want ctx scope llvm_builder blk_tid sub_tid def exp)
  | _ -> access_value ?want ctx scope llvm_builder blk_tid sub_tid def exp

let create_def ctx scope blk_tid llvm_builder sub_tid _fr def =
  let var = Def.lhs def in
  let exp = Def.rhs def in
  let def_tag = find_def_tag def in
  let want = if is_ptr_var var then Some ctx.ptr_ty else None in
  let res =
    if Hike_def_slots.def_is_dyn_alloc def then
      create_dynamic_alloc ctx scope llvm_builder blk_tid def exp
    else if Hike_def_slots.def_is_rip_relative def then
      create_rip_relative_addr ctx scope llvm_builder blk_tid exp
    else mem_access ?want ctx scope llvm_builder blk_tid sub_tid def_tag def exp
  in
  insert_local scope blk_tid var res;
  (* An SSA version has one def: its value is valid wherever the def
     dominates, so the binding is sub-wide. *)
  if Var.index var > 0 then bind_ssaval scope var res;
  (* An environment register's def also stores the process-global cell:
     the value must outlive the sub (its lane rides no signature). *)
  if Abi.is_env_reg ctx.abi var then
    ignore (Llvm.build_store res (env_global ctx var) llvm_builder)
