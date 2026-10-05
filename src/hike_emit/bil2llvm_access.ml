(* Per-definition access routing and dynamic allocations. *)

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

(* The machine's atomic RMW: a same-address load→store pair in one
   block is the lock-prefixed instruction whose atomicity BAP's
   single-threaded BIL drops; the pair renders as one atomicrmw (a
   sound strengthening) and the pair's other operand is its value. *)
let create_atomic_rmw ctx scope llvm_builder blk_tid exp op other =
  match exp with
  | Bil.Store (_, addr, _, _, size) ->
    let v = create_exp ctx scope llvm_builder blk_tid other in
    let ptr =
      if is_tls_addr ctx addr then
        create_tls_ptr ctx scope llvm_builder blk_tid addr
      else
        let a = create_exp ctx scope llvm_builder blk_tid addr in
        match Llvm.int64_of_const a with
        | Some ai ->
          Bil2llvm_memory.const_addr_ptr ctx llvm_builder ai
            ~fallback:(fun () ->
              Llvm.const_inttoptr
                (Llvm.const_int (Llvm.i64_type ctx.llvm_ctx)
                   (Int64.to_int ai))
                ctx.ptr_ty)
        | None ->
          Bil2llvm_section.create_addr_ptr ctx llvm_builder a
          |> fun p ->
          if Llvm.type_of p = ctx.ptr_ty then p
          else Llvm.build_inttoptr p ctx.ptr_ty "" llvm_builder
    in
    let bits = Size.in_bits size in
    let v =
      let w = Llvm.integer_bitwidth (Llvm.type_of v) in
      if w = bits then v
      else if w > bits then Llvm.build_trunc v (Llvm.integer_type ctx.llvm_ctx bits) "" llvm_builder
      else Llvm.build_zext v (Llvm.integer_type ctx.llvm_ctx bits) "" llvm_builder
    in
    let amop =
      match op with
      | Bil.PLUS -> Llvm.AtomicRMWBinOp.Add
      | Bil.MINUS -> Llvm.AtomicRMWBinOp.Sub
      | Bil.AND -> Llvm.AtomicRMWBinOp.And
      | Bil.OR -> Llvm.AtomicRMWBinOp.Or
      | Bil.XOR -> Llvm.AtomicRMWBinOp.Xor
      | _ -> failwith "hike-emit: rmw: unsupported binop"
    in
    let old =
      Llvm.build_atomicrmw amop ptr v Llvm.AtomicOrdering.Monotonic false ""
        llvm_builder
    in
    (* The pair's readers keep the decomposed shape: the pre-reads read
       the old cell (emitted before), the post-reads re-load.  The def's
       own value is the stored data, as the plain store binds. *)
    let binop b x y =
      match op with
      | Bil.PLUS -> Llvm.build_add x y "" b
      | Bil.MINUS -> Llvm.build_sub x y "" b
      | Bil.AND -> Llvm.build_and x y "" b
      | Bil.OR -> Llvm.build_or x y "" b
      | Bil.XOR -> Llvm.build_xor x y "" b
      | _ -> failwith "hike-emit: rmw: unsupported binop"
    in
    binop llvm_builder old v
  | _ -> failwith "hike-emit: rmw: the marked def is not a store"

let create_def ctx scope blk_tid llvm_builder sub_tid _fr def =
  let var = Def.lhs def in
  let exp = Def.rhs def in
  let def_tag = find_def_tag def in
  let want = if is_ptr_var var then Some ctx.ptr_ty else None in
  let res =
    match Core.Map.find !(scope.rmw_stores) (Term.tid def) with
    | Some (op, other) -> create_atomic_rmw ctx scope llvm_builder blk_tid exp op other
    | None ->
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
