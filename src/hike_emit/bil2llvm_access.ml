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

(* Runtime-sized allocas: the size is the runtime amount the def
   descends from its parent — the SP version live before it, or a
   nested allocation's parent frame base — plus the frame's floor (the
   SP positions and round-down slack below the base).  The base, and
   the def's value, is [%vla] past the floor. *)
let create_dynamic_alloc ctx scope llvm_builder blk_tid (def : def term) exp =
  let alloc =
    match Hike_def_slots.def_dyn_alloc def with
    | Some a -> a
    | None -> failwith "hike: dynamic allocation without its stamp"
  in
  let parent =
    match alloc.Hike_def_slots.parent with
    | Some p -> Hike_stack_model.vla_ptr ~addr_bits:ctx.addr_bits p
    | None -> (
      match Hike_def_slots.def_sp_before def with
      | Some v -> v
      | None -> failwith "hike: dynamic allocation without its SSA SP version")
  in
  let below = Int64.neg alloc.Hike_def_slots.floor in
  let amount =
    as_int ctx llvm_builder
      (create_exp ctx scope llvm_builder blk_tid
         (Bil.BinOp (Bil.MINUS, Bil.Var parent, exp)))
  in
  let size =
    if Int64.equal below 0L then amount
    else
      Llvm.build_add amount
        (Llvm.const_of_int64 (Llvm.type_of amount) below false) "" llvm_builder
  in
  Llvm.set_value_name "vla_size" size;
  let vla =
    Llvm.build_array_alloca (Llvm.i8_type ctx.llvm_ctx) size "vla" llvm_builder
  in
  Llvm.set_alignment Hike_abi.stack_align vla;
  let base =
    if Int64.equal below 0L then vla
    else
      Llvm.build_gep (Llvm.i8_type ctx.llvm_ctx) vla
        [| Llvm.const_of_int64 ctx.i64_ty below false |] "vla_base" llvm_builder
  in
  (* The allocation's storage base var binds to its frame base; a
     rewritten VLA address def's value GEPs it directly. *)
  let pv =
    Hike_stack_model.vla_ptr ~addr_bits:ctx.addr_bits (Term.tid def)
  in
  let base = Bil2llvm_value.Ptr base in
  insert_local scope blk_tid pv base;
  bind_ssaval scope pv base;
  base

(* The access's value: a memory node's load/store, or an arithmetic
   pointer rebased to its storage.  [ptr_cell]: the def's whole value is
   a word cell read as the pointer it holds. *)
let access_value ~ptr_cell ctx scope llvm_builder blk_tid def exp =
  match Hike_stack_model.mem_node_of exp with
  | None -> (
      let storage =
        if is_ptr_var (Def.lhs def) then Hike_def_slots.def_ptr_storage def
        else None
      in
      match storage with
      | Some storage -> (
          match create_offset ctx scope llvm_builder blk_tid exp with
          | Some off ->
              insert_ptr_offset scope (Def.lhs def) off;
              Bil2llvm_value.Ptr
                (Bil2llvm_synth.materialize ctx scope llvm_builder blk_tid
                   storage off)
          | None -> create_exp ctx scope llvm_builder blk_tid exp)
      | None -> create_exp ctx scope llvm_builder blk_tid exp)
  | Some node ->
      let mv =
        match node with
        | `Load (Bil.Var mv, _, _) -> Some mv
        | `Store (Bil.Var mv, _, _, _) -> Some mv
        | _ -> None
      in
      (* The synth vocabulary is the one classification: a stack bytes
         var is a region access, the window bytes var a window access,
         a Global bytes var a component access.  Anything else keeps
         the value lane's storage fact. *)
      let classified =
        Base.Option.bind mv ~f:(Hike_synth.classify ctx.synth)
      in
      let kind =
        match classified with
        | Some (Hike_synth.Storage (Hike_synth.Stack id))
        | Some (Hike_synth.Bytes (Hike_synth.Stack id)) -> `Region id
        | Some (Hike_synth.Storage Hike_synth.Window)
        | Some (Hike_synth.Bytes Hike_synth.Window) -> `Window
        | Some (Hike_synth.Storage (Hike_synth.Global _))
        | Some (Hike_synth.Bytes (Hike_synth.Global _)) -> `Component
        | _ -> `Other
      in
      let is_window = match kind with `Window -> true | _ -> false in
      let region_or_window =
        match kind with `Region _ | `Window -> true | _ -> false in
      let sec_comp = match kind with `Component -> true | _ -> false in
      (* The attribution's rewrite re-pointed the memory node at the
         owning storage's mem var: the def's own alloca is the region it
         names (the residue included), never the address operand's. *)
      let storage =
        match kind with
        | `Region id -> Some (Hike_stack_model.Ptr_region id)
        | `Window -> Some Hike_stack_model.Ptr_window
        | `Component | `Other -> Hike_def_slots.def_ptr_storage def
      in
      (match mv, sec_comp, region_or_window, node with
      | Some mv, true, _, `Load (_, addr, size) ->
          sec_comp_access ~ptr_cell ctx scope llvm_builder blk_tid exp ~store:false
            mv addr ~data:None size
      | Some mv, true, _, `Store (_, addr, data, size) ->
          sec_comp_access ctx scope llvm_builder blk_tid exp ~store:true mv
            addr ~data:(Some data) size
      | _, _, true, `Load (_, addr, size) ->
          storage_access ~ptr_cell ~is_window ~storage ctx scope llvm_builder
            blk_tid (`Load (addr, size)) exp
      | _, _, true, `Store (_, addr, data, size) ->
          storage_access ~is_window ~storage ctx scope llvm_builder
            blk_tid (`Store (addr, data, size)) exp
      | _, _, _, `Load (mem, addr, size)
        when ptr_cell
             && (match tls_classify ctx addr with Not_tls -> true | _ -> false) ->
          plain_load ~ptr_cell ctx scope llvm_builder blk_tid mem addr size
      | _ -> create_exp ctx scope llvm_builder blk_tid exp)

let mem_access ?(ptr_cell = false) ctx scope llvm_builder blk_tid def_tag def
    exp =
  match def_tag with
  | Some def_tag when Hike_stack_model.is_return_address_tag def_tag -> (
      match Hike_stack_model.mem_node_of exp with
      | Some (`Load (_, addr, size))
        when Size.in_bits size <= Hike_abi.word_bits ctx.abi
             && Base.Option.is_none
                  (Hike_stack_model.store_data_of_rhs (Def.rhs def)) ->
          let marker = marker_of_size size in
          let emit () =
            cell_value ctx ~ptr:ptr_cell size
              (Llvm.undef (cell_type ctx ~ptr:ptr_cell size))
          in
          let rewrite marker = rewrite_mem_node exp addr size marker in
          emit_with_marker ctx scope llvm_builder blk_tid marker ~emit ~rewrite
      | _ -> access_value ~ptr_cell ctx scope llvm_builder blk_tid def exp)
  | _ -> access_value ~ptr_cell ctx scope llvm_builder blk_tid def exp

(* The analytical accesses are generated by [Hike_atomic], with all inputs
   captured before the tagged load. Operation identity comes from BAP. *)
let plan_atomics (sub : sub term) : atomic_action Tid.Map.t =
  Term.enum blk_t sub |> Seq.fold ~init:Tid.Map.empty ~f:(fun plan blk ->
      let inputs = ref Core.Int.Map.empty in
      Term.enum def_t blk |> Seq.fold ~init:plan ~f:(fun plan d ->
          Base.Option.iter (Term.get_attr d Hike_atomic.input) ~f:(fun i ->
              inputs := Core.Map.set !inputs ~key:i ~data:(Bil.Var (Def.lhs d)));
          match Term.get_attr d Hike_atomic.operation with
          | Some op ->
            let operand i = match Core.Map.find !inputs i with
              | Some e -> e | None -> failwith "hike-emit: atomic input is missing" in
            let kind = match op with
              | Hike_atomic.Add -> Rmw (Llvm.AtomicRMWBinOp.Add,operand 0)
              | Sub -> Rmw (Llvm.AtomicRMWBinOp.Sub,operand 0)
              | And -> Rmw (Llvm.AtomicRMWBinOp.And,operand 0)
              | Or -> Rmw (Llvm.AtomicRMWBinOp.Or,operand 0)
              | Xor -> Rmw (Llvm.AtomicRMWBinOp.Xor,operand 0)
              | Xchg -> Rmw (Llvm.AtomicRMWBinOp.Xchg,operand 0)
              | Cmpxchg -> Compare_exchange (operand 0,operand 1)
              | Neg -> Negate in
            (match Def.rhs d with
             | Bil.Load (mem,addr,_,size) ->
               Core.Map.set plan ~key:(Term.tid d)
                 ~data:(Atomic_begin {kind;mem;addr;size})
             | _ -> failwith "hike-emit: atomic load was lost")
          | None when Term.has_attr d Hike_atomic.write ->
            (match Def.rhs d with
             | Bil.Store (_,_,data,_,_) ->
               Core.Map.set plan ~key:(Term.tid d) ~data:(Atomic_value data)
             | _ -> failwith "hike-emit: atomic store was lost")
          | None -> plan))

(* The atomic op's target pointer: the same resolution lanes an
   ordinary access takes. *)
let rec atomic_ptr ctx scope llvm_builder blk_tid mem addr =
  let component =
    match mem with
    | Bil.Var mv when (
        match Hike_synth.storage_of ctx.synth mv with
        | Some (Hike_synth.Global _) -> true
        | _ -> false) ->
      let index =
        as_int ctx llvm_builder (create_exp ctx scope llvm_builder blk_tid addr)
      in
      Bil2llvm_memory.component_ptr ctx llvm_builder mv index
    | _ -> None
  in
  match component with
  | Some ptr -> ptr
  | None -> (
    match tls_classify ctx addr with
    | Not_tls ->
      let a = create_exp ctx scope llvm_builder blk_tid addr in
      raw_addr_ptr ctx llvm_builder a
    | cls -> tls_ptr ctx scope llvm_builder blk_tid cls)

(* A raw address's pointer: a constant resolves through the sections,
   anything else is the value's pointer. *)
and raw_addr_ptr ctx llvm_builder (a : Bil2llvm_value.t) =
  match a with
  | Bil2llvm_value.Int i when Base.Option.is_some (Llvm.int64_of_const i) ->
    let ai = Base.Option.value_exn (Llvm.int64_of_const i) in
    Bil2llvm_memory.const_addr_ptr ctx llvm_builder ai
      ~fallback:(fun () ->
        Llvm.const_inttoptr
          (Llvm.const_int (Llvm.i64_type ctx.llvm_ctx) (Int64.to_int ai))
          ctx.ptr_ty)
  | _ -> as_ptr llvm_builder a

let create_atomic ctx scope llvm_builder blk_tid action : Bil2llvm_value.t =
  match action with
  | Atomic_value rhs -> create_exp ctx scope llvm_builder blk_tid rhs
  | Atomic_begin { kind; mem; addr; size } ->
    Bil2llvm_value.Int (
    let bits = Size.in_bits size in
    let value exp =
      let v = as_int ctx llvm_builder (create_exp ctx scope llvm_builder blk_tid exp) in
      coerce_int_width ctx.llvm_ctx llvm_builder ~bits:(Bil2llvm_int.width v) v bits in
    let ptr = atomic_ptr ctx scope llvm_builder blk_tid mem addr in
    match kind with
    | Rmw (op, operand) ->
      let old = Llvm.build_atomicrmw op ptr (value operand)
          Llvm.AtomicOrdering.SequentiallyConsistent false "xold" llvm_builder in
      Llvm.set_alignment 1 old;
      old
    | Compare_exchange (expected, desired) ->
      let expected = value expected and desired = value desired in
      let result = Bil2llvm_atomic.cmpxchg ptr expected desired llvm_builder in
      Llvm.set_alignment 1 result;
      Llvm.build_extractvalue result 0 "xold" llvm_builder
    | Negate -> Bil2llvm_atomic.negate ctx.llvm_module ptr bits llvm_builder)

let create_def ctx scope blk_tid llvm_builder sub_tid def =
  let var = Def.lhs def in
  let exp = Def.rhs def in
  let def_tag = find_def_tag def in
  let ptr = is_ptr_var var in
  let ptr_cell = ptr && (match exp with Bil.Load _ -> true | _ -> false) in
  let res =
    match Core.Map.find !(scope.atomic_plan) (Term.tid def) with
    | Some action -> create_atomic ctx scope llvm_builder blk_tid action
    | None ->
        if Hike_def_slots.def_is_dyn_alloc def then
          create_dynamic_alloc ctx scope llvm_builder blk_tid def exp
        else
          mem_access ~ptr_cell ctx scope llvm_builder blk_tid def_tag def exp
  in
  (* The def's value takes the def's type.  A store's def binds the
     memory state, which carries no value to type. *)
  let res =
    if Base.Option.is_some (Hike_stack_model.store_data_of_rhs exp) then res
    else Bil2llvm_value.coerce ~addr_bits:ctx.addr_bits llvm_builder ~ptr res
  in
  insert_local scope blk_tid var res;
  (* An SSA version has one def: its value is valid wherever the def
     dominates, so the binding is sub-wide. *)
  if Var.index var > 0 then bind_ssaval scope var res;
  (* An environment register's def also stores the process-global cell:
     the value must outlive the sub (its lane rides no signature). *)
  if Option.is_some (Hike_synth.env_of ctx.synth var) then
    ignore
      (Llvm.build_store (Bil2llvm_value.ll res) (env_global ctx var)
         llvm_builder)
