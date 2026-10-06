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
      (* The synth vocabulary is the one classification: a stack bytes
         var is a region access, the window bytes var a window access,
         a Global bytes var a component access.  Anything else keeps
         the value lane's storage fact. *)
      let classified =
        Base.Option.bind mv ~f:(Hike_synth.classify ctx.synth)
      in
      let is_region =
        match classified with
        | Some (Hike_synth.Storage (Hike_synth.Stack _))
        | Some (Hike_synth.Bytes (Hike_synth.Stack _)) -> true
        | _ -> false
      in
      let is_window =
        match classified with
        | Some (Hike_synth.Storage Hike_synth.Window)
        | Some (Hike_synth.Bytes Hike_synth.Window) -> true
        | _ -> false
      in
      let region_or_window = is_region || is_window in
      let sec_comp =
        match classified with
        | Some (Hike_synth.Storage (Hike_synth.Global _))
        | Some (Hike_synth.Bytes (Hike_synth.Global _)) -> true
        | _ -> false
      in
      (* The attribution's rewrite re-pointed the memory node at the
         owning storage's mem var: the def's own alloca is the region it
         names (the residue included), never the address operand's. *)
      let storage =
        match classified with
        | Some (Hike_synth.Storage (Hike_synth.Stack id))
        | Some (Hike_synth.Bytes (Hike_synth.Stack id)) ->
          Some (Hike_stack_model.Ptr_region id)
        | Some (Hike_synth.Storage Hike_synth.Window)
        | Some (Hike_synth.Bytes Hike_synth.Window) ->
          Some Hike_stack_model.Ptr_window
        | _ -> Hike_def_slots.def_ptr_storage def
      in
      (match mv, sec_comp, region_or_window, node with
      | Some mv, true, _, `Load (_, addr, size) ->
          sec_comp_access ?want ctx scope llvm_builder blk_tid exp ~store:false
            mv addr ~data:None size
      | Some mv, true, _, `Store (_, addr, data, size) ->
          sec_comp_access ?want ctx scope llvm_builder blk_tid exp ~store:true mv
            addr ~data:(Some data) size
      | _, _, true, `Load (_, addr, size) ->
          storage_access ?want ~is_window ~storage ctx scope llvm_builder
            blk_tid (`Load (addr, size)) exp
      | _, _, true, `Store (_, addr, data, size) ->
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

(* ---- The atomic lane: BAP's lock markers consumed. ----
   The x86 backend brackets every locked memory RMW with
   [intrinsic:x86:lock]/[x86:unlock] calls and marks the implicit case
   (a memory xchg); the fence instructions ride their own intrinsics.
   The bracket is the atomicity fact; the BIL inside names the op. *)

(* The def's own memory node, when its rhs is one load or store. *)
let mem_def (d : def term) :
    [ `Load of var * exp * Size.t | `Store of var * exp * exp * Size.t ]
    option =
  match Def.rhs d with
  | Bil.Load (Bil.Var m, a, _, s) -> Some (`Load (m, a, s))
  | Bil.Store (Bil.Var m, a, x, _, s) -> Some (`Store (m, a, x, s))
  | _ -> None

(* The bracket's per-def plan: [blocks] are the blocks between the lock
   call's continuation and the block whose jmp is the unlock call,
   inclusive.  The one memory store names the family; its shape picks
   the op, the value, and the defs the atomic result binds. *)
let plan_bracket (blocks : blk term list) : (Tid.t * atomic_action) list =
  let defs =
    Base.List.concat_map blocks ~f:(fun b ->
        Term.enum def_t b |> Seq.to_list)
  in
  let def_of_var v =
    Base.List.find defs ~f:(fun d -> Var.equal (Def.lhs d) v)
  in
  (* A side of the store's data names the old cell: an inline load, or
     a var whose bracket def is a load. *)
  let is_load_side = function
    | Bil.Load _ -> true
    | Bil.Var v -> (
      match def_of_var v with
      | Some d -> (
        match Def.rhs d with Bil.Load _ -> true | _ -> false)
      | None -> false)
    | _ -> false
  in
  let rmw_op = function
    | Bil.PLUS -> Some Llvm.AtomicRMWBinOp.Add
    | Bil.MINUS -> Some Llvm.AtomicRMWBinOp.Sub
    | Bil.AND -> Some Llvm.AtomicRMWBinOp.And
    | Bil.OR -> Some Llvm.AtomicRMWBinOp.Or
    | Bil.XOR -> Some Llvm.AtomicRMWBinOp.Xor
    | _ -> None
  in
  let stores =
    Base.List.filter_map defs ~f:(fun d ->
        match mem_def d with
        | Some (`Store _) -> Some d
        | _ -> None)
  in
  let malformed shape =
    failwith
      (Printf.sprintf
         "hike-emit: atomic: a lock-marker bracket holds an unsupported \
          RMW shape (%s)"
         shape)
  in
  match stores with
  | [ store ] ->
    let data = match mem_def store with Some (`Store (_, _, x, _)) -> x | _ -> assert false in
    (* The compare-exchange family: recognized, then refused — the
       LLVM 19 OCaml bindings ship no cmpxchg builder, and no sound
       emission expresses the conditional atomic store without it. *)
    let refused_cmpxchg () =
      failwith
        "hike-emit: atomic: a lock-marker bracket holds a compare-exchange \
         (cmpxchg/cmpxchg8b); the LLVM 19 OCaml bindings ship no cmpxchg \
         builder - refusing the class"
    in
    let cmpxchg8b () =
      match data with
      | Bil.Ite (Bil.Var eq, _, _) -> (
        match def_of_var eq with
        | Some d -> (
          match Def.rhs d with
          | Bil.BinOp (Bil.EQ, _, Bil.Load _)
          | Bil.BinOp (Bil.EQ, Bil.Load _, _) ->
            refused_cmpxchg ()
          | _ -> None)
        | None -> None)
      | _ -> None
    in
    (* xadd: the addend store beside a plus-sum def and its register
       def.  The machine's register result is the OLD cell value; BAP's
       BIL computes the sum into it. *)
    let xadd () =
      match data with
      | Bil.Var v -> (
        let sum =
          Base.List.find_map defs ~f:(fun d ->
              match Def.rhs d with
              | Bil.BinOp (Bil.PLUS, a, b) when is_load_side a || is_load_side b ->
                let side x = if is_load_side x then None else Some x in
                (match (side a, side b) with
                 | Some (Bil.Var w), _ when Var.equal w v -> Some d
                 | _, Some (Bil.Var w) when Var.equal w v -> Some d
                 | _ -> None)
              | _ -> None)
        in
        match sum with
        | Some sum -> (
          match
            Base.List.find_map defs ~f:(fun d ->
                match Def.rhs d with
                | Bil.Var t when Var.equal t (Def.lhs sum) -> Some d
                | _ -> None)
          with
          | Some reg ->
            Some
              [ (Term.tid store, Atomic_rmw (Llvm.AtomicRMWBinOp.Add, data));
                (Term.tid reg, Atomic_old_result) ]
          | None -> malformed "xadd without its register def")
        | None -> None)
      | _ -> None
    in
    (* The compare-exchange: a guarded store beside the compared load. *)
    let cmpxchg () =
      let guard =
        Base.List.find_map blocks ~f:(fun b ->
            Term.enum jmp_t b
            |> Seq.to_list
            |> Base.List.find_map ~f:(fun j ->
                   match Jmp.cond j with
                   | Bil.BinOp (Bil.EQ, Bil.Var _, Bil.Var _) -> Some j
                   | _ -> None))
      in
      let is_compare_load ld =
        match Base.Option.bind ld ~f:mem_def with
        | Some (`Load _) -> true
        | _ -> false
      in
      match guard with
      | Some j -> (
        (* Either side of the compare may be the temp; whichever has a
           bracket def that is a load names the compare-exchange. *)
        match Jmp.cond j with
        | Bil.BinOp (Bil.EQ, Bil.Var x, Bil.Var y)
          when is_compare_load (def_of_var x) || is_compare_load (def_of_var y)
          ->
            refused_cmpxchg ()
        | _ -> None)
      | None -> None
    in
    (* xchg: the swapped register's load beside the addend store. *)
    let xchg () =
      match data with
      | Bil.Var v -> (
        match def_of_var v with
        | Some d -> (
          match Def.rhs d with
          | Bil.Var r -> (
            let reg_load =
              Base.List.find_map defs ~f:(fun dl ->
                  match mem_def dl with
                  | Some (`Load _) when Var.same (Def.lhs dl) r -> Some dl
                  | _ -> None)
            in
            match reg_load with
            | Some dl ->
              Some
                [ (Term.tid dl, Atomic_rmw (Llvm.AtomicRMWBinOp.Xchg, data));
                  (Term.tid store, Atomic_suppressed) ]
            | None -> None)
          | _ -> None)
        | None -> None)
      | _ -> None
    in
    let classified =
      Base.Option.first_some (cmpxchg8b ()) (xadd ())
      |> Base.Option.first_some (cmpxchg ())
      |> Base.Option.first_some (xchg ())
    in
    (match classified with
    | Some plan -> plan
    | None -> (
      (* The plain family: [old op val] stored back — add/sub/inc/dec,
         and/or/xor, and the bit tests (their masks are the same ops). *)
      match data with
      | Bil.BinOp (op, a, b) -> (
        match rmw_op op with
        | Some aop when is_load_side a && not (is_load_side b) ->
          [ (Term.tid store, Atomic_rmw (aop, b)) ]
        | Some aop when is_load_side b && not (is_load_side a) ->
          [ (Term.tid store, Atomic_rmw (aop, a)) ]
        | _ -> malformed "a binop store whose operand is not the old cell")
      | _ -> malformed "unrecognized store data"))
  | [] -> malformed "no memory store"
  | _ -> malformed "more than one memory store"

(* Every lock-marker bracket of the sub, as one per-def plan. *)
let plan_atomics (sub : sub term) : atomic_action Tid.Map.t =
  let blocks = Term.enum blk_t sub |> Seq.to_list in
  let call_target_name j =
    match Jmp.kind j with
    | Call c -> (
      match Call.target c with
      | Direct t -> Some (Tid.name t)
      | Indirect _ -> None)
    | _ -> None
  in
  let succ_tids blk =
    Term.enum jmp_t blk
    |> Seq.concat_map ~f:(fun j ->
           match Jmp.kind j with
           | Goto (Direct t) -> Seq.return t
           | Call c -> (
             match Call.return c with
             | Some l -> Seq.return (label_tid l)
             | None -> Seq.empty)
           | _ -> Seq.empty)
    |> Seq.to_list
  in
  let is_marker name kind =
    Base.Option.exists name ~f:(fun n ->
        Abi.is_lock_marker n && Base.String.is_suffix n ~suffix:kind)
  in
  let brackets =
    Base.List.filter_map blocks ~f:(fun blk ->
        let lock =
          Term.enum jmp_t blk
          |> Seq.find ~f:(fun j ->
                 is_marker (call_target_name j) ":lock")
        in
        Base.Option.map lock ~f:(fun j ->
            match Jmp.kind j with
            | Call c -> (
              match Call.return c with
              | Some l -> (blk, label_tid l)
              | None ->
                failwith
                  "hike-emit: atomic: a lock-marker call has no continuation")
            | _ -> assert false))
  in
  let block_of tid = Base.List.find blocks ~f:(fun b -> Tid.equal (Term.tid b) tid) in
  let plan =
    Base.List.concat_map brackets ~f:(fun (_lk, cont) ->
        let visited = ref Tid.Set.empty in
        let rec walk tid acc =
          if Core.Set.mem !visited tid then acc
          else (
            visited := Core.Set.add !visited tid;
            match block_of tid with
            | None ->
              failwith
                "hike-emit: atomic: a lock-marker bracket names no block"
            | Some blk ->
              let ends =
                Term.enum jmp_t blk
                |> Seq.exists ~f:(fun j ->
                       is_marker (call_target_name j) ":unlock")
              in
              let acc = blk :: acc in
              if ends then acc
              else
                Base.List.fold (succ_tids blk) ~init:acc
                  ~f:(fun acc t -> walk t acc))
        in
        let bracket = List.rev (walk cont []) in
        if
          Base.List.exists bracket ~f:(fun blk ->
              Term.enum jmp_t blk
              |> Seq.exists ~f:(fun j ->
                     is_marker (call_target_name j) ":unlock"))
        then plan_bracket bracket
        else
          failwith
            "hike-emit: atomic: a lock-marker bracket closes with no unlock \
             call")
  in
  plan
  |> Base.List.fold ~init:Tid.Map.empty ~f:(fun m (tid, a) ->
         Core.Map.set m ~key:tid ~data:a)

(* The atomic op's target pointer: the same resolution lanes an
   ordinary access takes. *)
let atomic_ptr ctx scope llvm_builder blk_tid mem addr =
  let component =
    match mem with
    | Bil.Var mv when (
        match Hike_synth.storage_of ctx.synth mv with
        | Some (Hike_synth.Global _) -> true
        | _ -> false) ->
      let index =
        as_integer ctx llvm_builder (create_exp ctx scope llvm_builder blk_tid addr)
      in
      Bil2llvm_memory.component_ptr ctx llvm_builder mv index
    | _ -> None
  in
  match component with
  | Some ptr -> ptr
  | None when is_tls_addr ctx addr ->
    create_tls_ptr ctx scope llvm_builder blk_tid addr
  | None ->
    let a = create_exp ctx scope llvm_builder blk_tid addr in
    match Llvm.int64_of_const a with
    | Some ai ->
      Bil2llvm_memory.const_addr_ptr ctx llvm_builder ai
        ~fallback:(fun () ->
          Llvm.const_inttoptr
            (Llvm.const_int (Llvm.i64_type ctx.llvm_ctx) (Int64.to_int ai))
            ctx.ptr_ty)
    | None ->
      Bil2llvm_section.create_addr_ptr ctx llvm_builder a
      |> fun p ->
      if Llvm.type_of p = ctx.ptr_ty then p
      else Llvm.build_inttoptr p ctx.ptr_ty "" llvm_builder

(* Coerces a value to the atomic op's width. *)
let atomic_width ctx llvm_builder v bits =
  let w = Llvm.integer_bitwidth (Llvm.type_of v) in
  if w = bits then v
  else if w > bits then
    Llvm.build_trunc v (Llvm.integer_type ctx.llvm_ctx bits) "" llvm_builder
  else
    Llvm.build_zext v (Llvm.integer_type ctx.llvm_ctx bits) "" llvm_builder

let create_atomic ctx scope llvm_builder blk_tid (def : def term) action :
    Llvm.llvalue =
  let value exp bits =
    atomic_width ctx llvm_builder
      (create_exp ctx scope llvm_builder blk_tid exp)
      bits
  in
  match (action, Def.rhs def) with
  | Atomic_rmw (op, vexp), Bil.Store (mem, addr, _, _, size) ->
    let bits = Size.in_bits size in
    let v = value vexp bits in
    let ptr = atomic_ptr ctx scope llvm_builder blk_tid mem addr in
    let old =
      Llvm.build_atomicrmw op ptr v Llvm.AtomicOrdering.SequentiallyConsistent
        false "xold" llvm_builder
    in
    scope.atomic_old := Some old;
    v
  | Atomic_rmw (op, vexp), Bil.Load (mem, addr, _, size) ->
    (* The xchg: the swapped register's own load is the op. *)
    let bits = Size.in_bits size in
    let v = value vexp bits in
    let ptr = atomic_ptr ctx scope llvm_builder blk_tid mem addr in
    let old =
      Llvm.build_atomicrmw op ptr v Llvm.AtomicOrdering.SequentiallyConsistent
        false "xold" llvm_builder
    in
    scope.atomic_old := Some old;
    old
  | Atomic_old_result, _ ->
    Base.Option.value_exn
      !(scope.atomic_old)
      ~message:"hike-emit: atomic: the result def precedes its op"
  | Atomic_suppressed, Bil.Store (_, _, data, _, _) ->
    (* The bracket's atomic op performed the write. *)
    create_exp ctx scope llvm_builder blk_tid data
  | _ ->
    failwith
      (Printf.sprintf
         "hike-emit: atomic: the plan and the def's shape disagree at %s"
         (Tid.name (Term.tid def)))

let create_def ctx scope blk_tid llvm_builder sub_tid _fr def =
  let var = Def.lhs def in
  let exp = Def.rhs def in
  let def_tag = find_def_tag def in
  let want = if is_ptr_var var then Some ctx.ptr_ty else None in
  let res =
    match Core.Map.find !(scope.atomic_plan) (Term.tid def) with
    | Some action -> create_atomic ctx scope llvm_builder blk_tid def action
    | None ->
        if Hike_def_slots.def_is_dyn_alloc def then
          create_dynamic_alloc ctx scope llvm_builder blk_tid def exp
        else mem_access ?want ctx scope llvm_builder blk_tid sub_tid def_tag def exp
  in
  insert_local scope blk_tid var res;
  (* An SSA version has one def: its value is valid wherever the def
     dominates, so the binding is sub-wide. *)
  if Var.index var > 0 then bind_ssaval scope var res;
  (* An environment register's def also stores the process-global cell:
     the value must outlive the sub (its lane rides no signature). *)
  if Option.is_some (Hike_synth.env_of ctx.synth var) then
    ignore (Llvm.build_store res (env_global ctx var) llvm_builder)
