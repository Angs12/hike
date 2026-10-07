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

(* A bracket is one decoded instruction and therefore one memory cell.
   Capture its old/new values once, including the BIL flag calculations. *)
let plan_bracket (blocks : blk term list) : (Tid.t * atomic_action) list =
  let defs = Base.List.concat_map blocks ~f:(fun b ->
      Term.enum def_t b |> Seq.to_list) in
  let malformed shape =
    failwith ("hike-emit: atomic: unsupported lock bracket: " ^ shape) in
  let stores = Base.List.filter_map defs ~f:(fun d ->
      match Def.rhs d with
      | Bil.Store (mem, addr, data, _, size) -> Some (d, mem, addr, data, size)
      | _ -> None) in
  match stores with
  | [ (store, mem, addr, data, size) ] ->
    let indexed = Base.List.mapi defs ~f:(fun i d -> (i, d)) in
    let store_index = Base.List.find_map_exn indexed ~f:(fun (i, d) ->
        if Tid.equal (Term.tid d) (Term.tid store) then Some i else None) in
    let rec root_at limit = function
      | Bil.Var v as e -> (
        let definition = Base.List.filter indexed ~f:(fun (i, d) ->
            i < limit && Var.equal (Def.lhs d) v) |> Base.List.last in
        match definition with
        | Some (i, d) -> root_at i (Def.rhs d)
        | None -> e)
      | e -> e in
    let root = root_at store_index in
    let load_at limit e = match root_at limit e with Bil.Load _ -> true | _ -> false in
    let load = load_at store_index in
    let compare limit e =
      let difference e = match root_at limit e with
        | Bil.BinOp (Bil.MINUS, expected, old) when load_at limit old -> Some expected
        | _ -> None in
      match root_at limit e with
      | Bil.BinOp (Bil.EQ, a, b) when load_at limit a -> Some b
      | Bil.BinOp (Bil.EQ, a, b) when load_at limit b -> Some a
      | Bil.BinOp (Bil.EQ, Bil.Int zero, e) when Word.is_zero zero -> difference e
      | Bil.BinOp (Bil.EQ, e, Bil.Int zero) when Word.is_zero zero -> difference e
      | _ -> None in
    let prefixes = snd (Base.List.fold blocks ~init:(0, []) ~f:(fun (n, acc) b ->
        let n = n + Term.length def_t b in
        n, (Term.tid b, n) :: acc)) in
    let cas = match root data with
      | Bil.Ite (condition, desired, old) when load old ->
        Base.Option.map (compare store_index condition) ~f:(fun expected ->
            Compare_exchange (expected, desired))
      | _ ->
        Base.List.find_map blocks ~f:(fun b ->
            let limit = Base.List.Assoc.find_exn prefixes ~equal:Tid.equal (Term.tid b) in
            Term.enum jmp_t b |> Seq.find_map ~f:(fun j ->
                Base.Option.map (compare limit (Jmp.cond j)) ~f:(fun expected ->
                    Compare_exchange (expected, data)))) in
    let kind = match cas with
      | Some kind -> kind
      | None -> (
        let op = function
          | Bil.PLUS -> Some Llvm.AtomicRMWBinOp.Add
          | Bil.MINUS -> Some Llvm.AtomicRMWBinOp.Sub
          | Bil.AND -> Some Llvm.AtomicRMWBinOp.And
          | Bil.OR -> Some Llvm.AtomicRMWBinOp.Or
          | Bil.XOR -> Some Llvm.AtomicRMWBinOp.Xor
          | _ -> None in
        match root data with
        | Bil.BinOp (o, a, b) when load a -> (
          match op o with Some o -> Rmw (o, b) | None -> malformed "RMW operator")
        | Bil.BinOp ((Bil.PLUS | Bil.AND | Bil.OR | Bil.XOR as o), a, b)
          when load b ->
          Rmw (Base.Option.value_exn (op o), a)
        | Bil.UnOp (Bil.NOT, a) when load a ->
          Rmw (Llvm.AtomicRMWBinOp.Xor,
               Bil.Int (Word.ones (Size.in_bits size)))
        | Bil.Load _ ->
          Rmw (Llvm.AtomicRMWBinOp.Or, Bil.Int (Word.zero (Size.in_bits size)))
        | Bil.Var _ | Bil.Cast _ | Bil.Int _ ->
          Rmw (Llvm.AtomicRMWBinOp.Xchg, data)
        | _ -> malformed "store value") in
    let old_var = Var.create "atomic_old" (Type.Imm (Size.in_bits size)) in
    let new_var = Var.create "atomic_new" (Type.Imm (Size.in_bits size)) in
    let has_load e =
      (object inherit [bool] Exp.visitor
         method! enter_load ~mem:_ ~addr:_ _ _ _ = true
       end)#visit_exp e false in
    let rewrite ~after e =
      (object inherit Exp.mapper
         method! map_load ~mem:_ ~addr:_ _ _ =
           Bil.Var (if after then new_var else old_var)
       end)#map_exp e in
    let any_read = Base.List.exists defs ~f:(fun d -> has_load (Def.rhs d)) in
    let started = ref false in
    let plan = Base.List.filter_mapi defs ~f:(fun i d ->
        let rhs = if Tid.equal (Term.tid d) (Term.tid store) then data else Def.rhs d in
        let reads = has_load rhs in
        if (reads || (not any_read && Tid.equal (Term.tid d) (Term.tid store)))
           && not !started then begin
          started := true;
          Some (Term.tid d, Atomic_begin {
              kind; mem; addr; size; old_var; new_var; rhs = rewrite ~after:false rhs })
        end else if reads || Tid.equal (Term.tid d) (Term.tid store) then
          Some (Term.tid d, Atomic_value (rewrite ~after:(i > store_index) rhs))
        else None) in
    if not !started then malformed "no old-cell read";
    plan
  | [] -> malformed "no memory store"
  | _ -> malformed "multiple memory stores"

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
  let covered = ref Tid.Set.empty in
  let plan =
    Base.List.concat_map brackets ~f:(fun (_lk, cont) ->
        let visited = ref Tid.Set.empty in
        let rec walk active tid acc =
          if Core.Set.mem active tid then
            failwith "hike-emit: atomic: cyclic lock-marker bracket"
          else if Core.Set.mem !visited tid then acc
          else (
            if Core.Set.mem !covered tid then
              failwith "hike-emit: atomic: overlapping lock-marker brackets";
            visited := Core.Set.add !visited tid;
            let active = Core.Set.add active tid in
            match block_of tid with
            | None ->
              failwith
                "hike-emit: atomic: a lock-marker bracket names no block"
            | Some blk ->
              if Term.enum jmp_t blk |> Seq.exists ~f:(fun j ->
                  is_marker (call_target_name j) ":lock") then
                failwith "hike-emit: atomic: nested lock-marker bracket";
              let ends =
                Term.enum jmp_t blk
                |> Seq.exists ~f:(fun j ->
                       is_marker (call_target_name j) ":unlock")
              in
              let acc = blk :: acc in
              if ends then acc
              else match succ_tids blk with
                | [] -> failwith "hike-emit: atomic: lock-marker path has no unlock"
                | successors ->
                  Base.List.fold successors ~init:acc
                    ~f:(fun acc t -> walk active t acc))
        in
        let bracket = List.rev (walk Tid.Set.empty cont []) in
        covered := Core.Set.union !covered !visited;
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
  Base.List.iter blocks ~f:(fun blk ->
      if Term.enum jmp_t blk |> Seq.exists ~f:(fun j ->
          is_marker (call_target_name j) ":unlock")
         && not (Core.Set.mem !covered (Term.tid blk)) then
        failwith "hike-emit: atomic: unlock-marker has no lock bracket");
  plan
  |> Base.List.fold ~init:Tid.Map.empty ~f:(fun m (tid, a) ->
         Core.Map.set m ~key:tid ~data:a)

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
        as_integer ctx llvm_builder (create_exp ctx scope llvm_builder blk_tid addr)
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
   anything else materializes and casts. *)
and raw_addr_ptr ctx llvm_builder a =
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

let create_atomic ctx scope llvm_builder blk_tid action : Llvm.llvalue =
  match action with
  | Atomic_value rhs -> create_exp ctx scope llvm_builder blk_tid rhs
  | Atomic_begin { kind; mem; addr; size; old_var; new_var; rhs } ->
    let bits = Size.in_bits size in
    let value exp = atomic_width ctx llvm_builder
        (create_exp ctx scope llvm_builder blk_tid exp) bits in
    let ptr = atomic_ptr ctx scope llvm_builder blk_tid mem addr in
    let old, fresh = match kind with
      | Rmw (op, operand) ->
        let v = value operand in
        let old = Llvm.build_atomicrmw op ptr v
            Llvm.AtomicOrdering.SequentiallyConsistent false "xold" llvm_builder in
        let fresh = match op with
          | Llvm.AtomicRMWBinOp.Xchg -> v
          | Add -> Llvm.build_add old v "" llvm_builder
          | Sub -> Llvm.build_sub old v "" llvm_builder
          | And -> Llvm.build_and old v "" llvm_builder
          | Or -> Llvm.build_or old v "" llvm_builder
          | Xor -> Llvm.build_xor old v "" llvm_builder
          | _ -> assert false in
        old, fresh
      | Compare_exchange (expected, desired) ->
        let expected = value expected and desired = value desired in
        let result = Bil2llvm_atomic.cmpxchg ptr expected desired llvm_builder in
        let old = Llvm.build_extractvalue result 0 "xold" llvm_builder in
        let success = Llvm.build_extractvalue result 1 "xsuccess" llvm_builder in
        old, Llvm.build_select success desired old "" llvm_builder in
    Base.List.iter [ old_var, old; new_var, fresh ] ~f:(fun (var, v) ->
        insert_local scope blk_tid var v;
        bind_ssaval scope var v);
    create_exp ctx scope llvm_builder blk_tid rhs

let create_def ctx scope blk_tid llvm_builder sub_tid _fr def =
  let var = Def.lhs def in
  let exp = Def.rhs def in
  let def_tag = find_def_tag def in
  let want = if is_ptr_var var then Some ctx.ptr_ty else None in
  let res =
    match Core.Map.find !(scope.atomic_plan) (Term.tid def) with
    | Some action -> create_atomic ctx scope llvm_builder blk_tid action
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
