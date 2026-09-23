(* Emitter expression lane: pure exp emission (no calls, no mem dispatch). *)

open Bap.Std
open Bap.Std.Bil.Types
module Abi = Hike_abi
open Bil2llvm_env
open Bil2llvm_section

(* Coerces binop operands to one type. *)
let coerce_to_same_type llvm_builder op llvm_val1 llvm_val2 =
  let is_integer v =
    match Llvm.classify_type (Llvm.type_of v) with
    | Llvm.TypeKind.Integer -> true
    | _ -> false
  in
  let typ1 = Llvm.type_of llvm_val1 in
  let typ2 = Llvm.type_of llvm_val2 in
  if (not (is_integer llvm_val1)) || not (is_integer llvm_val2) then
    (llvm_val1, llvm_val2)
  else
    let size1 = Llvm.integer_bitwidth typ1 in
    let size2 = Llvm.integer_bitwidth typ2 in
    if size1 = size2 then (llvm_val1, llvm_val2)
    else
      let target_typ = if size1 >= size2 then typ1 else typ2 in
      let build_cast =
        match op with
        | SDIVIDE | SMOD | ARSHIFT | SLT | SLE -> Llvm.build_sext
        | _ -> Llvm.build_zext
      in
      let llvm_val1 =
        if size1 < size2 then build_cast llvm_val1 target_typ "" llvm_builder
        else llvm_val1
      in
      let llvm_val2 =
        if size2 < size1 then build_cast llvm_val2 target_typ "" llvm_builder
        else llvm_val2
      in
      (llvm_val1, llvm_val2)

let create_binop llvm_builder (op, llvm_val1, llvm_val2) =
  let llvm_val1, llvm_val2 =
    coerce_to_same_type llvm_builder op llvm_val1 llvm_val2
  in
  match op with
  | PLUS -> Llvm.build_add llvm_val1 llvm_val2 "" llvm_builder
  | MINUS -> Llvm.build_sub llvm_val1 llvm_val2 "" llvm_builder
  | TIMES -> Llvm.build_mul llvm_val1 llvm_val2 "" llvm_builder
  | DIVIDE -> Llvm.build_udiv llvm_val1 llvm_val2 "" llvm_builder
  | SDIVIDE -> Llvm.build_sdiv llvm_val1 llvm_val2 "" llvm_builder
  | MOD -> Llvm.build_urem llvm_val1 llvm_val2 "" llvm_builder
  | SMOD -> Llvm.build_srem llvm_val1 llvm_val2 "" llvm_builder
  | AND -> Llvm.build_and llvm_val1 llvm_val2 "" llvm_builder
  | OR -> Llvm.build_or llvm_val1 llvm_val2 "" llvm_builder
  | XOR -> Llvm.build_xor llvm_val1 llvm_val2 "" llvm_builder
  | LSHIFT -> Llvm.build_shl llvm_val1 llvm_val2 "" llvm_builder
  | RSHIFT -> Llvm.build_lshr llvm_val1 llvm_val2 "" llvm_builder
  | ARSHIFT -> Llvm.build_ashr llvm_val1 llvm_val2 "" llvm_builder
  | EQ -> Llvm.build_icmp Llvm.Icmp.Eq llvm_val1 llvm_val2 "" llvm_builder
  | NEQ -> Llvm.build_icmp Llvm.Icmp.Ne llvm_val1 llvm_val2 "" llvm_builder
  | LT -> Llvm.build_icmp Llvm.Icmp.Ult llvm_val1 llvm_val2 "" llvm_builder
  | SLT -> Llvm.build_icmp Llvm.Icmp.Slt llvm_val1 llvm_val2 "" llvm_builder
  | LE -> Llvm.build_icmp Llvm.Icmp.Ule llvm_val1 llvm_val2 "" llvm_builder
  | SLE -> Llvm.build_icmp Llvm.Icmp.Sle llvm_val1 llvm_val2 "" llvm_builder

let create_unop llvm_builder (op, llvm_val) =
  match op with
  | NEG -> Llvm.build_neg llvm_val "" llvm_builder
  | NOT -> Llvm.build_not llvm_val "" llvm_builder

let rec exp_size (e : exp) : int =
  match e with
  | Bil.Extract (hi, lo, _) -> max 0 (hi - lo + 1)
  | Bil.Cast (_, i, _) -> i
  | _ -> (
    match Type.infer e with
    | Ok (Type.Imm n) -> n
    | _ -> 0)

let create_concat ctx llvm_builder (llvm_var1, llvm_var2) =
  let llvm_var1_size = Llvm.type_of llvm_var1 |> Llvm.integer_bitwidth in
  let llvm_var2_size = Llvm.type_of llvm_var2 |> Llvm.integer_bitwidth in
  let result_typ =
    Llvm.integer_type ctx.llvm_ctx (llvm_var1_size + llvm_var2_size)
  in
  let llvm_var2_sizeof = Llvm.const_int result_typ llvm_var2_size in
  let zext_var1 = Llvm.build_zext llvm_var1 result_typ "" llvm_builder in
  let shl_var1 = Llvm.build_shl zext_var1 llvm_var2_sizeof "" llvm_builder in
  let zext_var2 = Llvm.build_zext llvm_var2 result_typ "" llvm_builder in
  Llvm.build_or shl_var1 zext_var2 "" llvm_builder

let create_extract ctx llvm_builder (hi, lo, llvm_var) =
  let width = Llvm.integer_bitwidth (Llvm.type_of llvm_var) in
  let result_size = hi - lo + 1 in
  if lo >= width then
    (* Out-of-range extracts yield zero. *)
    Llvm.const_int (Llvm.integer_type ctx.llvm_ctx result_size) 0
  else
    let temp_var =
      Llvm.build_lshr llvm_var
        (Llvm.const_int (Llvm.type_of llvm_var) lo)
        "" llvm_builder
    in
    if result_size >= width then
      (* Wide extracts zero-extend. *)
      Llvm.build_zext temp_var
        (Llvm.integer_type ctx.llvm_ctx result_size) "" llvm_builder
    else
      Llvm.build_trunc temp_var
        (Llvm.integer_type ctx.llvm_ctx result_size) "" llvm_builder

(* True when the address bases on the target's TLS register. *)
let rec is_tls_addr ctx (e : exp) : bool =
  match e with
  | Var v -> Var.same v ctx.abi.Abi.thread_pointer
  | BinOp (_, e1, e2) -> is_tls_addr ctx e1 || is_tls_addr ctx e2
  | UnOp (_, e) -> is_tls_addr ctx e
  | Cast (_, _, e) -> is_tls_addr ctx e
  | Extract (_, _, e) -> is_tls_addr ctx e
  | Concat (e1, e2) -> is_tls_addr ctx e1 || is_tls_addr ctx e2
  | Let (_, e1, e2) -> is_tls_addr ctx e1 || is_tls_addr ctx e2
  | _ -> false

(* A thread_local global's address is not a constant;
   llvm.threadlocal.address is its accessor. *)
let tls_anchor_addr ctx llvm_builder =
  let g =
    Llvm.declare_global (Llvm.i64_type ctx.llvm_ctx) "hike_tls_anchor"
      ctx.llvm_module
  in
  Llvm.set_thread_local_mode Llvm.ThreadLocalMode.GeneralDynamic g;
  Llvm.set_initializer (Llvm.const_int (Llvm.i64_type ctx.llvm_ctx) 0) g;
  let tp = Llvm.pointer_type ctx.llvm_ctx in
  let fty = Llvm.function_type tp [| tp |] in
  let f = Llvm.declare_function "llvm.threadlocal.address" fty ctx.llvm_module in
  Llvm.build_call fty f [| g |] "tls_anchor" llvm_builder

let create_load ctx llvm_builder (addr, size) =
  match Llvm.int64_of_const addr with
  | Some v ->
      const_addr_load ctx llvm_builder (Word.of_int64 ~width:64 v) size
        ~fallback:(fun () ->
          let ptr = create_addr_ptr ctx llvm_builder addr in
          Llvm.build_load (Llvm.integer_type ctx.llvm_ctx size) ptr ""
            llvm_builder)
  | _ ->
      (* Non-constant addresses materialize through [create_addr_ptr]. *)
      let addr = create_addr_ptr ctx llvm_builder addr in
      Llvm.build_load (Llvm.integer_type ctx.llvm_ctx size) addr ""
        llvm_builder

let create_store ctx llvm_builder (llvm_var, addr) =
  match Llvm.int64_of_const addr with
  | Some v ->
      const_addr_store ctx llvm_builder (Word.of_int64 ~width:64 v)
        ~data:(fun () -> llvm_var)
        ~fallback:(fun () ->
          let addr = create_addr_ptr ctx llvm_builder addr in
          let _ : Llvm.llvalue = Llvm.build_store llvm_var addr llvm_builder in
          llvm_var)
  | _ ->
      let addr = create_addr_ptr ctx llvm_builder addr in
      let _ : Llvm.llvalue = Llvm.build_store llvm_var addr llvm_builder in
      llvm_var

let create_cast ctx llvm_builder (cast, i, llvm_val) =
  let width = Llvm.integer_bitwidth (Llvm.type_of llvm_val) in
  let target = Llvm.integer_type ctx.llvm_ctx i in
  let extend cast =
    match cast with SIGNED -> Llvm.build_sext | _ -> Llvm.build_zext
  in
  let coerce cast v =
    if i > width then extend cast v target "" llvm_builder
    else if i < width then Llvm.build_trunc v target "" llvm_builder
    else v
  in
  match cast with
  | UNSIGNED -> coerce UNSIGNED llvm_val
  | SIGNED -> coerce SIGNED llvm_val
  | LOW -> coerce UNSIGNED llvm_val
  | HIGH ->
      let shift = max 0 (width - i) in
      let shifted =
        if shift > 0 then
          Llvm.build_lshr llvm_val
            (Llvm.const_int (Llvm.type_of llvm_val) shift) "" llvm_builder
        else llvm_val
      in
      coerce UNSIGNED shifted

(* Immediates keep their native bits; only the section initializers
   remap words that name lifted addresses. *)
let create_immidiate ctx word =
  Llvm.const_int_of_string
    (Llvm.integer_type ctx.llvm_ctx (Word.bitwidth word))
    (Word.string_of_value word)
    16

(* The one memory node of an exp (a def's rhs holds at most one). *)
type mem_node = [ `Load of exp * Size.t | `Store of exp * exp * Size.t ]

let find_mem_node (exp : exp) : mem_node option =
  match Hike_stack_model.mem_node_of exp with
  | Some (`Load (_, addr, size)) -> Some (`Load (addr, size))
  | Some (`Store (_, addr, data, size)) -> Some (`Store (addr, data, size))
  | None -> None

let marker_name = "hike_acc"

let marker_of_size size =
  Var.create ~is_virtual:true ~fresh:false marker_name
    (Type.Imm (Size.in_bits size))

(* The Let-binder's evaluation temp: a fresh identity with a name the
   lifted vocabulary never uses, so the substitution cannot capture. *)
let let_counter = ref 0

let fresh_let_var (v : Var.t) : Var.t =
  incr let_counter;
  Var.create ~is_virtual:true ~fresh:false
    (Printf.sprintf "hike_let%d" !let_counter)
    (Var.typ v)

(* Maps only the mem node matching (addr, size) to a var, preserving
   the enclosing structure. *)
let rewrite_mem_node exp addr size marker =
  let v =
    object
      inherit Exp.mapper
      method! map_load ~mem ~addr:a e s =
        if Exp.equal a addr && Size.equal s size then Bil.Var marker
        else Bil.Load (mem, a, e, s)
      method! map_store ~mem ~addr:a ~exp:x e s =
        if Exp.equal a addr && Size.equal s size then Bil.Var marker
        else Bil.Store (mem, a, x, e, s)
    end
  in
  v#map_exp exp

let rec create_exp ctx scope llvm_builder blk_tid exp =
  match exp with
  | BinOp (op, e1, e2) ->
      let var1 = create_exp ctx scope llvm_builder blk_tid e1 in
      let var2 = create_exp ctx scope llvm_builder blk_tid e2 in
      create_binop llvm_builder (op, var1, var2)
  | UnOp (op, e) ->
      let var = create_exp ctx scope llvm_builder blk_tid e in
      create_unop llvm_builder (op, var)
  | Var v -> (
      (* Width-family fallback, else undef. *)
      match get_local scope blk_tid v with
      | Some x -> x
      | None ->
          let want_w =
            match Var.typ v with Type.Imm w -> w | _ -> Hike_abi.word_bits ctx.abi
          in
          match probe_local_family scope blk_tid v ~want_w with
          | Some (val_at_w, bound_w) ->
              let want_ty = Llvm.integer_type ctx.llvm_ctx want_w in
              if bound_w = want_w then val_at_w
              else if bound_w > want_w then
                Llvm.build_trunc val_at_w want_ty "" llvm_builder
              else
                Llvm.build_zext val_at_w want_ty "" llvm_builder
          | None ->
              warn_undef_read ctx scope v blk_tid;
              frozen_undef ctx scope v)
  | Int i -> create_immidiate ctx i
  | Cast (cast, i, exp) ->
      let var = create_exp ctx scope llvm_builder blk_tid exp in
      create_cast ctx llvm_builder (cast, i, var)
  | Concat (exp1, exp2) ->
      let s1 = exp_size exp1 in
      let s2 = exp_size exp2 in
      if s1 = 0 then create_exp ctx scope llvm_builder blk_tid exp2
      else if s2 = 0 then create_exp ctx scope llvm_builder blk_tid exp1
      else
        let llvm_var1 = create_exp ctx scope llvm_builder blk_tid exp1 in
        let llvm_var2 = create_exp ctx scope llvm_builder blk_tid exp2 in
        create_concat ctx llvm_builder (llvm_var1, llvm_var2)
  | Extract (hi, lo, exp) ->
      let llvm_var = create_exp ctx scope llvm_builder blk_tid exp in
      create_extract ctx llvm_builder (hi, lo, llvm_var)
  (* Region/window and section-component mem vars route to their
     storage; everything else emits through the generic memory path. *)
  | Store (Bil.Var mv, addr, data, _, _)
    when Hike_stack_model.is_region_mem mv
         || Hike_stack_model.is_window_mem mv ->
      region_window_access ctx scope llvm_builder blk_tid mv exp
        ~raw:(fun () ->
          let addr = create_exp ctx scope llvm_builder blk_tid addr in
          let data = create_exp ctx scope llvm_builder blk_tid data in
          create_store ctx llvm_builder (data, addr))
  | Store (Bil.Var mv, addr, data, _, s)
    when Hike_stack_model.is_sec_comp_mem mv ->
      sec_comp_access ctx scope llvm_builder blk_tid ~store:true mv addr
        ~data:(Some data) (Size.in_bits s)
  | Store (_, addr, data, _, _) when is_tls_addr ctx addr ->
      let ptr = tls_anchor_addr ctx llvm_builder in
      let data = create_exp ctx scope llvm_builder blk_tid data in
      Llvm.build_store data ptr llvm_builder
  | Store (_, addr, data, _, _) ->
      let addr = create_exp ctx scope llvm_builder blk_tid addr in
      let data = create_exp ctx scope llvm_builder blk_tid data in
      create_store ctx llvm_builder (data, addr)
  | Load (Bil.Var mv, addr, _, size)
    when Hike_stack_model.is_region_mem mv
         || Hike_stack_model.is_window_mem mv ->
      region_window_access ctx scope llvm_builder blk_tid mv exp
        ~raw:(fun () ->
          let addr = create_exp ctx scope llvm_builder blk_tid addr in
          create_load ctx llvm_builder (addr, Size.in_bits size))
  | Load ((Bil.Var mv), addr, _, size)
    when Hike_stack_model.is_sec_comp_mem mv ->
      sec_comp_access ctx scope llvm_builder blk_tid ~store:false mv addr
        ~data:None (Size.in_bits size)
  | Load (_, addr, _, size) when is_tls_addr ctx addr ->
      let ptr = tls_anchor_addr ctx llvm_builder in
      Llvm.build_load
        (Llvm.integer_type ctx.llvm_ctx (Size.in_bits size)) ptr
        "" llvm_builder
  | Load (_, addr, _, size) ->
      let addr = create_exp ctx scope llvm_builder blk_tid addr in
      create_load ctx llvm_builder (addr, Size.in_bits size)
  | Let (var, exp, body) ->
      let unique_var = fresh_let_var var in
      let v = create_exp ctx scope llvm_builder blk_tid exp in
      insert_local scope blk_tid unique_var v;
      let body = Exp.substitute (Var var) (Var unique_var) body in
      create_exp ctx scope llvm_builder blk_tid body
  | Ite (cond, true_exp, false_exp) ->
      let cond = create_exp ctx scope llvm_builder blk_tid cond in
      let true_exp = create_exp ctx scope llvm_builder blk_tid true_exp in
      let false_exp = create_exp ctx scope llvm_builder blk_tid false_exp in
      Llvm.build_select cond true_exp false_exp "" llvm_builder
  | Unknown (_, typ) ->
      let typ = typ_lltype ctx typ in
      Llvm.poison typ


(* Named-component routing: the mem var is the component's identity,
   bound to its global and native base; the address evaluates to
   native bits, so the GEP index is the exact native delta. *)
and sec_comp_access ctx scope llvm_builder blk_tid ~(store : bool)
    (mv : var) (addr : exp) ~(data : exp option) (size : int) :
    Llvm.llvalue =
  match Base.List.Assoc.find ~equal:Var.equal !(ctx.sec_comps) mv with
  | Some (base, own_lo) ->
    let a = create_exp ctx scope llvm_builder blk_tid addr in
    let idx =
      Llvm.build_sub a
        (Llvm.const_of_int64 (Llvm.i64_type ctx.llvm_ctx) own_lo false)
        "" llvm_builder
    in
    let p =
      Llvm.build_gep (Llvm.i8_type ctx.llvm_ctx) base [| idx |] ""
        llvm_builder
    in
    if store then
      (match data with
       | Some d ->
         let v = create_exp ctx scope llvm_builder blk_tid d in
         let _ : Llvm.llvalue = Llvm.build_store v p llvm_builder in
         v
       | None -> assert false)
    else
      Llvm.build_load (Llvm.integer_type ctx.llvm_ctx size) p ""
        llvm_builder
  | None ->
    (* Unknown component: the generic memory path, unremapped. *)
    if store then
      (match data with
       | Some d ->
         let a = create_exp ctx scope llvm_builder blk_tid addr in
         let v = create_exp ctx scope llvm_builder blk_tid d in
         create_store ctx llvm_builder (v, a)
       | None -> assert false)
    else
      let a = create_exp ctx scope llvm_builder blk_tid addr in
      create_load ctx llvm_builder (a, size)

and create_rip_relative_addr ctx scope llvm_builder blk_tid exp =
  match exp with
  | Bil.Int w ->
      let v = Word.to_int64_exn w in
      Base.Option.value (remap_native_addr ctx ctx.llvm_ctx ctx.llvm_module v)
        ~default:(Llvm.const_of_int64 (Llvm.i64_type ctx.llvm_ctx) v false)
  | Store (Bil.Var mv, addr, data, _, s)
    when Hike_stack_model.is_sec_comp_mem mv ->
      sec_comp_access ctx scope llvm_builder blk_tid ~store:true mv addr
        ~data:(Some data) (Size.in_bits s)
  | Load (Bil.Var mv, addr, _, s)
    when Hike_stack_model.is_sec_comp_mem mv ->
      sec_comp_access ctx scope llvm_builder blk_tid ~store:false mv addr
        ~data:None (Size.in_bits s)
  | Store (_, addr, data, _, _) ->
      let addr = create_exp ctx scope llvm_builder blk_tid addr in
      (match Llvm.int64_of_const addr with
       | Some i64 ->
           let addr_w = Word.of_int64 ~width:64 i64 in
           const_addr_store ctx llvm_builder addr_w
             ~data:(fun () -> create_exp ctx scope llvm_builder blk_tid data)
             ~fallback:(fun () ->
               let base = resolve_addr ctx llvm_builder addr_w in
               let data = create_exp ctx scope llvm_builder blk_tid data in
               let _ : Llvm.llvalue =
                 Llvm.build_store data base llvm_builder in
               data)
       | None ->
           let data = create_exp ctx scope llvm_builder blk_tid data in
           create_store ctx llvm_builder (data, addr))
  | Load (_, addr, _, size) ->
      let addr = create_exp ctx scope llvm_builder blk_tid addr in
      (match Llvm.int64_of_const addr with
       | Some i64 ->
           let addr_w = Word.of_int64 ~width:64 i64 in
           const_addr_load ctx llvm_builder addr_w (Size.in_bits size)
             ~fallback:(fun () ->
               section_load ctx llvm_builder ctx.llvm_ctx addr_w i64
                 (Size.in_bits size))
       | None ->
           create_load ctx llvm_builder (addr, Size.in_bits size))
  | Cast (cast, i, (Load _ as load)) ->
      (* RIP-relative widening loads. *)
      let v = create_rip_relative_addr ctx scope llvm_builder blk_tid load in
      create_cast ctx llvm_builder (cast, i, v)
  | _ -> create_exp ctx scope llvm_builder blk_tid exp

and emit_with_marker ctx scope llvm_builder blk_tid marker ~emit ~rewrite =
  let v = emit () in
  insert_local scope blk_tid marker v;
  create_exp ctx scope llvm_builder blk_tid (rewrite marker)

(* The fission access: GEP the storage at the access's index, emit
   the load or store, and bind the marker the mem node carries
   forward.  The index arithmetic is the caller's — the window's
   (a − stack0) and the region's (a − stack0 − rel_rlo) are the two
   spellings of "access offset relative to the storage base". *)
and storage_access ctx scope llvm_builder blk_tid ~(base : Llvm.llvalue)
    ~(index_of : Llvm.llvalue -> Llvm.llvalue) node (exp : exp) :
    Llvm.llvalue =
  let rewrite addr size marker = rewrite_mem_node exp addr size marker in
  match node with
  | `Load (addr, size) ->
      let marker = marker_of_size size in
      let p =
        Llvm.build_gep (Llvm.i8_type ctx.llvm_ctx) base
          [| index_of (create_exp ctx scope llvm_builder blk_tid addr) |]
          "" llvm_builder
      in
      let emit () =
        Llvm.build_load
          (Llvm.integer_type ctx.llvm_ctx (Size.in_bits size))
          p "" llvm_builder
      in
      emit_with_marker ctx scope llvm_builder blk_tid marker ~emit
        ~rewrite:(rewrite addr size)
  | `Store (addr, data, size) ->
      let marker = marker_of_size size in
      let p =
        Llvm.build_gep (Llvm.i8_type ctx.llvm_ctx) base
          [| index_of (create_exp ctx scope llvm_builder blk_tid addr) |]
          "" llvm_builder
      in
      let emit () =
        let d = create_exp ctx scope llvm_builder blk_tid data in
        let _ : Llvm.llvalue = Llvm.build_store d p llvm_builder in
        d
      in
      emit_with_marker ctx scope llvm_builder blk_tid marker ~emit
        ~rewrite:(rewrite addr size)

(* Region accesses GEP the region alloca at (access offset − region
   base), both relative to the SP anchor.  Window accesses normalize
   the same way against the hike_window parameter — a pointer into the
   caller's residue. *)
and window_mem_access ctx scope llvm_builder blk_tid fr mv exp =
  match Hike_stack_model.is_window_mem mv with
  | false -> create_exp ctx scope llvm_builder blk_tid exp
  | true -> (
      let w_ptr =
        let w = Hike_stack_model.hike_window_var ~word:ctx.abi.Abi.word in
        match get_local scope blk_tid w with
        | Some v -> v
        | None -> Llvm.undef (var_lltype ctx w)
      in
      match find_mem_node exp with
      | Some node ->
          storage_access ctx scope llvm_builder blk_tid ~base:w_ptr
            ~index_of:(fun a ->
                Llvm.build_sub a (frame_stack0 fr) "" llvm_builder)
            node exp
      | None -> create_exp ctx scope llvm_builder blk_tid exp)

and region_mem_access ctx scope llvm_builder blk_tid fr mv exp =
  let stack0 = frame_stack0 fr in
  let region_index llvm_builder rel_rlo a =
    let rel = Llvm.build_sub a stack0 "reg_rel" llvm_builder in
    Llvm.build_sub rel
      (Llvm.const_of_int64 (Llvm.i64_type ctx.llvm_ctx) rel_rlo false)
      "" llvm_builder
  in
  match Base.List.Assoc.find ~equal:Var.equal fr.regions mv with
  | None -> create_exp ctx scope llvm_builder blk_tid exp
  | Some (base, rel_rlo) -> (
      match find_mem_node exp with
      | Some node ->
          storage_access ctx scope llvm_builder blk_tid ~base
            ~index_of:(fun a -> region_index llvm_builder rel_rlo a) node exp
      | None -> create_exp ctx scope llvm_builder blk_tid exp)

(* Routes a region/window mem var to its storage; with no frame
   bound, the raw arm serves the access. *)
and region_window_access ctx scope llvm_builder blk_tid mv exp ~raw =
  match !(scope.cur_frame) with
  | Some fr when Hike_stack_model.is_region_mem mv ->
      region_mem_access ctx scope llvm_builder blk_tid fr mv exp
  | Some fr when Hike_stack_model.is_window_mem mv ->
      window_mem_access ctx scope llvm_builder blk_tid fr mv exp
  | _ -> raw ()
