(* Emitter expression lane: pure exp emission (no calls, no mem dispatch). *)

open Bap.Std
open Bap.Std.Bil.Types
module Abi = Hike_abi
open Bil2llvm_env
open Bil2llvm_section

let create_binop llvm_builder (op, llvm_val1, llvm_val2) =
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
    match !(ctx.tls_anchor) with
    | Some g -> g
    | None ->
      let g =
        Llvm.declare_global (ctx.i64_ty) "hike_tls_anchor"
          ctx.llvm_module
      in
      Llvm.set_thread_local_mode Llvm.ThreadLocalMode.GeneralDynamic g;
      Llvm.set_initializer (Llvm.const_int (ctx.i64_ty) 0) g;
      ctx.tls_anchor := Some g;
      g
  in
  let tp = ctx.ptr_ty in
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
   remap words that name lifted addresses.  Widths to 64 bits take
   the direct integer path; wider words go through the text form. *)
let create_immediate ctx word =
  let w = Word.bitwidth word in
  let ty = Llvm.integer_type ctx.llvm_ctx w in
  if w <= 64 then
    Llvm.const_of_int64 ty (Word.to_int64_exn word) false
  else
    Llvm.const_int_of_string ty (Word.string_of_value word) 16

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
let fresh_let_var scope (v : Var.t) : Var.t =
  incr scope.let_counter;
  Var.create ~is_virtual:true ~fresh:false
    (Printf.sprintf "hike_let%d" !(scope.let_counter))
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
      match get_ssaval scope v with
      | Some x -> x
      | None -> (
          match get_local scope blk_tid v with
          | Some x -> x
          | None ->
              warn_undef_read ctx scope v blk_tid;
              frozen_undef ctx scope v))
  | Int i -> create_immediate ctx i
  | Cast (cast, i, exp) ->
      let var = create_exp ctx scope llvm_builder blk_tid exp in
      create_cast ctx llvm_builder (cast, i, var)
  | Concat (exp1, exp2) ->
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
      let unique_var = fresh_let_var scope var in
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
      (* The boundary identity is a frozen undef, never poison: poison
         is UB and folds under opt. *)
      let typ = typ_lltype ctx typ in
      Llvm.build_freeze (Llvm.undef typ) "hike_unknown" llvm_builder


(* Named-component routing: the mem var is the component's identity,
   bound to its global and native base; the address evaluates to
   native bits, so the GEP index is the exact native delta. *)
and sec_comp_access ctx scope llvm_builder blk_tid ~(store : bool)
    (mv : var) (addr : exp) ~(data : exp option) (size : int) :
    Llvm.llvalue =
  match Core.Map.find !(ctx.sec_comps) mv with
  | Some (base, own_lo) ->
    let a = create_exp ctx scope llvm_builder blk_tid addr in
    let idx =
      Llvm.build_sub a
        (Llvm.const_of_int64 (ctx.i64_ty) own_lo false)
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

(* A rip-relative def's VALUE is a constant address: the section
   owner's base plus its offset — never the native constant.  Every
   other shape renders through the generic exp path, whose load/store
   arms own the const-address and section routing. *)
and create_rip_relative_addr ctx scope llvm_builder blk_tid exp =
  match exp with
  | Bil.Int w ->
      let v = Word.to_int64_exn w in
      remapped_const ctx ctx.llvm_ctx ctx.llvm_module v
        (ctx.i64_ty)
  | exp -> create_exp ctx scope llvm_builder blk_tid exp

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
and window_mem_access ctx scope llvm_builder blk_tid fr exp ~raw =
  let w_ptr =
    let w = Hike_stack_model.hike_window_var ~word:ctx.abi.Abi.word in
    match get_local scope blk_tid w with
    | Some v -> v
    | None -> Llvm.undef (var_lltype ctx w)
  in
  match find_mem_node exp with
  | Some node ->
      (* The window parameter IS its own base: an access's address
         minus the sub's stack0 is the offset into the window. *)
      storage_access ctx scope llvm_builder blk_tid ~base:w_ptr
        ~index_of:(fun a -> Llvm.build_sub a (frame_stack0 fr) "" llvm_builder)
        node exp
  | None -> raw ()

and region_mem_access ctx scope llvm_builder blk_tid fr mv exp ~raw =
  let stack0 = frame_stack0 fr in
  (* The region alloca's base sits [rel_rlo] above the sub's stack0
     (the region's lowest byte): anchor-normalized minus that offset
     is the byte index inside the alloca. *)
  let region_index llvm_builder rel_rlo a =
    let rel = Llvm.build_sub a stack0 "reg_rel" llvm_builder in
    Llvm.build_sub rel
      (Llvm.const_of_int64 (ctx.i64_ty) rel_rlo false)
      "" llvm_builder
  in
  match Base.List.Assoc.find ~equal:Var.equal fr.regions mv with
  | None -> raw ()
  | Some (base, rel_rlo) -> (
      match find_mem_node exp with
      | Some node ->
          storage_access ctx scope llvm_builder blk_tid ~base
            ~index_of:(fun a -> region_index llvm_builder rel_rlo a) node exp
      | None -> raw ())

(* Routes a region/window mem var to its storage; with no frame
   bound, the raw arm serves the access. *)
and region_window_access ctx scope llvm_builder blk_tid mv exp ~raw =
  match !(scope.cur_frame) with
  | Some fr when Hike_stack_model.is_region_mem mv ->
      region_mem_access ctx scope llvm_builder blk_tid fr mv exp ~raw
  | Some fr when Hike_stack_model.is_window_mem mv ->
      window_mem_access ctx scope llvm_builder blk_tid fr exp ~raw
  | _ -> raw ()
