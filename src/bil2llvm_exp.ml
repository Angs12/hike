(* Emitter expression lane: pure exp emission (no calls, no mem dispatch). *)

open Bap.Std
open Bap.Std.Bil.Types
module Abi = Hike_abi
open Bil2llvm_env
open Bil2llvm_ptr
open Bil2llvm_section

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
  (* A pointer coerces through its integer form; the caller re-types it
     at a pointer use. *)
  let llvm_val =
    if Llvm.classify_type (Llvm.type_of llvm_val) = Llvm.TypeKind.Pointer
    then
      Llvm.build_ptrtoint llvm_val
        (Llvm.integer_type ctx.llvm_ctx ctx.addr_bits)
        "" llvm_builder
    else llvm_val
  in
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

(* A window value is a model address; when it escapes into i64 memory
   (a store) or a numeric lane, materialize the real address — the
   caller-window pointer plus the entry-relative offset.  This is the
   ONE as_int boundary. *)
let is_window_exp scope (e : exp) : bool =
  match e with
  | Bil.Var w -> Core.Set.mem !(scope.window_vars) w
  | _ -> false

(* ---- The expression evaluator.  The pointer semantics live in
   [Bil2llvm_ptr]; this lane evaluates exps and asks it for values. ---- *)

(* The entry-line offset of an expression, when structurally known: an
   arithmetic chain from the entry line / a slot.  A load, parameter,
   phi, or cast has none. *)
let rec static_offset scope (exp : exp) : int64 option =
  match exp with
  | Bil.Int w -> ( match Word.to_int64 w with Ok x -> Some x | Error _ -> None)
  | Bil.Var v -> (
      match get_ptr_offset scope v with
      | Some ll -> Llvm.int64_of_const ll
      | None -> None)
  | Bil.BinOp (Bil.PLUS, a, b) ->
      Base.Option.bind (static_offset scope a) ~f:(fun x ->
          Base.Option.map (static_offset scope b) ~f:(Stdlib.Int64.add x))
  | Bil.BinOp (Bil.MINUS, a, b) ->
      Base.Option.bind (static_offset scope a) ~f:(fun x ->
          Base.Option.map (static_offset scope b) ~f:(Stdlib.Int64.sub x))
  | _ -> None

let rec create_offset ctx scope llvm_builder blk_tid exp :
    Llvm.llvalue option =
  let addr_ty = Llvm.integer_type ctx.llvm_ctx ctx.addr_bits in
  let coerce v =
    let b = Llvm.integer_bitwidth (Llvm.type_of v) in
    if b = ctx.addr_bits then v
    else if b > ctx.addr_bits then
      Llvm.build_trunc v addr_ty "" llvm_builder
    else Llvm.build_sext v addr_ty "" llvm_builder
  in
  match exp with
  | Bil.Int w -> Some (coerce (create_immediate ctx w))
  | Bil.Var v -> (
      match get_ptr_offset scope v with
      | Some off -> Some off
      | None ->
          if is_ptr_var v then None
          else
            let x = create_exp ctx scope llvm_builder blk_tid exp in
            if is_ptr_value x then None else Some x)
  | BinOp (op, e1, e2) -> (
      match
        ( create_offset ctx scope llvm_builder blk_tid e1,
          create_offset ctx scope llvm_builder blk_tid e2 )
      with
      | Some a, Some b ->
          Some (create_binop llvm_builder (op, coerce a, coerce b))
      | _ -> None)
  | UnOp (op, e) ->
      Base.Option.map (create_offset ctx scope llvm_builder blk_tid e)
        ~f:(fun v -> create_unop llvm_builder (op, v))
  | Ite (cond, t, f) -> (
      match
        ( create_offset ctx scope llvm_builder blk_tid t,
          create_offset ctx scope llvm_builder blk_tid f )
      with
      | Some tv, Some fv ->
          let c = create_exp ctx scope llvm_builder blk_tid cond in
          Some (select ctx llvm_builder c tv fv)
      | _ -> None)
  | Load _ | Store _ | Unknown _ | Cast _ | Extract _ | Concat _ | Let _ ->
      None

and create_exp ?want ctx scope llvm_builder blk_tid exp =
  match exp with
  | BinOp (op, e1, e2) ->
      let v1 = create_exp ctx scope llvm_builder blk_tid e1 in
      let v2 = create_exp ctx scope llvm_builder blk_tid e2 in
      let null e = match e with Bil.Int w -> Word.is_zero w | _ -> false in
      binop ctx llvm_builder ~null1:(null e1) ~null2:(null e2) (op, v1, v2)
  | UnOp (op, e) ->
      let v =
        as_integer ctx llvm_builder
          (create_exp ctx scope llvm_builder blk_tid e)
      in
      create_unop llvm_builder (op, v)
  | Var v -> (
      match get_ssaval scope v with
      | Some x -> x
      | None -> (
          match get_local scope blk_tid v with
          | Some x -> x
          | None -> (
              match WVarMap.find_opt (wvar_of v) !(scope.sec_comp_ptrs) with
              | Some x -> x
              | None ->
                  warn_undef_read ctx scope v blk_tid;
                  frozen_undef ctx scope v)))
  | Int i -> create_immediate ctx i
  | Cast (cast, i, e) ->
      let v = create_exp ctx scope llvm_builder blk_tid e in
      create_cast ctx llvm_builder (cast, i, v)
  | Concat (e1, e2) ->
      let v1 =
        as_integer ctx llvm_builder
          (create_exp ctx scope llvm_builder blk_tid e1)
      in
      let v2 =
        as_integer ctx llvm_builder
          (create_exp ctx scope llvm_builder blk_tid e2)
      in
      create_concat ctx llvm_builder (v1, v2)
  | Extract (hi, lo, e) ->
      let v =
        as_integer ctx llvm_builder
          (create_exp ctx scope llvm_builder blk_tid e)
      in
      create_extract ctx llvm_builder (hi, lo, v)
  | Store (_, addr, data, _, _) when is_tls_addr ctx addr ->
      let ptr = tls_anchor_addr ctx llvm_builder in
      let d = create_exp ctx scope llvm_builder blk_tid data in
      let _ : Llvm.llvalue = Llvm.build_store d ptr llvm_builder in
      d
  | Load (_, addr, _, size) when is_tls_addr ctx addr ->
      let ptr = tls_anchor_addr ctx llvm_builder in
      let ty =
        match want with
        | Some t -> t
        | None -> Llvm.integer_type ctx.llvm_ctx (Size.in_bits size)
      in
      Llvm.build_load ty ptr "" llvm_builder
  | Store (_, addr, data, _, _) ->
      let a = create_exp ctx scope llvm_builder blk_tid addr in
      let d = create_exp ctx scope llvm_builder blk_tid data in
      create_store ctx llvm_builder (d, a)
  | Load (_, addr, _, size) ->
      let a = create_exp ctx scope llvm_builder blk_tid addr in
      (match want with
       | Some ty when not (Llvm.classify_type ty = Llvm.TypeKind.Integer) ->
           Llvm.build_load ty (as_pointer ctx llvm_builder a) ""
             llvm_builder
       | _ -> create_load ctx llvm_builder (a, Size.in_bits size))
  | Let (var, e, body) ->
      let unique_var = fresh_let_var scope var in
      let v = create_exp ctx scope llvm_builder blk_tid e in
      insert_local scope blk_tid unique_var v;
      let body = Exp.substitute (Var var) (Var unique_var) body in
      create_exp ?want ctx scope llvm_builder blk_tid body
  | Ite (cond, true_exp, false_exp) ->
      let cond =
        as_integer ctx llvm_builder
          (create_exp ctx scope llvm_builder blk_tid cond)
      in
      let tv = create_exp ?want ctx scope llvm_builder blk_tid true_exp in
      let fv = create_exp ?want ctx scope llvm_builder blk_tid false_exp in
      select ctx llvm_builder ?want cond tv fv
  | Unknown (_, typ) ->
      let typ =
        match want with Some t -> t | None -> typ_lltype ctx typ
      in
      Llvm.build_freeze (Llvm.undef typ) "hike_unknown" llvm_builder

(* One memory node: the address is a pointer (a stack/VLA value) or an
   integer (the raw/heap lane); the marker carries the loaded value
   through the enclosing rhs. *)
and storage_access ?want ?(is_window = false)
    ~(storage : Hike_stack_model.ptr_storage option) ctx scope llvm_builder
    blk_tid node exp =
  let rewrite addr size marker = rewrite_mem_node exp addr size marker in
  (* A region/residue access's address value already points into its
     storage alloca.  A window access lives in the caller's frame: the
     window base GEP'd at the entry-relative offset. *)
  let addr_ptr addr =
    if is_window then
      match create_offset ctx scope llvm_builder blk_tid addr with
      | Some off ->
          Bil2llvm_ptr.materialize ctx scope llvm_builder blk_tid
            Hike_stack_model.Ptr_window off
      | None ->
          as_pointer ctx llvm_builder
            (create_exp ctx scope llvm_builder blk_tid addr)
    else
      (* The address value is the pointer: a rewritten def's value
         already points into its storage, and a reloaded base holds a
         real pointer.  No entry-line rebase. *)
      as_pointer ctx llvm_builder
        (create_exp ctx scope llvm_builder blk_tid addr)
  in
  match node with
  | `Load (addr, size) ->
      let marker = marker_of_size size in
      let p = addr_ptr addr in
      let ty =
        match want with
        | Some t -> t
        | None -> Llvm.integer_type ctx.llvm_ctx (Size.in_bits size)
      in
      let emit () = Llvm.build_load ty p "" llvm_builder in
      emit_with_marker ?want ctx scope llvm_builder blk_tid marker ~emit
        ~rewrite:(rewrite addr size)
  | `Store (addr, data, size) ->
      let marker = marker_of_size size in
      let p = addr_ptr addr in
      let emit () =
        let d = create_exp ctx scope llvm_builder blk_tid data in
        let _ : Llvm.llvalue = Llvm.build_store d p llvm_builder in
        d
      in
      emit_with_marker ctx scope llvm_builder blk_tid marker ~emit
        ~rewrite:(rewrite addr size)

(* Named-component routing: the mem var is the component's identity,
   bound to its global and native base; the address evaluates to
   native bits, so the GEP index is the exact native delta. *)
and sec_comp_access ?want ctx scope llvm_builder blk_tid ~(store : bool)
    (mv : var) (addr : exp) ~(data : exp option) (size : int) :
    Llvm.llvalue =
  match Core.Map.find !(ctx.sec_comps) mv with
  | Some (base, own_lo) ->
    let a =
      as_integer ctx llvm_builder
        (create_exp ctx scope llvm_builder blk_tid addr)
    in
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
      let ty =
        match want with
        | Some t -> t
        | None -> Llvm.integer_type ctx.llvm_ctx size
      in
      Llvm.build_load ty p "" llvm_builder
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

and emit_with_marker ?want ctx scope llvm_builder blk_tid marker ~emit
    ~rewrite =
  let v = emit () in
  insert_local scope blk_tid marker v;
  create_exp ?want ctx scope llvm_builder blk_tid (rewrite marker)

(* The one as_int boundary; as_arg is the identity (a lane's value is
   already its type). *)
let as_int ctx _scope llvm_builder _blk_tid _is_window v =
  Bil2llvm_ptr.as_int ctx llvm_builder v

let as_arg _ctx _scope _llvm_builder _blk_tid _a_exp v = v
