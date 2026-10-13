(* Emitter expression lane: pure exp emission (no calls, no mem dispatch). *)

open Bap.Std
open Bap.Std.Bil.Types
module Abi = Hike_abi
open Bil2llvm_env
open Bil2llvm_ptr

(* PT_TLS owns its byte range; the TCB belongs to the native runtime. *)
type tls_class =
  | Tls_block of int64           (* the block's byte index *)
  | Tls_tp of int64              (* the real thread pointer's offset *)
  | Tls_tp_exp of exp            (* the dynamic offset; the pointer reads 0 *)
  | Not_tls

let tls_classify ctx (addr : exp) : tls_class =
  match
    Hike_stack_model.tls_tp_offset ~tp:ctx.abi.Abi.thread_pointer addr
  with
  | Hike_stack_model.Tp_absent -> Not_tls
  | Tp_nonlinear ->
    failwith
      "hike-emit: tls: an access reads the thread pointer but is not \
       pointer-plus-offset (a width-changing cast or a non-unit \
       coefficient) - no sound TLS rendering exists"
  | Tp_based None ->
    Tls_tp_exp
      (Exp.substitute (Bil.Var ctx.abi.Abi.thread_pointer)
         (Bil.Int (Word.zero ctx.addr_bits)) addr)
  | Tp_based (Some o) -> (
    match !(ctx.tls) with
    | Some (_, tls) when o >= tls.tls_base
                        && o < Int64.add tls.tls_base tls.tls_memsz ->
      Tls_block (Int64.add (Int64.sub o tls.tls_base)
                   (Int64.of_int tls.tls_prefix))
    | _ -> Tls_tp o)

(* The real thread pointer: the native runtime's own value. *)
let thread_pointer ctx llvm_builder =
  let fty = Llvm.function_type ctx.ptr_ty [||] in
  let f = Llvm.declare_function "llvm.thread.pointer" fty ctx.llvm_module in
  Llvm.build_call fty f [||] "hike_tp" llvm_builder

(* The one memory node of an exp (a def's rhs holds at most one). *)
type mem_node = [ `Load of exp * Size.t | `Store of exp * exp * Size.t ]

let marker_of_size size =
  Hike_synth.accumulator ~addr_bits:(Size.in_bits size)

(* The Let-binder's evaluation temp: a fresh identity with a name the
   lifted vocabulary never uses, so the substitution cannot capture. *)
let fresh_let_var ctx scope (v : Var.t) : Var.t =
  incr scope.let_counter;
  Hike_synth.let_var ~addr_bits:ctx.addr_bits !(scope.let_counter) (Var.typ v)

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

(* ---- The expression evaluator.  The pointer semantics live in
   [Bil2llvm_ptr]; this lane evaluates exps and asks it for values. ---- *)

(* A cell read: [ptr] reads a word cell as the pointer it holds (the
   def's whole value is the load and the def is pointer-typed); any
   other load reads its BIR size. *)
let cell_is_ptr ctx ~ptr size = ptr && Size.in_bits size = ctx.addr_bits

let cell_type ctx ~ptr size =
  if cell_is_ptr ctx ~ptr size then ctx.ptr_ty
  else Llvm.integer_type ctx.llvm_ctx (Size.in_bits size)

let cell_value ctx ~ptr size v =
  if cell_is_ptr ctx ~ptr size then Bil2llvm_value.Ptr v
  else Bil2llvm_value.Int v

let load_cell ctx llvm_builder ~ptr size p =
  cell_value ctx ~ptr size
    (Bil2llvm_memory.load_ptr llvm_builder (cell_type ctx ~ptr size) p)

let as_int ctx b v = Bil2llvm_value.as_int ~addr_bits:ctx.addr_bits b v
let as_ptr b v = Bil2llvm_value.as_ptr b v

(* The entry-line offset of an expression, when structurally known: an
   arithmetic chain from the entry line / a slot.  A load, parameter,
   phi, or cast has none. *)
let synth_value ctx scope llvm_builder blk_tid v =
  match Bil2llvm_synth.value ctx scope llvm_builder blk_tid v with
  | Some value -> value
  | None ->
    warn_undef_read ctx scope v blk_tid;
    frozen_undef ctx scope v

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
  | Bil.Int w -> Some (coerce (Bil2llvm_int.immediate ctx.llvm_ctx w))
  | Bil.Var v -> (
      match get_ptr_offset scope v with
      | Some off -> Some off
      | None ->
          if is_ptr_var v then None
          else
            match create_exp ctx scope llvm_builder blk_tid exp with
            | Bil2llvm_value.Int x -> Some x
            | Bil2llvm_value.Ptr _ -> None)
  | BinOp (op, e1, e2) -> (
      match
        ( create_offset ctx scope llvm_builder blk_tid e1,
          create_offset ctx scope llvm_builder blk_tid e2 )
      with
      | Some a, Some b ->
          Some (Bil2llvm_int.binop llvm_builder op (coerce a) (coerce b))
      | _ -> None)
  | UnOp (op, e) ->
      Base.Option.map (create_offset ctx scope llvm_builder blk_tid e)
        ~f:(fun v -> Bil2llvm_int.unop llvm_builder op v)
  | Ite (cond, t, f) -> (
      match
        ( create_offset ctx scope llvm_builder blk_tid t,
          create_offset ctx scope llvm_builder blk_tid f )
      with
      | Some tv, Some fv ->
          let c = as_int ctx llvm_builder
              (create_exp ctx scope llvm_builder blk_tid cond) in
          Some (Bil2llvm_int.select llvm_builder c tv fv)
      | _ -> None)
  | Load _ | Store _ | Unknown _ | Cast _ | Extract _ | Concat _ | Let _ ->
      None

and create_exp ctx scope llvm_builder blk_tid exp : Bil2llvm_value.t =
  let addr_bits = ctx.addr_bits in
  let eval e = create_exp ctx scope llvm_builder blk_tid e in
  match exp with
  | BinOp (op, e1, e2) ->
      Bil2llvm_value.lift2 ~addr_bits llvm_builder op (eval e1) (eval e2)
  | UnOp (op, e) -> Bil2llvm_value.lift1 ~addr_bits llvm_builder op (eval e)
  | Var v when Var.same v ctx.abi.Abi.thread_pointer ->
      Bil2llvm_value.Int
        (Llvm.build_ptrtoint (thread_pointer ctx llvm_builder)
           (Llvm.integer_type ctx.llvm_ctx addr_bits) "hike_tp_value"
           llvm_builder)
  | Var v -> synth_value ctx scope llvm_builder blk_tid v
  | Int i -> Bil2llvm_value.Int (Bil2llvm_int.immediate ctx.llvm_ctx i)
  | Cast (cast, i, e) ->
      Bil2llvm_value.cast ~addr_bits llvm_builder cast i (eval e)
  | Concat (e1, e2) ->
      Bil2llvm_value.concat ~addr_bits llvm_builder (eval e1) (eval e2)
  | Extract (hi, lo, e) ->
      Bil2llvm_value.extract ~addr_bits llvm_builder hi lo (eval e)
  | Store (mem, addr, data, _, _) -> (
    match tls_classify ctx addr with
    | Not_tls -> tls_plain_store ctx scope llvm_builder blk_tid mem addr data
    | cls ->
        let ptr = tls_ptr ctx scope llvm_builder blk_tid cls in
        let d = eval data in
        ignore (Bil2llvm_memory.store_ptr llvm_builder (Bil2llvm_value.ll d) ptr);
        d)
  | Load (mem, addr, _, size) -> (
    match tls_classify ctx addr with
    | Not_tls -> tls_plain_load ctx scope llvm_builder blk_tid mem addr size
    | cls ->
        load_cell ctx llvm_builder ~ptr:false size
          (tls_ptr ctx scope llvm_builder blk_tid cls))
  | Let (var, e, body) ->
      let unique_var = fresh_let_var ctx scope var in
      insert_local scope blk_tid unique_var (eval e);
      eval (Exp.substitute (Var var) (Var unique_var) body)
  | Ite (cond, true_exp, false_exp) ->
      Bil2llvm_value.select ~addr_bits llvm_builder (eval cond)
        (eval true_exp) (eval false_exp)
  | Unknown (_, typ) ->
      let v = Llvm.build_freeze (Llvm.undef (typ_lltype ctx typ))
          "hike_unknown" llvm_builder in
      (match typ with
       | Type.Imm _ -> Bil2llvm_value.Int v
       | _ -> Bil2llvm_value.Ptr v)

and tls_ptr ctx scope llvm_builder blk_tid cls =
  let addr_bits = ctx.addr_bits in
  let i64 n = Llvm.const_of_int64 (Llvm.i64_type ctx.llvm_ctx) n false in
  match cls with
  | Tls_block idx ->
    let block, _ = Base.Option.value_exn !(ctx.tls) in
    let fty = Llvm.function_type ctx.ptr_ty [| ctx.ptr_ty |] in
    let f =
      Llvm.declare_function "llvm.threadlocal.address" fty ctx.llvm_module
    in
    let base = Llvm.build_call fty f [| block |] "tls_addr" llvm_builder in
    Bil2llvm_ptr.offset ~addr_bits llvm_builder base (i64 idx)
  | Tls_tp off ->
    Bil2llvm_ptr.offset ~addr_bits llvm_builder
      (thread_pointer ctx llvm_builder) (i64 off)
  | Tls_tp_exp e ->
    let off = as_int ctx llvm_builder
        (create_exp ctx scope llvm_builder blk_tid e) in
    Bil2llvm_ptr.offset ~addr_bits llvm_builder
      (thread_pointer ctx llvm_builder) off
  | Not_tls -> assert false

(* The generic memory arms an unclassified access keeps (split out of
   [create_exp]'s dispatch so the TLS arms read as one rule). *)
and tls_plain_store ctx scope llvm_builder blk_tid mem addr data =
  let a = create_exp ctx scope llvm_builder blk_tid addr in
  let d = create_exp ctx scope llvm_builder blk_tid data in
  let dv = Bil2llvm_value.ll d in
  (match mem with
   | Bil.Var mv when Hike_synth.is_memory_var ctx.synth mv -> (
     match
       Bil2llvm_memory.component_ptr ctx llvm_builder mv
         (as_int ctx llvm_builder a)
     with
     | Some p -> ignore (Bil2llvm_memory.store_ptr llvm_builder dv p)
     | None -> ignore (Bil2llvm_memory.store ctx llvm_builder dv a))
   | _ -> ignore (Bil2llvm_memory.store ctx llvm_builder dv a));
  d

and tls_plain_load ?(ptr_cell = false) ctx scope llvm_builder blk_tid mem
    addr size =
  let a = create_exp ctx scope llvm_builder blk_tid addr in
  let raw () =
    cell_value ctx ~ptr:ptr_cell size
      (Bil2llvm_memory.load ctx llvm_builder a
         (cell_type ctx ~ptr:ptr_cell size))
  in
  match mem with
  | Bil.Var mv when Hike_synth.is_memory_var ctx.synth mv -> (
    match
      Bil2llvm_memory.component_ptr ctx llvm_builder mv
        (as_int ctx llvm_builder a)
    with
    | Some p -> load_cell ctx llvm_builder ~ptr:ptr_cell size p
    | None -> raw ())
  | _ -> raw ()

(* One memory node: the address is a pointer (a stack/VLA value) or an
   integer (the raw/heap lane); the marker carries the loaded value
   through the enclosing rhs.  [ptr_cell]: the cell is read as the
   pointer it holds. *)
and storage_access ?(ptr_cell = false) ?(is_window = false)
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
          Bil2llvm_synth.materialize ctx scope llvm_builder blk_tid
            Hike_stack_model.Ptr_window off
      | None -> as_ptr llvm_builder (create_exp ctx scope llvm_builder blk_tid addr)
    else
      (* The address value is the pointer: a rewritten def's value
         already points into its storage, and a reloaded base holds a
         real pointer.  No entry-line rebase. *)
      as_ptr llvm_builder (create_exp ctx scope llvm_builder blk_tid addr)
  in
  match node with
  | `Load (addr, size) ->
      let p = addr_ptr addr in
      emit_with_marker ctx scope llvm_builder blk_tid (marker_of_size size)
        ~emit:(fun () -> load_cell ctx llvm_builder ~ptr:ptr_cell size p)
        ~rewrite:(rewrite addr size)
  | `Store (addr, data, size) ->
      let p = addr_ptr addr in
      let emit () =
        let d = create_exp ctx scope llvm_builder blk_tid data in
        ignore (Bil2llvm_memory.store_ptr llvm_builder (Bil2llvm_value.ll d) p);
        d
      in
      emit_with_marker ctx scope llvm_builder blk_tid (marker_of_size size)
        ~emit ~rewrite:(rewrite addr size)

(* Named-component routing: the mem var names storage and the address
   is its byte index, just as for a stack storage access.  The marker
   re-evaluation preserves the def's enclosing structure (a load inside
   a cast), exactly as the stack path does. *)
and sec_comp_access ?(ptr_cell = false) ctx scope llvm_builder blk_tid exp
    ~(store : bool) (mv : var) (addr : exp) ~(data : exp option)
    (size : Size.t) : Bil2llvm_value.t =
  let emit () =
    let idx = as_int ctx llvm_builder
        (create_exp ctx scope llvm_builder blk_tid addr) in
    let stored () =
      match data with
      | Some d -> create_exp ctx scope llvm_builder blk_tid d
      | None -> assert false
    in
    match Bil2llvm_memory.component_ptr ctx llvm_builder mv idx with
    | Some p ->
      if store then begin
        let d = stored () in
        ignore (Bil2llvm_memory.store_ptr llvm_builder (Bil2llvm_value.ll d) p);
        d
      end
      else load_cell ctx llvm_builder ~ptr:ptr_cell size p
    | None ->
      (* Unknown component: the generic memory path, unremapped. *)
      let a = Bil2llvm_value.Int idx in
      if store then begin
        let d = stored () in
        ignore (Bil2llvm_memory.store ctx llvm_builder (Bil2llvm_value.ll d) a);
        d
      end
      else
        cell_value ctx ~ptr:ptr_cell size
          (Bil2llvm_memory.load ctx llvm_builder a
             (cell_type ctx ~ptr:ptr_cell size))
  in
  emit_with_marker ctx scope llvm_builder blk_tid (marker_of_size size) ~emit
    ~rewrite:(rewrite_mem_node exp addr size)

and emit_with_marker ctx scope llvm_builder blk_tid marker ~emit ~rewrite =
  insert_local scope blk_tid marker (emit ());
  create_exp ctx scope llvm_builder blk_tid (rewrite marker)
