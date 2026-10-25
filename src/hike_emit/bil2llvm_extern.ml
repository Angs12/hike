(* External functions the user's signatures describe: the exact LLVM
   declaration and call.  An external whose record has only lowerable
   types is declared with its declared parameter types and called with
   them in their System V registers and stack slots; its declared return
   fills the first return lane of its class, and a long double return is
   pushed on the x87 stack.  Any other external keeps the generic
   convention. *)

open Bap.Std
module Abi = Hike_abi
open Bil2llvm_env
open Bil2llvm_exp

(* The types the emitter can pass and return: the integers, pointers,
   float, double and long double. *)
let lowers : Hike_sysv.ctype -> bool = function
  | Scalar
      (Bool | Char | Short | Int | Long | Long_long | Pointer
      | Real (Float | Double | Long_double)) -> true
  | Scalar _ | Complex _ | Aggregate _ -> false

let lltype ctx : Hike_sysv.ctype -> Llvm.lltype = function
  | Scalar (Bool | Char) -> Llvm.i8_type ctx.llvm_ctx
  | Scalar Short -> Llvm.i16_type ctx.llvm_ctx
  | Scalar Int -> Llvm.i32_type ctx.llvm_ctx
  | Scalar (Long | Long_long) -> ctx.i64_ty
  | Scalar Pointer -> ctx.ptr_ty
  | Scalar (Real Float) -> Llvm.float_type ctx.llvm_ctx
  | Scalar (Real Double) -> Llvm.double_type ctx.llvm_ctx
  | Scalar (Real Long_double) -> Llvm.x86fp80_type ctx.llvm_ctx
  | ty ->
      failwith
        ("hike-emit: no LLVM type for "
        ^ Sexplib0.Sexp.to_string (Hike_sysv.sexp_of_ctype ty))

let name sub_tid = Abi.strip_at (Tid.name sub_tid)

(* The record of an external sub, whether or not its types lower. *)
let record ctx sub_tid =
  if is_extern ctx sub_tid then Hike_signatures.find ctx.signatures (name sub_tid)
  else None

(* The record of an external sub and its placement, when its types all
   lower. *)
let lowering ctx sub_tid =
  Base.Option.bind (record ctx sub_tid) ~f:(fun record ->
      let types =
        Base.List.map record.Hike_signatures.params ~f:(fun p ->
            p.Hike_signatures.ty) in
      if Base.List.for_all types ~f:lowers
         && Base.Option.for_all record.Hike_signatures.return ~f:lowers
      then Some (record, Hike_signatures.place ~abi:ctx.abi record)
      else None)

let fn_type ctx (record : Hike_signatures.record) =
  let ret =
    match record.Hike_signatures.return with
    | None -> Llvm.void_type ctx.llvm_ctx
    | Some ty -> lltype ctx ty in
  let params =
    Array.of_list
      (Base.List.map record.Hike_signatures.params ~f:(fun p ->
           lltype ctx p.Hike_signatures.ty)) in
  if record.Hike_signatures.variadic then Llvm.var_arg_function_type ret params
  else Llvm.function_type ret params

(* The slots a call's outgoing stack arguments fill: the highest bound
   [call_arg] slot of the block, and the arity the promotion recorded
   from stores in other blocks. *)
let stack_arity ctx (blk : blk term) =
  let bound =
    Term.enum def_t blk
    |> Seq.fold ~init:0 ~f:(fun arity d ->
        let v = Def.lhs d in
        if Hike_stack_model.is_call_arg ctx.synth v then
          match Hike_synth.index_of ctx.synth v with
          | Some i -> Stdlib.max arity (i + 1)
          | None -> arity
        else arity) in
  let recorded =
    Term.enum jmp_t blk
    |> Seq.fold ~init:0 ~f:(fun arity j ->
        match Term.get_attr j Hike_stack_model.call_stack_arity with
        | Some n -> Stdlib.max arity n
        | None -> arity) in
  Stdlib.max bound recorded

let bits v = Llvm.integer_bitwidth (Llvm.type_of v)

(* A lane's value as the declared type: a pointer stays a pointer, an
   integer is truncated or extended to its width, a float or double is the
   low bits of the vector lane. *)
let declared ctx llvm_builder (ty : Hike_sysv.ctype) (v : Bil2llvm_value.t) =
  let width_of w =
    let value = as_int ctx llvm_builder v in
    let target = Llvm.integer_type ctx.llvm_ctx w in
    if bits value = w then value
    else if bits value > w then Llvm.build_trunc value target "" llvm_builder
    else Llvm.build_zext value target "" llvm_builder in
  match ty with
  | Scalar Pointer -> as_ptr llvm_builder v
  | Scalar (Bool | Char) -> width_of 8
  | Scalar Short -> width_of 16
  | Scalar Int -> width_of 32
  | Scalar (Long | Long_long) -> width_of 64
  | Scalar (Real Float) ->
      Llvm.build_bitcast (width_of 32) (Llvm.float_type ctx.llvm_ctx) ""
        llvm_builder
  | Scalar (Real Double) ->
      Llvm.build_bitcast (width_of 64) (Llvm.double_type ctx.llvm_ctx) ""
        llvm_builder
  | ty ->
      failwith
        ("hike-emit: no value for "
        ^ Sexplib0.Sexp.to_string (Hike_sysv.sexp_of_ctype ty))

(* The value a return lane takes from the call's result; the lanes the
   declared return does not fill are clobbered. *)
let result_lane ctx llvm_builder (record : Hike_signatures.record) result ret =
  let lane_ty = lane_type ctx ret in
  let first_of ~vector =
    Base.List.find ctx.abi.Abi.return_regs ~f:(fun r ->
        Bool.equal (Abi.is_vector_param_reg ctx.abi r) vector) in
  let is_first ~vector =
    Base.Option.exists (first_of ~vector) ~f:(Var.same (Arg.lhs ret)) in
  match record.Hike_signatures.return with
  | Some (Scalar Pointer) when is_first ~vector:false ->
      if lane_is_ptr ctx ret then result
      else Llvm.build_ptrtoint result lane_ty "" llvm_builder
  | Some (Scalar (Real (Float | Double) as real)) when is_first ~vector:true ->
      let width = (match real with Real Float -> 32 | _ -> 64) in
      let integer =
        Llvm.build_bitcast result (Llvm.integer_type ctx.llvm_ctx width) ""
          llvm_builder in
      let lane_bits =
        match Var.typ (Arg.lhs ret) with Type.Imm w -> w | _ -> ctx.addr_bits in
      let widened =
        Llvm.build_zext integer (Llvm.integer_type ctx.llvm_ctx lane_bits) ""
          llvm_builder in
      Llvm.build_bitcast widened lane_ty "" llvm_builder
  | Some (Scalar (Real _)) -> Llvm.undef lane_ty
  | Some _ when is_first ~vector:false ->
      let wide =
        if bits result >= ctx.addr_bits then result
        else Llvm.build_zext result ctx.i64_ty "" llvm_builder in
      if lane_is_ptr ctx ret then Bil2llvm_int.to_ptr llvm_builder wide else wide
  | _ -> Llvm.undef lane_ty

(* A call to an external with an exact record.  [callee] is its declared
   function, [slot_ptr i] the address of stack slot [i] at the call, and
   [bind_lane] binds a return lane to a value.  A variadic call passes
   after the fixed part the integer and vector registers it left and the
   stack slots past it. *)
let call ctx scope llvm_builder blk_tid blk target ~callee:(fn, fn_typ)
    ~slot_ptr ~bind_lane
    ((record : Hike_signatures.record), (call : Hike_sysv.call)) =
  let bir_args = get_args ctx target in
  let register_value regs index =
    Base.Option.bind (Base.List.nth regs index) ~f:(fun reg ->
        Base.List.find bir_args ~f:(fun a -> Var.same (Arg.lhs a) reg)
        |> Base.Option.map ~f:(fun arg ->
            create_exp ctx scope llvm_builder blk_tid
              (lane_exp scope blk_tid (Arg.rhs arg)))) in
  let undef = Bil2llvm_value.Int (Llvm.undef ctx.i64_ty) in
  let integer index =
    Base.Option.value (register_value ctx.abi.Abi.int_param_regs index)
      ~default:undef in
  let vector index =
    Base.Option.value (register_value ctx.abi.Abi.vector_param_regs index)
      ~default:undef in
  let stack_word slot =
    Bil2llvm_value.Int
      (Bil2llvm_memory.load_ptr llvm_builder ctx.i64_ty (slot_ptr slot)) in
  let declared = declared ctx llvm_builder in
  let fixed =
    Base.List.map2_exn record.Hike_signatures.params call.arguments
      ~f:(fun p a ->
          let ty = p.Hike_signatures.ty in
          match a.Hike_sysv.location with
          | Registers [ Integer_register i ] -> declared ty (integer i)
          | Registers [ Vector_register { index; _ } ] ->
              declared ty (vector index)
          | Stack { offset; _ } ->
              Bil2llvm_memory.load_ptr llvm_builder (lltype ctx ty)
                (slot_ptr (offset / ctx.abi.Abi.word))
          | Registers _ | Nowhere ->
              failwith "hike-emit: a scalar parameter has no single location") in
  let tail =
    if not record.Hike_signatures.variadic then []
    else
      let ints =
        Base.List.init
          (Base.List.length ctx.abi.Abi.int_param_regs
           - call.integer_registers_used)
          ~f:(fun i ->
              declared (Scalar Long) (integer (call.integer_registers_used + i))) in
      let vectors =
        Base.List.init
          (Base.List.length ctx.abi.Abi.vector_param_regs
           - call.vector_registers_used)
          ~f:(fun i ->
              declared (Scalar (Real Double))
                (vector (call.vector_registers_used + i))) in
      let first_slot = call.stack_size / ctx.abi.Abi.word in
      let slots =
        Base.List.init
          (Stdlib.max 0 (stack_arity ctx blk - first_slot))
          ~f:(fun i -> declared (Scalar Long) (stack_word (first_slot + i))) in
      ints @ vectors @ slots in
  let result =
    Llvm.build_call fn_typ fn (Array.of_list (fixed @ tail)) "" llvm_builder in
  (match call.return with
   | Returned_in [ X87_return ] ->
       Bil2llvm_fp.X87.push ctx llvm_builder
         (Bil2llvm_fp.X87.lane ctx llvm_builder result)
   | _ -> ());
  Base.List.iter (get_rets ctx target) ~f:(fun ret ->
      bind_lane ret (result_lane ctx llvm_builder record result ret))
