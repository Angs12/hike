(* Emitter call lane: sub declarations, call arms, dispatch. *)

open Bap.Std
open Bap.Std.Bil.Types
module Abi = Hike_abi
open Bil2llvm_env
open Bil2llvm_exp
open Bil2llvm_fp
open Bil2llvm_mem


(* Machine calls push a return address the callee's ret pops, so the
   call's fallthrough edge rebinds SP to its pre-call value.  The
   binding is edge-keyed.  The edge is recorded unconditionally — the
   phi planner's predecessor set is the rendered edges, so a call whose
   block does not track SP still needs its fallthrough recorded or the
   target's phis come out with no incoming. *)
let restore_sp_after_call llvm_builder ctx scope blk_tid fallthrough_tid =
  let sp_key = ctx.sp in
  let sp_restore =
    match get_local scope blk_tid sp_key with
    | None -> None
    | Some post_push ->
        let restored =
          Llvm.build_add post_push
            (Llvm.const_int (ctx.i64_ty) ctx.abi.Abi.word)
            "sp_restored" llvm_builder
        in
        (match get_local scope fallthrough_tid sp_key with
         | None -> insert_local scope fallthrough_tid sp_key restored
         | Some _ -> ());
        Some restored
  in
  Bil2llvm_phi.record_edge scope ~pred:blk_tid ~target:fallthrough_tid
    ~term_bb:(get_bb scope blk_tid) ?sp_restore ()

let create_call_args ctx scope blk_tid llvm_builder call_tid =
  let args = get_args ctx call_tid in
  let extern = is_extern ctx call_tid in
  let slot_args =
    Base.List.filter args ~f:(fun a -> Hike_stack_model.is_arg_slot (Arg.lhs a))
  in
  (* Slot parameter i binds the block's [call_arg i] def; both names
     derive from the index, so the binding is order-independent. *)
  let arg_value_of_slot i =
    get_local scope blk_tid
      (Hike_stack_model.call_arg ~word:ctx.abi.Abi.word i)
  in
  Base.List.map args ~f:(fun arg ->
      let exp = Arg.rhs arg in
      if Var.same (Arg.lhs arg)
          (Hike_stack_model.hike_window_var ~word:ctx.abi.Abi.word)
      then
        (* The caller-window base is the caller's SP at the call, as a
           pointer into the caller's residue. *)
        (match (get_local scope blk_tid ctx.sp, !(scope.cur_frame)) with
         | Some sp, Some fr -> (
             match fr.anchor_ptr with
             | Some aptr ->
                 let delta = Llvm.build_sub sp fr.anchor_i64 "" llvm_builder in
                 Llvm.build_gep (Llvm.i8_type ctx.llvm_ctx) aptr [| delta |] ""
                   llvm_builder
             | None -> Llvm.undef (var_lltype ctx (Arg.lhs arg)))
         | _ -> Llvm.undef (var_lltype ctx (Arg.lhs arg)))
      else if Hike_stack_model.is_arg_slot (Arg.lhs arg) then
        let i =
          Base.Option.value ~default:0
            (Base.List.findi slot_args
               ~f:(fun _ a -> Var.equal (Arg.lhs a) (Arg.lhs arg))
               |> Base.Option.map ~f:fst)
        in
        (match arg_value_of_slot i with
         | Some v ->
           let v =
             match Llvm.classify_type (Llvm.type_of v) with
             | Llvm.TypeKind.Integer ->
                 coerce_int_width ctx.llvm_ctx llvm_builder
                   ~bits:(Llvm.integer_bitwidth (Llvm.type_of v)) v
                   (Llvm.integer_bitwidth (var_lltype ctx (Arg.lhs arg)))
             | _ -> v
           in
           v
         | None -> Llvm.undef (var_lltype ctx (Arg.lhs arg)))
      else if extern && is_fp_param ctx (Arg.lhs arg) then
        (* Lowers YMM args to doubles for externs. *)
        let v = create_exp ctx scope llvm_builder blk_tid exp in
        let v =
          if Llvm.integer_bitwidth (Llvm.type_of v) = 256 then
            Llvm.build_trunc v (ctx.i64_ty) "" llvm_builder
          else v
        in
        Llvm.build_bitcast v (Llvm.double_type ctx.llvm_ctx) ""
          llvm_builder
      else
        create_exp ctx scope llvm_builder blk_tid exp)

type fp_ret_kind = FpFloat | FpDouble | FpLongDouble

let fp_double_libm : string list =
  [ "acos"; "acosh"; "asin"; "asinh"; "atan"; "atan2"; "atanh"; "cbrt";
    "ceil"; "copysign"; "cos"; "cosh"; "drem"; "erf"; "erfc"; "exp";
    "exp2"; "exp10"; "expm1"; "fabs"; "fdim"; "floor"; "fma"; "fmax";
    "fmin"; "fmod"; "gamma"; "hypot"; "j0"; "j1"; "jn"; "ldexp";
    "lgamma"; "log"; "log10"; "log1p"; "log2"; "logb"; "modf";
    "nearbyint"; "nextafter"; "nexttoward"; "nextup"; "nextdown"; "pow";
    "pow10"; "remainder"; "rint"; "round"; "scalb"; "scalbln"; "scalbn";
    "significand"; "sin"; "sinh"; "sqrt"; "tan"; "tanh"; "tgamma";
    "trunc"; "y0"; "y1"; "yn" ]

let fp_double_parsing : string list = [ "atof"; "strtod"; "strtod_l" ]
let fp_float_parsing : string list = [ "strtof"; "strtof_l" ]
let fp_longdouble_parsing : string list = [ "strtold"; "strtold_l" ]

let fp_double_libm_set = Base.Set.of_list (module Base.String) fp_double_libm
let fp_double_parsing_set = Base.Set.of_list (module Base.String) fp_double_parsing
let fp_float_parsing_set = Base.Set.of_list (module Base.String) fp_float_parsing
let fp_longdouble_parsing_set = Base.Set.of_list (module Base.String) fp_longdouble_parsing
let fp_double_direct_set = Base.Set.union fp_double_libm_set fp_double_parsing_set

let fp_ret_kind_of_extern ctx (sub_tid : tid) : fp_ret_kind option =
  if not (is_extern ctx sub_tid) then None
  else
    let name = strip_at (Tid.name sub_tid) in
    if Base.Set.mem fp_double_direct_set name then Some FpDouble
    else if Base.Set.mem fp_float_parsing_set name then Some FpFloat
    else if Base.Set.mem fp_longdouble_parsing_set name then Some FpLongDouble
    else if String.length name > 1 then
      let last = name.[String.length name - 1] in
      let base = String.sub name 0 (String.length name - 1) in
      if last = 'f' && Base.Set.mem fp_double_libm_set base then Some FpFloat
      else if last = 'l' && Base.Set.mem fp_double_libm_set base then
        Some FpLongDouble
      else None
    else None

let fp_lltype llvm_ctx = function
  | FpFloat -> Llvm.float_type llvm_ctx
  | FpDouble -> Llvm.double_type llvm_ctx
  | FpLongDouble -> Llvm.x86fp80_type llvm_ctx

let ret_type_of_rets ctx rets =
  match rets with
  | [] -> Llvm.void_type ctx.llvm_ctx
  | [ ret ] -> lane_type ctx ret
  | rets ->
      let rets_typs = Base.List.map rets ~f:(lane_type ctx) in
      Llvm.struct_type ctx.llvm_ctx (Array.of_list rets_typs)

let register_fn ctx sub_tid fn fn_typ =
  ctx.ll_funcs :=
    Core.Map.add_exn !(ctx.ll_funcs) ~key:sub_tid ~data:(fn, fn_typ)

let create_ret_type ctx sub_tid =
  match fp_ret_kind_of_extern ctx sub_tid with
  | Some kind -> fp_lltype ctx.llvm_ctx kind
  | None -> ret_type_of_rets ctx (get_rets ctx sub_tid)

(* The LLVM types of one arg list: Both-intent args pass pointers, an
   extern's FP params lower to doubles, the rest keep the BIR type. *)
let arg_types_of ctx sub_tid args =
  Base.List.map args ~f:(fun arg ->
      let var = Arg.lhs arg in
      if is_extern ctx sub_tid && is_fp_param ctx var then
        Llvm.double_type ctx.llvm_ctx
      else lane_type ctx arg)

let create_arg_types ctx sub_tid =
  arg_types_of ctx sub_tid (get_args ctx sub_tid)

let set_arg_names_of args fn =
  Base.List.iteri args ~f:(fun i arg ->
      let param = Llvm.param fn i in
      Llvm.set_value_name (Var.name (Arg.lhs arg)) param)

let set_arg_attrs_of ctx fn args =
  Base.List.iteri args ~f:(fun i arg ->
      if Arg.intent arg = Some Both then
        let attr = Llvm.create_enum_attr ctx.llvm_ctx "noalias" 0L in
        Llvm.add_function_attr fn attr (Llvm.AttrIndex.Param i))

let add_args_to_vars ctx scope llvm_builder blk_tid sub_tid fn =
  let args = get_args ctx sub_tid in
  Llvm.iter_params
    (fun param ->
      let arg =
        Base.List.find_exn args ~f:(fun arg ->
            Base.String.equal
              (Var.name (Arg.lhs arg))
              (Llvm.value_name param))
      in
      let value =
        match Llvm.classify_type (Llvm.type_of param) with
        | Llvm.TypeKind.Pointer
          when not (Hike_stack_model.is_ptr_arg arg) ->
            Llvm.build_ptrtoint param
              (Llvm.integer_type ctx.llvm_ctx ctx.addr_bits)
              "" llvm_builder
        | _ -> param
      in
      insert_local scope blk_tid (Arg.lhs arg) value)
    fn

let create_fun_declaration ctx sub_tid =
  let ret_typ = create_ret_type ctx sub_tid in
  let args_typ = create_arg_types ctx sub_tid in
  (* Extern declares are variadic. *)
  let fn_typ =
    if is_extern ctx sub_tid then
      Llvm.var_arg_function_type ret_typ (Array.of_list args_typ)
    else Llvm.function_type ret_typ (Array.of_list args_typ)
  in
  let fn =
    Llvm.declare_function (sanitize_name @@ Tid.name sub_tid) fn_typ
      ctx.llvm_module
  in
  register_fn ctx sub_tid fn fn_typ

let create_fun ctx sub_tid ~rets ~args =
  let ret_typ = ret_type_of_rets ctx rets in
  let args_typ = arg_types_of ctx sub_tid args in
  let fn_typ = Llvm.function_type ret_typ (Array.of_list args_typ) in
  let fn =
    Llvm.define_function (sanitize_name @@ Tid.name sub_tid) fn_typ
      ctx.llvm_module
  in
  set_arg_names_of args fn;
  register_fn ctx sub_tid fn fn_typ;
  set_arg_attrs_of ctx fn args


let get_func ctx tid =
  match Core.Map.find !(ctx.ll_funcs) tid with
  | Some v -> v
  | None ->
      create_fun_declaration ctx tid;
      Core.Map.find_exn !(ctx.ll_funcs) tid

(* Binds the call result into the ret lanes: a single ret zeroext,
   multiple rets extract from the aggregate. *)
let bind_call_rets ctx scope blk_tid llvm_builder fn_typ fn args rets =
  match rets with
  | [] ->
      Llvm.build_call fn_typ fn (Array.of_list args) "" llvm_builder
      |> ignore
  | [ ret ] ->
      let ret_var =
        Llvm.build_call fn_typ fn (Array.of_list args) "" llvm_builder
      in
      (* A sub-register lane needs the extension promise; a full-width
         lane carries it vacuously. *)
      (match Llvm.classify_type (Llvm.type_of ret_var) with
       | Llvm.TypeKind.Integer when
           Llvm.integer_bitwidth (Llvm.type_of ret_var) < ctx.addr_bits ->
         Llvm.add_call_site_attr ret_var
           (Llvm.create_enum_attr ctx.llvm_ctx "zeroext" 0L)
           Llvm.AttrIndex.Return
       | _ -> ());
      insert_local scope blk_tid (Arg.lhs ret) ret_var
  | rets ->
      let ret_struct =
        Llvm.build_call fn_typ fn (Array.of_list args) "" llvm_builder
      in
      Base.List.iteri rets ~f:(fun i ret ->
          let ret_val = Llvm.build_extractvalue ret_struct i "" llvm_builder in
          insert_local scope blk_tid (Arg.lhs ret) ret_val)

(* The outgoing stack args in slot order: [call_arg k] defs
  enumerated by index, stopping at the first absent slot.  An extern
  consumes stack slots after the register args, so the window stores
  are its trailing varargs. *)
let extern_stack_args ctx scope blk_tid (blk : blk term) =
  let word = ctx.abi.Abi.word in
  (* The block's defined lhs vars, one pass; the slot walk conses and
     one rev restores slot order. *)
  let defined_vars =
    Term.enum def_t blk
    |> Seq.fold ~init:Var.Set.empty ~f:(fun acc d ->
        Core.Set.add acc (Def.lhs d))
  in
  let rec slots i acc =
    let v = Hike_stack_model.call_arg ~word i in
    if Core.Set.mem defined_vars v then
      match get_local scope blk_tid v with
      | Some value -> slots (i + 1) (value :: acc)
      | None -> acc
    else List.rev acc
  in
  slots 0 []

(* An extern float call's return lanes: RAX (and RDX for long
   doubles) split the FP bits; RDX of float externs stays undef. *)
let bind_extern_fp_rets ctx scope llvm_builder blk_tid fn_typ fn args rets
    ~(first : Arg.t) ~(kind : fp_ret_kind) =
  let ret_val = Llvm.build_call fn_typ fn (Array.of_list args) "" llvm_builder in
  let first_ret (v : Llvm.llvalue) = insert_local scope blk_tid (Arg.lhs first) v in
  let second_ret (v : Llvm.llvalue) =
    match rets with
    | _ :: rd :: _ -> insert_local scope blk_tid (Arg.lhs rd) v
    | _ -> ()
  in
  match kind with
  | FpLongDouble ->
    let bits =
      Llvm.build_bitcast ret_val (Llvm.integer_type ctx.llvm_ctx 80) ""
        llvm_builder
    in
    let rax = Llvm.build_trunc bits (ctx.i64_ty) "" llvm_builder in
    let high =
      Llvm.build_lshr bits
        (Llvm.const_int (Llvm.integer_type ctx.llvm_ctx 80) 64)
        "" llvm_builder
    in
    let rdx = Llvm.build_trunc high (ctx.i64_ty) "" llvm_builder in
    first_ret rax;
    second_ret rdx
  | FpFloat | FpDouble ->
    let d =
      Llvm.build_fpcast ret_val (Llvm.double_type ctx.llvm_ctx) "" llvm_builder
    in
    let i = Llvm.build_bitcast d (ctx.i64_ty) "" llvm_builder in
    first_ret i;
    second_ret (Llvm.undef (ctx.i64_ty))

let create_func_call ?(emit_unreachable = true) ctx scope llvm_builder blk_tid blk
    fallthrough target =
  let args = create_call_args ctx scope blk_tid llvm_builder target in
  let args =
    if is_extern ctx target then
      args @ extern_stack_args ctx scope blk_tid blk
    else args
  in
  let rets = get_rets ctx target in
  let fn, fn_typ = get_func ctx target in
  (match (fp_ret_kind_of_extern ctx target, rets) with
  | Some kind, ret :: _ ->
    bind_extern_fp_rets ctx scope llvm_builder blk_tid fn_typ fn args rets
      ~first:ret ~kind
  | _, rets -> bind_call_rets ctx scope blk_tid llvm_builder fn_typ fn args rets);
  (match fallthrough with
  | Some fallthrough ->
      restore_sp_after_call llvm_builder ctx scope blk_tid fallthrough;
      finish_call scope llvm_builder (Some fallthrough)
  | None ->
      if emit_unreachable then finish_call scope llvm_builder None)

(* An indirect site with an unresolved target: the pointer lands in
   a promoted target's thunk (via address rendering), else the
   target's existing convention. *)
let create_indirect_call ctx scope llvm_builder blk_tid (j : jmp term) =
  let icall_tid = indirect_call_tid in
  let call = call_exn j in
  let target = Call.target call |> label_exp in
  let fallthrough =
    Call.return call
    |> Base.Option.value_exn ~message:"Create call: expected call got return"
    |> label_tid
  in
  let target_exp = create_exp ctx scope llvm_builder blk_tid target in
  let func_ptr =
    if Llvm.classify_type (Llvm.type_of target_exp) = Llvm.TypeKind.Pointer
    then target_exp
    else Bil2llvm_section.create_addr_ptr ctx llvm_builder target_exp
  in
  let fn, fn_typ = get_func ctx icall_tid in
  let rets = get_rets ctx icall_tid in
  let args = create_call_args ctx scope blk_tid llvm_builder icall_tid in
  bind_call_rets ctx scope blk_tid llvm_builder fn_typ func_ptr args rets;
  restore_sp_after_call llvm_builder ctx scope blk_tid fallthrough;
  finish_call scope llvm_builder (Some fallthrough)

(* The Thunk — the memory-convention twin of a promoted sub. *)

let thunk_name_of (sub_tid : tid) : string =
  sanitize_name (Tid.name sub_tid) ^ "_hike_thunk"

let rec is_plt_trampoline ctx (sub : sub term) : bool =
  match Core.Map.find !(ctx.plt_trampolines) (Term.tid sub) with
  | Some v -> v
  | None ->
    let verdict = is_plt_trampoline_slow ctx sub in
    ctx.plt_trampolines := Core.Map.set !(ctx.plt_trampolines)
        ~key:(Term.tid sub) ~data:verdict;
    verdict

and is_plt_trampoline_slow ctx (sub : sub term) : bool =
  let free_vars = Hike_stack_model.free_regs sub in
  let reg_vars =
    Base.List.filter free_vars ~f:(fun reg ->
        not (Var.same reg ctx.sp)
        && not (Abi.is_return_reg ctx.abi reg))
  in
  reg_vars = []
  && Term.enum blk_t sub
     |> Seq.exists ~f:(fun blk ->
            Term.enum jmp_t blk
            |> Seq.exists ~f:(fun j ->
                   match Jmp.kind j with
                   | Call _ when not (Hike_return.is_jmp j) -> true
                   | _ -> false))

let thunk_tid_of (sub_tid : tid) : tid =
  Tid.for_name (Tid.name sub_tid ^ ":thunk")

(* The twin unpacks the window into the promoted body's slot
   parameters and forwards the register lanes.  Internal linkage: the
   consumer's optimizer inlines it where the call site resolves. *)
let create_thunk ctx (sub_tid : tid) =
  let llvm_ctx = ctx.llvm_ctx in
  let llvm_module = ctx.llvm_module in
      (* A twin exists iff the sub's own signature carries promoted
         slots. *)
  let arity = count_slot_args (get_args ctx sub_tid) in
  if arity = 0 then ()
  else if Core.Map.mem !(ctx.ll_funcs) (thunk_tid_of sub_tid) then ()
  else begin
    let args = get_args ctx sub_tid in
    let rets = get_rets ctx sub_tid in
    let word = ctx.abi.Abi.word in
    let window_var = Hike_stack_model.hike_window_var ~word in
    (* The twin carries the synthetic indirect convention — exactly
       what a pointer call passes. *)
    let conv = ctx.abi in
    let twin_args = window_conv_args ~word conv in
        let reg_args =
          Base.List.filter args ~f:(fun a ->
              (not (Hike_stack_model.is_arg_slot (Arg.lhs a)))
              && not (Var.same (Arg.lhs a) window_var))
        in
      let ret_typ = ret_type_of_rets ctx rets in
      let arg_typs =
        Base.List.map twin_args ~f:(fun a ->
            if Var.same (Arg.lhs a) window_var then
              Llvm.pointer_type llvm_ctx
            else lane_type ctx a)
      in
      let fn_typ =
        Llvm.function_type ret_typ (Array.of_list arg_typs)
      in
      let fn =
        Llvm.define_function (thunk_name_of sub_tid) fn_typ llvm_module
      in
      Llvm.set_linkage Llvm.Linkage.Internal fn;
      Base.List.iteri twin_args ~f:(fun i a ->
          Llvm.set_value_name (Var.name (Arg.lhs a)) (Llvm.param fn i));
      register_fn ctx (thunk_tid_of sub_tid) fn fn_typ;
      (* The twin's body: unpack the window, forward, return. *)
      let builder = Llvm.builder_at_end llvm_ctx (Llvm.entry_block fn) in
      let window = Llvm.param fn (Base.List.length twin_args - 1) in
      let slot_vals =
        Base.List.init arity ~f:(fun i ->
            let off =
              Llvm.const_of_int64 (Llvm.i64_type llvm_ctx)
                (Hike_stack_model.slot_offset ~word:ctx.abi.Abi.word i) false
            in
            let ptr =
              Llvm.build_gep (Llvm.i8_type llvm_ctx) window [| off |] ""
                builder
            in
            Llvm.build_load
              (Llvm.integer_type llvm_ctx (8 * word)) ptr "" builder)
      in
      (* Forwards [sub]'s register lanes by name from the twin's
         params, then the unpacked slots; a lane the twin's
         convention lacks reads undef. *)
      let param_named (v : var) : Llvm.llvalue =
        let n = Var.name v in
        Base.Option.value
          (Base.List.findi twin_args ~f:(fun i a -> Var.name (Arg.lhs a) = n)
           |> Base.Option.map ~f:(fun (i, _) -> Llvm.param fn i))
          ~default:(Llvm.undef (Llvm.i64_type llvm_ctx))
      in
      let call_args =
        Base.List.map reg_args ~f:(fun a -> param_named (Arg.lhs a))
        |> fun regs -> regs @ slot_vals
      in
      let callee_fn, callee_typ = get_func ctx sub_tid in
      let r =
        Llvm.build_call callee_typ callee_fn
          (Array.of_list call_args) "" builder
      in
      (match rets with
       | [] -> ignore (Llvm.build_ret_void builder)
       | _ -> ignore (Llvm.build_ret r builder));
      ctx.thunks :=
        (sanitize_name (Tid.name sub_tid), fn) :: !(ctx.thunks)
    end

let create_return ctx scope blk_tid llvm_builder cur_sub =
  let rets =
    Base.List.map (get_rets ctx (Term.tid cur_sub)) ~f:(fun ret ->
        match get_local scope blk_tid (Arg.lhs ret) with
        | Some v -> v
        | None ->
            warn_undef_read ctx scope (Arg.lhs ret) blk_tid;
            Llvm.undef (var_lltype ctx (Arg.lhs ret)))
  in
  match rets with
  | [] -> Llvm.build_ret_void llvm_builder |> ignore
  | [ ret ] -> Llvm.build_ret ret llvm_builder |> ignore
  | rets -> Llvm.build_aggregate_ret (Array.of_list rets) llvm_builder |> ignore

let create_indirect_tail ctx scope llvm_builder blk_tid blk sub (j : jmp term) =
  let call = call_exn j in
  match Call.target call with
  | Indirect (Bil.Unknown _) ->
      create_return ctx scope blk_tid llvm_builder sub
  | Indirect target ->
      let target_exp = create_exp ctx scope llvm_builder blk_tid target in
      let target_ptr =
        if Llvm.classify_type (Llvm.type_of target_exp) = Llvm.TypeKind.Pointer
        then target_exp
        else Bil2llvm_section.create_addr_ptr ctx llvm_builder target_exp
      in
      ignore
        (build_indirect_br llvm_builder target_ptr
           ~reserved_destinations:indirect_br_no_reserved)
  | Direct _ -> failwith "create_indirect_tail: expected an indirect target"

(* Unmapped intrinsic stubs use a fixed i64 synthetic ABI; normalize
   their operands to that interface before the external call. *)
let create_external_intrinsic_call ctx scope llvm_builder blk_tid call name =
  let target = Call.target call |> label_tid in
  let args = get_args ctx target in
  let n_args = Base.List.length args in
  let fn_ty = Llvm.function_type (ctx.i64_ty)
      (Array.init n_args (fun _ -> ctx.i64_ty)) in
  let callee = Llvm.declare_function name fn_ty ctx.llvm_module in
  let arg_vals =
    Base.List.map ~f:(fun a ->
        let v = create_exp ctx scope llvm_builder blk_tid (Arg.rhs a) in
        match Llvm.classify_type (Llvm.type_of v) with
        | Llvm.TypeKind.Integer ->
            let bits = Llvm.integer_bitwidth (Llvm.type_of v) in
            coerce_int_width ctx.llvm_ctx llvm_builder ~bits v 64
        | _ -> v)
      args
  in
  let r = Llvm.build_call fn_ty callee
      (Array.of_list arg_vals) "" llvm_builder in
  (match get_rets ctx target with
   | [ ret ] -> insert_local scope blk_tid (Arg.lhs ret) r
   | _ -> ());
  let fallthrough = Option.map label_tid (Call.return call) in
  Option.iter
    (fun t ->
      Bil2llvm_phi.record_edge scope ~pred:blk_tid ~target:t
        ~term_bb:(get_bb scope blk_tid) ())
    fallthrough;
  finish_call scope llvm_builder fallthrough

(* A self-call stub targets its own address (the symtab names an
   external there); it declares but never defines, so call sites
   resolve to the external at link time. *)
let is_self_call_stub (ctx : emit_ctx) (sub : sub term) : bool =
  let sub_name = sanitize_name (Tid.name (Term.tid sub)) in
  let self_targeted =
    Term.enum blk_t sub
    |> Seq.exists ~f:(fun blk ->
        Term.enum jmp_t blk
        |> Seq.exists ~f:(fun j ->
            match Jmp.kind j with
            | Call c -> (
                match Call.target c with
                | Direct t ->
                    Tid.equal t (Term.tid sub)
                    || sanitize_name (Tid.name t) = sub_name
                | Indirect _ -> false)
            | _ -> false))
  in
  self_targeted && is_plt_trampoline ctx sub

let create_call ctx scope llvm_builder blk_tid blk sub call fr =
  let target = Call.target call |> label_tid in
  let name = Tid.name target |> fp_intrinsic_name in
  if Bil2llvm_env.is_interrupt_name (Tid.name target) then
    create_interrupt ctx llvm_builder
  else
    match native_fp_op (Tid.name target) with
    | Some op ->
        create_native_fp_call ctx scope llvm_builder blk_tid (Term.tid sub) fr blk call
          op
    | None ->
        if Hike_abi.is_intrinsic_name name then begin
          Hike_diag.warn
            "guarded: unmapped intrinsic call: %s (in sub %s) - emitting as external; result lanes bind the external result"
            name (Tid.name (Term.tid sub));
          create_external_intrinsic_call ctx scope llvm_builder blk_tid call name
        end
        else (
        match Call.return call with
        | Some l ->
            let fallthrough = Some (label_tid l) in
            create_func_call ctx scope llvm_builder blk_tid blk fallthrough target
        | None ->
            create_func_call ~emit_unreachable:false ctx scope llvm_builder blk_tid
              blk None target;
            create_return ctx scope blk_tid llvm_builder sub)
