(* Emitter call lane: sub declarations, call arms, dispatch. *)

open Bap.Std
open Bap.Std.Bil.Types
module Abi = Hike_abi
module KB = Bap_knowledge.Knowledge
open Bil2llvm_env
open Bil2llvm_exp
open Bil2llvm_fp


(* Machine calls push a return address the callee's ret pops, so the
   call's fallthrough edge rebinds SP to its pre-call value.  The
   binding is edge-keyed. *)
let restore_sp_after_call llvm_builder ctx blk_tid fallthrough_tid =
  let open KB in
  let sp_key = ctx.sp in
  match get_local ctx blk_tid sp_key with
  | None -> return ()
  | Some post_push ->
        let* { llvm_ctx; _ } = Context.get emit_ctx_var in
        let restored =
          Llvm.build_add post_push
            (Llvm.const_int (Llvm.i64_type llvm_ctx) ctx.abi.Abi.word)
            "sp_restored" llvm_builder
        in
        Edge_tbl.set !(ctx.edge_tbl) ~pred:blk_tid ~target:fallthrough_tid
          ~term_bb:(get_bb ctx blk_tid)
          ~sp_restore:restored ();
        (match get_local ctx fallthrough_tid sp_key with
         | None -> insert_local ctx fallthrough_tid sp_key restored
         | Some _ -> ());
        return ()

let create_call_args blk_tid llvm_builder
    call_tid =
  let open KB in
  let* ctx, llvm_ctx = emit_env () in
  let args = get_args ctx call_tid in
  let extern = is_extern ctx call_tid in
  let slot_args =
    Base.List.filter args ~f:(fun a -> Hike_stack_model.is_arg_slot (Arg.lhs a))
  in
  (* Slot parameter k binds the block's [call_arg (k-1)] def; both
     names derive from the index, so the binding is order-independent. *)
  let arg_value_of_slot k =
    if k < 1 then None
    else
      get_local ctx blk_tid
        (Hike_stack_model.call_arg ~word:ctx.abi.Abi.word (k - 1))
  in
  KB.List.map args ~f:(fun arg ->
      let exp = Arg.rhs arg in
      if Var.same (Arg.lhs arg)
          (Hike_stack_model.hike_window_var ~word:ctx.abi.Abi.word)
      then
        (* The caller-window base is the caller's SP at the call. *)
        (match get_local ctx blk_tid ctx.sp with
         | Some v -> return v
         | None ->
             let* ty = var_lltype (Arg.lhs arg) in
             return @@ Llvm.undef ty)
      else if Hike_stack_model.is_arg_slot (Arg.lhs arg) then
        let k =
          Base.Option.value_map
            (Base.List.findi slot_args
               ~f:(fun _ a -> Var.equal (Arg.lhs a) (Arg.lhs arg)))
            ~default:0 ~f:(fun (i, _) -> i + 1)
        in
        (match arg_value_of_slot k with
         | Some v ->
             let* ty = var_lltype (Arg.lhs arg) in
             let v =
               match Llvm.classify_type (Llvm.type_of v) with
               | Llvm.TypeKind.Integer ->
                   coerce_int_width llvm_ctx llvm_builder
                     ~bits:(Llvm.integer_bitwidth (Llvm.type_of v)) v
                     (Llvm.integer_bitwidth ty)
               | _ -> v
             in
             return v
         | None ->
             let* ty = var_lltype (Arg.lhs arg) in
             return @@ Llvm.undef ty)
      else if extern && is_fp_param ctx (Arg.lhs arg) then
        (* Lowers YMM args to doubles for externs. *)
        let* v = create_exp llvm_builder blk_tid exp in
        let* { llvm_ctx; _ } = Context.get emit_ctx_var in
        let* v =
          if Llvm.integer_bitwidth (Llvm.type_of v) = 256 then
            KB.return
            @@ Llvm.build_trunc v (Llvm.i64_type llvm_ctx) "" llvm_builder
          else KB.return v
        in
        KB.return @@ Llvm.build_bitcast v (Llvm.double_type llvm_ctx) ""
          llvm_builder
      else
        let* arg = create_exp llvm_builder blk_tid exp in
        KB.return arg)

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

let fp_ret_kind_of_extern ctx (sub_tid : tid) : fp_ret_kind option =
  if not (is_extern ctx sub_tid) then None
  else
    let name = strip_at (Tid.name sub_tid) in
    if Base.Set.mem fp_double_libm_set name then Some FpDouble
    else if Base.Set.mem fp_double_parsing_set name then Some FpDouble
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

let ret_type_of_rets rets =
  let open KB in
  let* { llvm_ctx; _ } = Context.get emit_ctx_var in
  match rets with
  | [] -> return @@ Llvm.void_type llvm_ctx
  | [ ret ] -> var_lltype (Arg.lhs ret)
  | rets ->
      let* rets_typs =
        KB.List.map rets ~f:(fun ret -> var_lltype (Arg.lhs ret))
      in
      return @@ Llvm.struct_type llvm_ctx (Array.of_list rets_typs)

let register_fn ctx sub_tid fn fn_typ =
  ctx.ll_funcs :=
    Core.Map.add_exn !(ctx.ll_funcs) ~key:sub_tid ~data:(fn, fn_typ)

let create_ret_type sub_tid =
  let open KB in
  let* ctx, llvm_ctx = emit_env () in
  match fp_ret_kind_of_extern ctx sub_tid with
  | Some kind -> return @@ fp_lltype llvm_ctx kind
  | None -> ret_type_of_rets (get_rets ctx sub_tid)

(* The LLVM types of one arg list: Both-intent args pass pointers, an
   extern's FP params lower to doubles, the rest keep the BIR type. *)
let arg_types_of ctx sub_tid llvm_ctx args =
  let open KB in
  KB.List.map args ~f:(fun arg ->
      let var = Arg.lhs arg in
      if Arg.intent arg = Some Both then return @@ Llvm.pointer_type llvm_ctx
      else if is_extern ctx sub_tid && is_fp_param ctx var then
        return @@ Llvm.double_type llvm_ctx
      else var_lltype var)

let create_arg_types sub_tid =
  let open KB in
  let* ctx, llvm_ctx = emit_env () in
  arg_types_of ctx sub_tid llvm_ctx (get_args ctx sub_tid)

let set_arg_names_of args fn =
  Base.List.iteri args ~f:(fun i arg ->
      let param = Llvm.param fn i in
      Llvm.set_value_name (Var.name (Arg.lhs arg)) param)

let set_arg_attrs_of fn args =
  let open KB in
  let* { llvm_ctx; _ } = Context.get emit_ctx_var in
  Base.List.iteri args ~f:(fun i arg ->
      if Arg.intent arg = Some Both then
        let attr = Llvm.create_enum_attr llvm_ctx "noalias" 0L in
        Llvm.add_function_attr fn attr (Llvm.AttrIndex.Param i));
  return ()

let add_args_to_vars llvm_builder blk_tid sub_tid fn () =
  let open KB in
  let* ctx, llvm_ctx = emit_env () in
  let args = get_args ctx sub_tid in
  return
  @@ Llvm.iter_params
       (fun param ->
         let arg =
           Base.List.find_exn args ~f:(fun arg ->
               Base.String.equal
                 (Var.name (Arg.lhs arg))
                 (Llvm.value_name param))
         in
         let value =
           match Llvm.classify_type (Llvm.type_of param) with
           | Llvm.TypeKind.Pointer ->
               Llvm.build_ptrtoint param
                 (Llvm.integer_type llvm_ctx ctx.ptrsize)
                 "" llvm_builder
           | _ -> param
         in
         insert_local ctx blk_tid (Arg.lhs arg) value)
       fn

let create_fun_declaration sub_tid =
  let open KB in
  let* { llvm_module; _ } = Context.get emit_ctx_var in
  let* ctx = Context.get emit_ctx_var in
  let* ret_typ = create_ret_type sub_tid in
  let* args_typ = create_arg_types sub_tid in
  (* Extern declares are variadic. *)
  let fn_typ =
    if is_extern ctx sub_tid then
      Llvm.var_arg_function_type ret_typ (Array.of_list args_typ)
    else Llvm.function_type ret_typ (Array.of_list args_typ)
  in
  let fn =
    Llvm.declare_function (sanitize_name @@ Tid.name sub_tid) fn_typ llvm_module
  in
  register_fn ctx sub_tid fn fn_typ;
  return ()

let create_fun sub_tid ~rets ~args =
  let open KB in
  let* { llvm_ctx; _ } = Context.get emit_ctx_var in
  let* { llvm_module; _ } = Context.get emit_ctx_var in
  let* ctx = Context.get emit_ctx_var in
  let* ret_typ = ret_type_of_rets rets in
  let* args_typ = arg_types_of ctx sub_tid llvm_ctx args in
  let fn_typ = Llvm.function_type ret_typ (Array.of_list args_typ) in
  let fn =
    Llvm.define_function (sanitize_name @@ Tid.name sub_tid) fn_typ llvm_module
  in
  set_arg_names_of args fn;
  register_fn ctx sub_tid fn fn_typ;
  set_arg_attrs_of fn args >>= return


let get_func tid =
  let open KB in
  let* ctx = Context.get emit_ctx_var in
  match Core.Map.find !(ctx.ll_funcs) tid with
  | Some v -> return v
  | None ->
      let* _ = create_fun_declaration tid in
      return @@ Core.Map.find_exn !(ctx.ll_funcs) tid

(* Binds the call result into the ret lanes: a single ret zeroext,
   multiple rets extract from the aggregate. *)
let bind_call_rets ctx blk_tid llvm_builder fn_typ fn args rets =
  let open KB in
  let* { llvm_ctx; _ } = Context.get emit_ctx_var in
  match rets with
  | [] ->
      Llvm.build_call fn_typ fn (Array.of_list args) "" llvm_builder
      |> ignore;
      return ()
  | [ ret ] ->
      let ret_var =
        Llvm.build_call fn_typ fn (Array.of_list args) "" llvm_builder
      in
      Llvm.add_call_site_attr ret_var
        (Llvm.create_enum_attr llvm_ctx "zeroext" 0L)
        Llvm.AttrIndex.Return;
      insert_local ctx blk_tid (Arg.lhs ret) ret_var;
      return ()
  | rets ->
      let ret_struct =
        Llvm.build_call fn_typ fn (Array.of_list args) "" llvm_builder
      in
      Base.List.iteri rets ~f:(fun i ret ->
          let ret_val = Llvm.build_extractvalue ret_struct i "" llvm_builder in
          insert_local ctx blk_tid (Arg.lhs ret) ret_val);
      return ()

(* The outgoing stack args in slot order: [call_arg k] defs
  enumerated by index, stopping at the first absent slot.  An extern
  consumes stack slots after the register args, so the window stores
  are its trailing varargs. *)
let extern_stack_args ctx blk_tid (blk : blk term) =
  let word = ctx.abi.Abi.word in
  let defined v =
    Term.enum def_t blk
    |> Seq.exists ~f:(fun d -> Var.equal (Def.lhs d) v)
  in
  let rec slots i acc =
    let v = Hike_stack_model.call_arg ~word i in
    if defined v then
      match get_local ctx blk_tid v with
      | Some value -> slots (i + 1) (acc @ [ value ])
      | None -> acc
    else acc
  in
  slots 0 []

let create_func_call ?(emit_unreachable = true) llvm_builder blk_tid blk sub
    fallthrough target =
  let open KB in
  let* ctx, llvm_ctx = emit_env () in
  let* args = create_call_args blk_tid llvm_builder target in
  let* args =
    if is_extern ctx target then
      KB.return (args @ extern_stack_args ctx blk_tid blk)
    else KB.return args
  in
  let rets = get_rets ctx target in
  let* fn, fn_typ = get_func target in
  let* () =
    (match (fp_ret_kind_of_extern ctx target, rets) with
    | Some kind, ret :: _ ->
        (* Extern float returns bypass the model. *)
        let ret_val =
          Llvm.build_call fn_typ fn (Array.of_list args) "" llvm_builder
        in
        (match kind with
         | FpLongDouble ->
             let bits =
               Llvm.build_bitcast ret_val (Llvm.integer_type llvm_ctx 80) ""
                 llvm_builder
             in
             let rax =
               Llvm.build_trunc bits (Llvm.i64_type llvm_ctx) "" llvm_builder
             in
             let high =
               Llvm.build_lshr bits
                 (Llvm.const_int (Llvm.integer_type llvm_ctx 80) 64)
                 "" llvm_builder
             in
             let rdx =
               Llvm.build_trunc high (Llvm.i64_type llvm_ctx) "" llvm_builder
             in
             insert_local ctx blk_tid (Arg.lhs ret) rax;
             (match rets with
              | _ :: rd :: _ -> insert_local ctx blk_tid (Arg.lhs rd) rdx
              | _ -> ());
             return ()
         | FpFloat | FpDouble ->
             let d =
               Llvm.build_fpcast ret_val (Llvm.double_type llvm_ctx) ""
                 llvm_builder
             in
             let i =
               Llvm.build_bitcast d (Llvm.i64_type llvm_ctx) "" llvm_builder
             in
             insert_local ctx blk_tid (Arg.lhs ret) i;
             (match rets with
              | _ :: rd :: _ ->
                  (* RDX of float externs stays undef. *)
                  insert_local ctx blk_tid (Arg.lhs rd)
                    (Llvm.undef (Llvm.i64_type llvm_ctx))
              | _ -> ());
             return ())
    | _, rets -> bind_call_rets ctx blk_tid llvm_builder fn_typ fn args rets)
  in
  (match fallthrough with
  | Some fallthrough ->
      let* () = restore_sp_after_call llvm_builder ctx blk_tid fallthrough in
      finish_call llvm_builder ctx (Some fallthrough)
  | None ->
      if emit_unreachable then finish_call llvm_builder ctx None
      else return ())

(* An indirect site with an unresolved target: the pointer lands in
   a promoted target's thunk (via address rendering), else the
   target's existing convention. *)
let create_indirect_call llvm_builder blk_tid blk sub (j : jmp term) =
  let open KB in
  let* ctx = Context.get emit_ctx_var in
  let icall_tid = Tid.for_name "indirect_call" in
  let call = call_exn j in
  let target = Call.target call |> label_exp in
  let fallthrough =
    Call.return call
    |> Base.Option.value_exn ~message:"Create call: expected call got return"
    |> label_tid
  in
  let* target_exp = create_exp llvm_builder blk_tid target in
  let* func_ptr =
    if Llvm.classify_type (Llvm.type_of target_exp) = Llvm.TypeKind.Pointer
    then KB.return target_exp
    else Bil2llvm_section.create_addr_ptr llvm_builder target_exp
  in
  let* fn, fn_typ = get_func icall_tid in
  let rets = get_rets ctx icall_tid in
  let* args =
    create_call_args blk_tid llvm_builder icall_tid
  in
  let* () = bind_call_rets ctx blk_tid llvm_builder fn_typ func_ptr args rets in
  let* () = restore_sp_after_call llvm_builder ctx blk_tid fallthrough in
  finish_call llvm_builder ctx (Some fallthrough)

(* The Thunk — the memory-convention twin of a promoted sub. *)

let thunk_name_of (sub_tid : tid) : string =
  sanitize_name (Tid.name sub_tid) ^ "_hike_thunk"

let thunk_tid_of (sub_tid : tid) : tid =
  Tid.for_name (Tid.name sub_tid ^ ":thunk")

(* A slot's offset in the caller window (SysV: [entry_rsp + word +
   word*i]). *)
let slot_offset ~(word : int) (i : int) : Int64.t =
  Int64.of_int (word + (word * i))

(* The twin unpacks the window into the promoted body's slot
   parameters and forwards the register lanes.  Internal linkage: the
   consumer's optimizer inlines it where the call site resolves. *)
let create_thunk (sub_tid : tid) =
  let open KB in
  let* ctx = Context.get emit_ctx_var in
  let* { llvm_ctx; _ } = Context.get emit_ctx_var in
  let* { llvm_module; _ } = Context.get emit_ctx_var in
      (* A twin exists iff the sub's own signature carries promoted
         slots. *)
  let arity =
    Base.List.count (get_args ctx sub_tid) ~f:(fun a ->
        Hike_stack_model.is_arg_slot (Arg.lhs a))
  in
  if arity = 0 then
    KB.return ()
  else
    if Core.Map.mem !(ctx.ll_funcs) (thunk_tid_of sub_tid) then
      KB.return ()
    else begin
      let args = get_args ctx sub_tid in
      let rets = get_rets ctx sub_tid in
      let word = ctx.abi.Abi.word in
      let window_var = Hike_stack_model.hike_window_var ~word in
        (* The twin carries the synthetic indirect convention — exactly
           what a pointer call passes. *)
        let conv = Abi.of_target ctx.target in
        let twin_args = window_conv_args ~word conv in
        let reg_args =
          Base.List.filter args ~f:(fun a ->
              let n = Var.name (Arg.lhs a) in
              (not (Base.String.is_prefix n ~prefix:"hike_slot"))
              && not (Var.same (Arg.lhs a) window_var))
        in
        let* ret_typ = ret_type_of_rets rets in
        let* arg_typs =
          KB.List.map twin_args ~f:(fun a ->
              if Var.same (Arg.lhs a) window_var then
                KB.return @@ Llvm.integer_type llvm_ctx (8 * word)
              else var_lltype (Arg.lhs a))
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
              let addr =
                Llvm.build_add window
                  (Llvm.const_of_int64 (Llvm.i64_type llvm_ctx)
                     (slot_offset ~word:ctx.abi.Abi.word i) false)
                  "" builder
              in
              let ptr =
                Llvm.build_inttoptr addr (Llvm.pointer_type llvm_ctx) ""
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
        let* callee_fn, callee_typ = get_func sub_tid in
        let r =
          Llvm.build_call callee_typ callee_fn
            (Array.of_list call_args) "" builder
        in
        (match rets with
         | [] -> ignore (Llvm.build_ret_void builder)
         | _ -> ignore (Llvm.build_ret r builder));
        ctx.thunks :=
          (sanitize_name (Tid.name sub_tid), fn) :: !(ctx.thunks);
        KB.return ()
    end

let create_return blk_tid llvm_builder cur_sub =
  let open KB in
  let* ctx = Context.get emit_ctx_var in
  let* rets =
    KB.List.map (get_rets ctx (Term.tid cur_sub)) ~f:(fun ret ->
        match get_local ctx blk_tid (Arg.lhs ret) with
        | Some v -> return v
        | None ->
            let* typ = var_lltype (Arg.lhs ret) in
            warn_undef_read ctx (Arg.lhs ret) blk_tid;
            return @@ Llvm.undef typ)
  in
  (match rets with
  | [] -> Llvm.build_ret_void llvm_builder |> ignore
  | [ ret ] -> Llvm.build_ret ret llvm_builder |> ignore
  | rets -> Llvm.build_aggregate_ret (Array.of_list rets) llvm_builder |> ignore);
  return ()

let create_external_intrinsic_call llvm_builder blk_tid call name =
  let open KB in
  let* { llvm_ctx; _ } = Context.get emit_ctx_var in
  let* { llvm_module; _ } = Context.get emit_ctx_var in
  let* ctx = Context.get emit_ctx_var in
  let target = Call.target call |> label_tid in
  let args = get_args ctx target in
  let n_args = Base.List.length args in
  let fn_ty = Llvm.function_type (Llvm.i64_type llvm_ctx)
      (Array.init n_args (fun _ -> Llvm.i64_type llvm_ctx)) in
  let callee = Llvm.declare_function name fn_ty llvm_module in
  let* arg_vals =
    KB.List.map ~f:(fun a ->
        let* v = create_exp llvm_builder blk_tid (Arg.rhs a) in
        match Llvm.classify_type (Llvm.type_of v) with
        | Llvm.TypeKind.Integer ->
            let bits = Llvm.integer_bitwidth (Llvm.type_of v) in
            KB.return @@ coerce_int_width llvm_ctx llvm_builder ~bits v 64
        | _ -> KB.return v)
      args
  in
  let r = Llvm.build_call fn_ty callee
      (Array.of_list arg_vals) "" llvm_builder in
  (match get_rets ctx target with
   | [ ret ] -> insert_local ctx blk_tid (Arg.lhs ret) r
   | _ -> ());
  finish_call llvm_builder ctx (Option.map label_tid (Call.return call))

(* A self-call stub targets its own address (the symtab names an
   external there); it declares but never defines, so call sites
   resolve to the external at link time. *)
let is_self_call_stub (ctx : emit_ctx) (sub : sub term) : bool =
  let self_targeted =
    Term.enum blk_t sub
    |> Seq.exists ~f:(fun blk ->
        Term.enum jmp_t blk
        |> Seq.exists ~f:(fun j ->
            match Jmp.kind j with
            | Call c -> (
                match Call.target c with
                | Direct t -> Tid.equal t (Term.tid sub)
                | Indirect _ -> false)
            | _ -> false))
  in
  self_targeted && Bil2llvm_mem.is_plt_trampoline ctx sub

let create_call llvm_builder blk_tid blk sub call fr =
  let open KB in
  let* ctx = Context.get emit_ctx_var in
  let target = Call.target call |> label_tid in
  let name = Tid.name target |> fp_intrinsic_name in
  if Base.String.is_prefix (Tid.name target) ~prefix:"@interrupt:" then
    create_interrupt llvm_builder
  else
    match native_fp_op (Tid.name target) with
    | Some op ->
        create_native_fp_call llvm_builder blk_tid (Term.tid sub) fr blk call
          op
    | None ->
        if Hike_stack_model.is_intrinsic_name name then begin
          Hike_diag.warn
            "guarded: unmapped intrinsic call: %s (in sub %s) - emitting as external; result lanes are poison"
            name (Tid.name (Term.tid sub));
          create_external_intrinsic_call llvm_builder blk_tid call name
        end
        else (
        match Call.return call with
        | Some l ->
            let fallthrough = Some (label_tid l) in
            create_func_call llvm_builder blk_tid blk sub fallthrough target
        | None ->
            if Bil2llvm_mem.is_plt_trampoline ctx sub then
              let* () =
                create_func_call ~emit_unreachable:false llvm_builder blk_tid
                  blk sub None target
              in
              create_return blk_tid llvm_builder sub
            else create_func_call llvm_builder blk_tid blk sub None target)
