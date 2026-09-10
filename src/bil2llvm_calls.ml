(* Emitter call lane: sub declarations, native-FP table, call arms, dispatch. *)

open Bap.Std
open Bap.Std.Bil.Types
open Convutils
module Abi = Hike_abi
module KB = Bap_knowledge.Knowledge
open Bil2llvm_env
open Bil2llvm_exp


(* Restores SP after calls. *)
let restore_sp_after_call llvm_builder ctx sub_tid fr fallthrough_tid =
  let open KB in
  if fr.is_precise then return ()
  else
    let sp_key = ctx.Convutils.sp in
    match get_local ctx sub_tid sp_key with
    | None -> return ()
    | Some post_push ->
        let* llvm_ctx = Context.get llvm_ctx_var in
        let restored =
          Llvm.build_add post_push
            (Llvm.const_int (Llvm.i64_type llvm_ctx) 8) "sp_restored"
            llvm_builder
        in
        (* Binds restores edge-keyed. *)
        (match EHashtbl.find !(ctx.edge_sp_restores) sub_tid with
         | Some inner -> EHashtbl.set inner ~key:fallthrough_tid ~data:restored
         | None ->
             let inner = EHashtbl.create (module Tid) in
             EHashtbl.set inner ~key:fallthrough_tid ~data:restored;
             EHashtbl.set !(ctx.edge_sp_restores) ~key:sub_tid ~data:inner);
        (match get_local ctx fallthrough_tid sp_key with
         | None -> insert_local ctx fallthrough_tid sp_key restored
         | Some _ -> ());
        return ()

let create_call_args blk_tid llvm_builder call_tid fr =
  let open KB in
  let* ctx, llvm_ctx = emit_env () in
  let args = get_args ctx call_tid in
  let extern = is_extern ctx call_tid in
  KB.List.map args ~f:(fun arg ->
      let exp = Arg.rhs arg in
      if Var.same (Arg.lhs arg) Convutils.hike_window_var then
        (* The caller-window base is the caller's SP at the call: the
           outgoing stores land at SP-relative addresses, so the
           callee's slot k sits at window + k (T4). *)
        (match get_local ctx blk_tid ctx.Convutils.sp with
         | Some v -> return v
         | None ->
             let* llvm_ctx = Context.get llvm_ctx_var in
             return @@ Llvm.undef (Llvm.i64_type llvm_ctx))
      else if
        Base.String.is_prefix (Var.name (Arg.lhs arg)) ~prefix:"hike_slot"
      then
        (* A promoted slot argument: the site's proven outgoing store,
           whose value the store's own emission recorded (T4b) — a site
           storing fewer slots leaves the rest unpassed (reading an
           unpassed arg is UB in the binary too). *)
        let name = Var.name (Arg.lhs arg) in
        let i =
          int_of_string @@ String.sub name 9 (String.length name - 9)
        in
        let stored =
          match Core.Map.find fr.outgoing blk_tid with
          | Some site ->
              Base.List.Assoc.find ~equal:Int.equal site.Convutils.site_slots i
          | None -> None
        in
        (match Base.Option.bind stored ~f:(fun dtid ->
                     EHashtbl.find fr.store_vals dtid) with
         | Some v ->
             let ty = Llvm.type_of v in
             let v =
               match Llvm.classify_type ty with
               | Llvm.TypeKind.Integer ->
                   let bits = Llvm.integer_bitwidth ty in
                   if bits = 64 then v
                   else if bits > 64 then
                     Llvm.build_trunc v (Llvm.i64_type llvm_ctx) ""
                       llvm_builder
                   else
                     Llvm.build_zext v (Llvm.i64_type llvm_ctx) ""
                       llvm_builder
               | _ -> v
             in
             return v
         | None ->
             let* llvm_ctx = Context.get llvm_ctx_var in
             return @@ Llvm.undef (Llvm.i64_type llvm_ctx))
      else if extern && is_fp_param (Arg.lhs arg) then
        (* Lowers YMM args to doubles for externs. *)
        let* v = create_exp llvm_builder blk_tid exp in
        let* llvm_ctx = Context.get llvm_ctx_var in
        let* v =
          if Llvm.integer_bitwidth (Llvm.type_of v) = 256 then
            KB.return
            @@ Llvm.build_trunc v (Llvm.i64_type llvm_ctx) "" llvm_builder
          else KB.return v
        in
        return
        @@ Llvm.build_bitcast v (Llvm.double_type llvm_ctx) "" llvm_builder
      else
        let* arg = create_exp llvm_builder blk_tid exp in
        return arg)
(* Sub declarations (shared by the definition and call lanes). *)



(* FP return width. *)
type fp_ret_kind = FpFloat | FpDouble | FpLongDouble

(* Double-returning libm names. *)
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

(* Module-init membership sets for the extern-float classifier. *)
let fp_double_libm_set = Base.Set.of_list (module Base.String) fp_double_libm
let fp_double_parsing_set = Base.Set.of_list (module Base.String) fp_double_parsing
let fp_float_parsing_set = Base.Set.of_list (module Base.String) fp_float_parsing
let fp_longdouble_parsing_set = Base.Set.of_list (module Base.String) fp_longdouble_parsing

let strip_at (name : string) : string =
  if String.length name > 0 && name.[0] = '@' then
    String.sub name 1 (String.length name - 1)
  else name

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

(* Ret-type constructor shared by declarations and definitions. *)
let ret_type_of_rets rets =
  let open KB in
  let* llvm_ctx = Context.get llvm_ctx_var in
  match rets with
  | [] -> return @@ Llvm.void_type llvm_ctx
  | [ ret ] -> var_lltype (Arg.lhs ret)
  | rets ->
      let* rets_typs =
        KB.List.map rets ~f:(fun ret -> var_lltype (Arg.lhs ret))
      in
      return @@ Llvm.struct_type llvm_ctx (Array.of_list rets_typs)

(* Registers a declared/defined function in the emit context. *)
let register_fn ctx sub_tid fn fn_typ =
  ctx.Convutils.ll_funcs :=
    Core.Map.add_exn !(ctx.Convutils.ll_funcs) ~key:sub_tid ~data:(fn, fn_typ)

let create_ret_type sub_tid =
  let open KB in
  let* ctx, llvm_ctx = emit_env () in
  match fp_ret_kind_of_extern ctx sub_tid with
  | Some kind -> return @@ fp_lltype llvm_ctx kind
  | None -> ret_type_of_rets (get_rets ctx sub_tid)

let create_arg_types sub_tid =
  let open KB in
  let* ctx, llvm_ctx = emit_env () in
  let args = get_args ctx sub_tid in
  KB.List.map args ~f:(fun arg ->
      let var = Arg.lhs arg in
      if Arg.intent arg = Some Both then return @@ Llvm.pointer_type llvm_ctx
      else if is_extern ctx sub_tid && is_fp_param var then
        return @@ Llvm.double_type llvm_ctx
      else var_lltype var)

let set_arg_names_of args fn =
  Base.List.iteri args ~f:(fun i arg ->
      let param = Llvm.param fn i in
      Llvm.set_value_name (Var.name (Arg.lhs arg)) param)

let set_arg_attrs_of fn args =
  let open KB in
  let* llvm_ctx = Context.get llvm_ctx_var in
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
                 (Llvm.integer_type llvm_ctx ctx.Convutils.ptrsize)
                 "" llvm_builder
           | _ -> param
         in
         insert_local ctx blk_tid (Arg.lhs arg) value)
       fn

let create_fun_declaration sub_tid =
  let open KB in
  let* llvm_module = Context.get llvm_module_var in
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
  let* llvm_ctx = Context.get llvm_ctx_var in
  let* llvm_module = Context.get llvm_module_var in
  let* ctx = Context.get emit_ctx_var in
  (* Uses explicit rets/args. *)
  let* ret_typ = ret_type_of_rets rets in
  let* args_typ =
    KB.List.map args ~f:(fun arg ->
        let var = Arg.lhs arg in
        if Arg.intent arg = Some Both then return @@ Llvm.pointer_type llvm_ctx
        else var_lltype var)
  in
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
  match Core.Map.find !(ctx.Convutils.ll_funcs) tid with
  | Some v -> return v
  | None ->
      let* _ = create_fun_declaration tid in
      return @@ Core.Map.find_exn !(ctx.Convutils.ll_funcs) tid

(* Binds a call's aggregate return into its ret lanes. *)
let bind_extracted_rets ctx blk_tid llvm_builder rets ret_struct =
  Base.List.iteri rets ~f:(fun i ret ->
      let ret_val = Llvm.build_extractvalue ret_struct i "" llvm_builder in
      insert_local ctx blk_tid (Arg.lhs ret) ret_val)

(* Finishes a call with its fallthrough edge. *)
let finish_call llvm_builder ctx fallthrough =
  let open KB in
  match fallthrough with
  | Some ft ->
      let bb = get_bb ctx ft in
      ignore (Llvm.build_br bb llvm_builder);
      return ()
  | None ->
      ignore (Llvm.build_unreachable llvm_builder);
      return ()

let create_func_call ?(emit_unreachable = true) llvm_builder blk_tid sub
    fallthrough target fr =
  let open KB in
  let* ctx, llvm_ctx = emit_env () in
  let* args = create_call_args blk_tid llvm_builder target fr in
  let rets = get_rets ctx target in
  let* fn, fn_typ = get_func target in
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
            | _ -> ())
       | FpFloat | FpDouble ->
           let d =
             Llvm.build_fpcast ret_val (Llvm.double_type llvm_ctx) "" llvm_builder
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
            | _ -> ()))
  | _, [] ->
      Llvm.build_call fn_typ fn (Array.of_list args) "" llvm_builder |> ignore
  | _, [ ret ] ->
      let ret_var =
        Llvm.build_call fn_typ fn (Array.of_list args) "" llvm_builder
      in
      Llvm.add_call_site_attr ret_var
        (Llvm.create_enum_attr llvm_ctx "zeroext" 0L)
        Llvm.AttrIndex.Return;
      insert_local ctx blk_tid (Arg.lhs ret) ret_var
  | _, rets ->
      let ret_struct =
        Llvm.build_call fn_typ fn (Array.of_list args) "" llvm_builder
      in
      bind_extracted_rets ctx blk_tid llvm_builder rets ret_struct);
  (match fallthrough with
  | Some fallthrough ->
      let* () = restore_sp_after_call llvm_builder ctx blk_tid fr fallthrough in
      finish_call llvm_builder ctx (Some fallthrough)
  | None ->
      if emit_unreachable then finish_call llvm_builder ctx None
      else return ())

(* The Resolved Call Site class and the pointer-call class (T4): the
   VSA's singleton resolution calls the promoted body directly; every
   other site takes the pointer call through the synthetic indirect
   signature (which carries the caller-window base). *)
let create_indirect_call llvm_builder blk_tid sub (j : jmp term) fr =
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
  match Core.Map.find fr.resolved (Term.tid j) with
  | Some (Some target_tid) ->
      (* A Resolved Call Site (T4): the target is provably a singleton
         lifted sub — the direct call goes through its promoted
         signature. *)
      create_func_call llvm_builder blk_tid sub (Some fallthrough) target_tid fr
  | _ ->
      (* The pointer call: bounded multi-target sets, foreign
         addresses, and unresolvable targets.  The pointer lands in
         the Thunk of a promoted target (address rendering), or in the
         target's existing memory convention. *)
      let* target_exp = create_exp llvm_builder blk_tid target in
      let* func_ptr = Bil2llvm_section.create_addr_ptr llvm_builder target_exp in
      let* fn, fn_typ = get_func icall_tid in
      let rets = get_rets ctx icall_tid in
      let* args =
        create_call_args blk_tid llvm_builder icall_tid fr
      in
      let ret_struct =
        Llvm.build_call fn_typ func_ptr (Array.of_list args) "" llvm_builder
      in
      bind_extracted_rets ctx blk_tid llvm_builder rets ret_struct;
      let* () = restore_sp_after_call llvm_builder ctx blk_tid fr fallthrough in
      finish_call llvm_builder ctx (Some fallthrough)

(* ------------------------------------------------------------------ *)
(* T4: the Thunk — the memory-convention twin of a promoted sub.       *)
(* ------------------------------------------------------------------ *)

(* The twin's LLVM name and its synthetic tid. *)
let thunk_name_of (sub_tid : tid) : string =
  sanitize_name (Tid.name sub_tid) ^ "_hike_thunk"

let thunk_tid_of (sub_tid : tid) : tid =
  Tid.for_name (Tid.name sub_tid ^ ":thunk")

(* A slot's offset in the caller window (SysV: [entry_rsp + 8 + 8*i]). *)
let slot_offset (i : int) : Int64.t = Int64.of_int (8 + (8 * i))

(* Emits the memory-convention twin of one promoted sub: it unpacks
   the window memory into the promoted body's slot parameters and
   forwards the register lanes.  INTERNAL linkage — the consumer's
   optimizer sees through it (inlines it into callers, devirtualizes
   provable pointers), so the twin costs nothing where the site
   resolves anyway.  Function-pointer data renders to the twin, so
   unresolvable sites stay sound.  No target ever demotes. *)
let create_thunk (sub_tid : tid) =
  let open KB in
  let* ctx = Context.get emit_ctx_var in
  let* llvm_ctx = Context.get llvm_ctx_var in
  let* llvm_module = Context.get llvm_module_var in
  let info = Hike_kb.info_of_sub sub_tid in
  let arity = info.Convutils.prom_arity in
  if arity = 0 || String.equal (Tid.name sub_tid) "@main" then
    KB.return ()
  else
    if Core.Map.mem !(ctx.Convutils.ll_funcs) (thunk_tid_of sub_tid) then
      KB.return ()
    else begin
      let args = get_args ctx sub_tid in
      let rets = get_rets ctx sub_tid in
        (* The twin carries the SYNTHETIC INDIRECT convention, exactly
           the signature the pointer call passes: every convention
           register lane (integer and vector) plus the caller-window
           base — so the twin's window param sits at the same position
           the icall type puts it. *)
        let conv = Abi.of_target ctx.Convutils.target in
        let twin_args =
          Base.List.map
            (conv.Abi.int_param_regs @ conv.Abi.vector_param_regs)
            ~f:(fun reg -> Arg.create ~intent:In reg (Var reg))
          @ [
              Arg.create ~intent:In Convutils.hike_window_var
                (Var Convutils.hike_window_var);
            ]
        in
        (* The lanes of [sub]'s own signature the twin forwards (by
           name, from the twin's params). *)
        let reg_args =
          Base.List.filter args ~f:(fun a ->
              let n = Var.name (Arg.lhs a) in
              (not (Base.String.is_prefix n ~prefix:"hike_slot"))
              && not (Var.same (Arg.lhs a) Convutils.hike_window_var))
        in
        let* ret_typ = ret_type_of_rets rets in
        let* arg_typs =
          KB.List.map twin_args ~f:(fun a ->
              if Var.same (Arg.lhs a) Convutils.hike_window_var then
                KB.return @@ Llvm.i64_type llvm_ctx
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
                     (slot_offset i) false)
                  "" builder
              in
              let ptr =
                Llvm.build_inttoptr addr (Llvm.pointer_type llvm_ctx) ""
                  builder
              in
              Llvm.build_load (Llvm.i64_type llvm_ctx) ptr "" builder)
        in
        (* Forward [sub]'s own register lanes by name from the twin's
           params, then the unpacked slots.  A lane outside the
           convention the twin carries is never passed by any caller —
           it reads undef, the model-ABI never-defined treatment. *)
        let param_named (v : var) : Llvm.llvalue =
          let n = Var.name v in
          match
            Base.List.findi twin_args ~f:(fun i a -> Var.name (Arg.lhs a) = n)
            |> Base.Option.map ~f:(fun (i, _) -> Llvm.param fn i)
          with
          | Some p -> p
          | None -> Llvm.undef (Llvm.i64_type llvm_ctx)
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
        (* Function-address rendering produces the twin (keyed by the
           sub's LLVM name). *)
        ctx.Convutils.thunks :=
          (sanitize_name (Tid.name sub_tid), fn) :: !(ctx.Convutils.thunks);
        KB.return ()
    end

let create_return blk_tid llvm_builder cur_sub =
  let open KB in
  let* ctx = Context.get emit_ctx_var in
  let* rets =
    KB.List.map (get_rets ctx (Term.tid cur_sub)) ~f:(fun ret ->
        (* Missing YMM0 reads yield undef. *)
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

(* Name of the trap function trap edges declare. *)
let trap_name = "llvm.trap"

(* Emits trap edges. *)
let create_interrupt llvm_builder =
  let open KB in
  let* llvm_ctx = Context.get llvm_ctx_var in
  let* llvm_module = Context.get llvm_module_var in
  let trap_ty = Llvm.function_type (Llvm.void_type llvm_ctx) [||] in
  let trap = Llvm.declare_function trap_name trap_ty llvm_module in
  ignore
    (Llvm.build_call trap_ty trap [||] "" llvm_builder);
  ignore (Llvm.build_unreachable llvm_builder);
  KB.return ()

(* Maps soft-float calls to native FP ops. *)
type native_fp = FMUL | FADD | FSUB | FDIV | FREM | SFLOAT | SINT | FORDER | FHLT | ISNAN

let fp_intrinsic_name = strip_at

let native_fp_op (name : string) : native_fp option =
  match fp_intrinsic_name name with
  (* Width-suffixed intrinsic names. *)
  | "intrinsic:fmul_rne_ieee754_binary_64" -> Some FMUL
  | "intrinsic:fmul_rne_ieee754_binary_32" -> Some FMUL
  | "intrinsic:fadd_rne_ieee754_binary_64" -> Some FADD
  | "intrinsic:fadd_rne_ieee754_binary_32" -> Some FADD
  | "intrinsic:fsub_rne_ieee754_binary_64" -> Some FSUB
  | "intrinsic:fsub_rne_ieee754_binary_32" -> Some FSUB
  | "intrinsic:fdiv_rne_ieee754_binary_64" -> Some FDIV
  | "intrinsic:fdiv_rne_ieee754_binary_32" -> Some FDIV
  | "intrinsic:frem_rne_ieee754_binary_64" -> Some FREM
  | "intrinsic:frem_rne_ieee754_binary_32" -> Some FREM
  | "intrinsic:forder_rne_ieee754_binary_64" -> Some FORDER
  | "intrinsic:forder_rne_ieee754_binary_32" -> Some FORDER
  (* NaN predicate via fcmp uno. *)
  | "intrinsic:is_nan_rne_ieee754_binary_64" -> Some ISNAN
  | "intrinsic:is_nan_rne_ieee754_binary_32" -> Some ISNAN
  | "intrinsic:is_nan_ieee754_binary" -> Some ISNAN
  | "intrinsic:is_nan_rne_ieee754_binary" -> Some ISNAN
  (* Unsuffixed compare names. *)
  | "intrinsic:forder_ieee754_binary" -> Some FORDER
  | "intrinsic:forder_rne_ieee754_binary" -> Some FORDER
  | "intrinsic:cast_sfloat_rne_ieee754_binary_64" -> Some SFLOAT
  | "intrinsic:cast_sint_rne_ieee754_binary_64" -> Some SINT
  (* Legacy unsuffixed names. *)
  | "intrinsic:fmul_rne_ieee754_binary" -> Some FMUL
  | "intrinsic:fadd_rne_ieee754_binary" -> Some FADD
  | "intrinsic:fsub_rne_ieee754_binary" -> Some FSUB
  | "intrinsic:fdiv_rne_ieee754_binary" -> Some FDIV
  | "intrinsic:frem_rne_ieee754_binary" -> Some FREM
  (* Halt uses the trap model. *)
  | "intrinsic:hlt" -> Some FHLT
  | _ -> None

(* The STATIC model interface of each mapped op: the input temps the call
   block must define, in order.  The name IS the interface fact — operand
   resolution reads these temps directly, never a signature-table fallback
   and never a register lane. *)
let fp_op_inputs = function
  | FMUL | FADD | FSUB | FDIV | FREM | FORDER ->
      [ "intrinsic:x0"; "intrinsic:x1" ]
  | SFLOAT | SINT | ISNAN -> [ "intrinsic:x0" ]
  | FHLT -> []

(* Tests for 32-bit sources. *)
(* Builds a width-aware FP binop. *)
(* Returns width-derived FP/int types. *)
let fp_ty_of (llvm_ctx : Llvm.llcontext) (w : int) :
    Llvm.lltype * Llvm.lltype =
  ( (if w <= 32 then Llvm.float_type llvm_ctx
     else Llvm.double_type llvm_ctx),
    (if w <= 32 then Llvm.i32_type llvm_ctx else Llvm.i64_type llvm_ctx) )

(* Integer width of a value, defaulting to a declared width. *)
let int_width_or default_w v =
  match Llvm.classify_type (Llvm.type_of v) with
  | Llvm.TypeKind.Integer -> Llvm.integer_bitwidth (Llvm.type_of v)
  | _ -> default_w

(* Bitcasts integer lanes to an FP type; other lanes pass through. *)
let bitcast_to_fp llvm_builder v fp_ty =
  if Llvm.classify_type (Llvm.type_of v) = Llvm.TypeKind.Integer then
    Llvm.build_bitcast v fp_ty "" llvm_builder
  else v

(* Coerces an integer value of known width to a lane width. *)
let coerce_int_width llvm_ctx llvm_builder ~bits v w =
  if bits = w then v
  else if bits > w then
    Llvm.build_trunc v (Llvm.integer_type llvm_ctx w) "" llvm_builder
  else Llvm.build_zext v (Llvm.integer_type llvm_ctx w) "" llvm_builder

let build_fp_binop llvm_builder op a b ~(w : int) =
  let open KB in
  let* llvm_ctx = Context.get llvm_ctx_var in
  let fp_ty, ret_ty = fp_ty_of llvm_ctx w in
  let da = bitcast_to_fp llvm_builder a fp_ty in
  let db = bitcast_to_fp llvm_builder b fp_ty in
  let d =
    match op with
    | FMUL -> Llvm.build_fmul da db "" llvm_builder
    | FADD -> Llvm.build_fadd da db "" llvm_builder
    | FSUB -> Llvm.build_fsub da db "" llvm_builder
    | FDIV -> Llvm.build_fdiv da db "" llvm_builder
    | FREM -> Llvm.build_frem da db "" llvm_builder
    | SFLOAT | SINT | FORDER | FHLT | ISNAN -> assert false
  in
  return
  @@ Llvm.build_bitcast d ret_ty "" llvm_builder

(* Operand temps of a block indexed by base var, last def wins. *)
let temp_rhss_of_blk (blk : blk term) : exp Var.Map.t =
  Term.enum def_t blk
  |> Seq.fold ~init:Var.Map.empty ~f:(fun m d ->
         Core.Map.set m ~key:(Var.base (Def.lhs d)) ~data:(Def.rhs d))

(* Derives intrinsic widths from types. *)
let fp_intrinsic_sizes (args : Arg.t list) (rets : Arg.t list) :
    int * int =
  let arg_w (i : int) : int =
    match Base.List.nth args i with
    | Some a -> (
        match Var.typ (Arg.lhs a) with Type.Imm w -> w | _ -> 64)
    | None -> 64
  in
  let res_w =
    match rets with
    | r :: _ -> (
        match Var.typ (Arg.lhs r) with Type.Imm w -> w | _ -> 64)
    | [] -> 64
  in
  (arg_w 0, res_w)

(* Emits native FP ops inline. *)
let create_native_fp_call llvm_builder blk_tid blk call op =
  let open KB in
  match op with
  | FHLT ->
      (* Halt traps without binding results or emitting fallthrough. *)
      create_interrupt llvm_builder
  | FMUL | FADD | FSUB | FDIV | FREM | SFLOAT | SINT | FORDER | ISNAN ->
      let* llvm_ctx = Context.get llvm_ctx_var in
      let* ctx = Context.get emit_ctx_var in
  let fallthrough = Option.map label_tid (Call.return call) in
  let target = Call.target call |> label_tid in
  let args = get_args ctx target in
  (* Widths come from declared types. *)
  let rets = get_rets ctx target in
  let in_w, res_w = fp_intrinsic_sizes args rets in
  (* Operand temps indexed once per call. *)
  let temp_rhss = temp_rhss_of_blk blk in
  let arg_value (i : int) : Llvm.llvalue KB.t =
    (* Resolves operands from the op's STATIC input temps: the mapped name
       is the interface, so the [intrinsic:xN] temp the block defined IS
       the operand — a signature-table miss can never substitute a
       register lane for it. *)
    let name = Base.List.nth_exn (fp_op_inputs op) i in
    let av = Var.create ~is_virtual:false ~fresh:false name (Type.Imm 64) in
    match Core.Map.find temp_rhss av with
    | Some rhs -> create_exp llvm_builder blk_tid rhs
    | None -> create_exp llvm_builder blk_tid (Bil.Var av)
  in
  (* Integer width of a value, defaulting to the declared input width. *)
  let w_of = int_width_or in_w in
  let result =
    match op with
    | FMUL | FADD | FSUB | FDIV | FREM ->
        (* Operand width comes from values. *)
        let* a = arg_value 0 in
        let* b = arg_value 1 in
        let w = min (w_of a) (w_of b) in
        build_fp_binop llvm_builder op a b ~w
    | SFLOAT ->
        (* Int-to-FP casts: the source width IS the operand value's own
           LLVM type — the lifter's extract/cast chain built it (an
           [x0 := 31:0[RAX]] read is i32; a [:u64] load is i64).  No BIL
           inspection, no slot lists, no width tests: [sitofp] converts at
           the operand's own width. *)
        let* x = arg_value 0 in
        (* Converts use result width. *)
        let tgt_fp_ty, tgt_lane_ty = fp_ty_of llvm_ctx res_w in
        let* d =
          KB.return
          @@ Llvm.build_sitofp x tgt_fp_ty "" llvm_builder
        in
        return
        @@ Llvm.build_bitcast d tgt_lane_ty "" llvm_builder
    | SINT ->
        (* FP-to-int casts use operand width. *)
        let* x = arg_value 0 in
        let src_w = int_width_or in_w x in
        let src_fp_ty, _ = fp_ty_of llvm_ctx src_w in
        let _, res_lane_ty = fp_ty_of llvm_ctx res_w in
        let* d =
          KB.return
          @@ Llvm.build_bitcast x src_fp_ty "" llvm_builder
        in
        let* r =
          KB.return
          @@ Llvm.build_fptosi d res_lane_ty "" llvm_builder
        in
        return r
    | FORDER ->
        (* Ordered less-than via fcmp olt. *)
        let* a = arg_value 0 in
        let* b = arg_value 1 in
        let w = min (w_of a) (w_of b) in
        let src_fp_ty, _ = fp_ty_of llvm_ctx w in
        let* p =
          KB.return
          @@ Llvm.build_fcmp Llvm.Fcmp.Olt
               (bitcast_to_fp llvm_builder a src_fp_ty)
               (bitcast_to_fp llvm_builder b src_fp_ty)
               "" llvm_builder
        in
        return @@ Llvm.build_zext p (Llvm.i64_type llvm_ctx) "" llvm_builder
    | ISNAN ->
        (* NaN test via fcmp uno. *)
        let* x = arg_value 0 in
        let w = int_width_or in_w x in
        let src_fp_ty, _ = fp_ty_of llvm_ctx w in
        let xf = bitcast_to_fp llvm_builder x src_fp_ty in
        let* p =
          KB.return
          @@ Llvm.build_fcmp Llvm.Fcmp.Uno xf xf "" llvm_builder
        in
        return @@ Llvm.build_zext p (Llvm.i64_type llvm_ctx) "" llvm_builder
    | FHLT -> assert false
  in
  let* r = result in
  (match rets with
   | [ ret ] ->
     (* Binds the primary ret lane width-aware. *)
     let lane_w =
       match Var.typ (Arg.lhs ret) with Type.Imm w -> w | _ -> 64
     in
     let r_bits = try Llvm.integer_bitwidth (Llvm.type_of r) with _ -> 64 in
     let r_lane = coerce_int_width llvm_ctx llvm_builder ~bits:r_bits r lane_w in
     insert_local ctx blk_tid (Arg.lhs ret) r_lane;
     (* Binds remaining ret lanes width-adjusted. *)
     Base.List.iter rets ~f:(fun ret2 ->
         if Var.same (Arg.lhs ret2) (Arg.lhs ret) then ()
         else begin
           let lw =
             match Var.typ (Arg.lhs ret2) with
             | Type.Imm w -> w
             | _ -> 64
           in
           insert_local ctx blk_tid (Arg.lhs ret2)
             (coerce_int_width llvm_ctx llvm_builder ~bits:r_bits r lw)
         end)
   | _ -> ());
  finish_call llvm_builder ctx fallthrough

(* Emits unmapped intrinsics as extern calls. *)
let create_external_intrinsic_call llvm_builder blk_tid call name =
  let open KB in
  let* llvm_ctx = Context.get llvm_ctx_var in
  let* llvm_module = Context.get llvm_module_var in
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

let create_call llvm_builder blk_tid blk sub call fr =
  let open KB in
  let* ctx = Context.get emit_ctx_var in
  let target = Call.target call |> label_tid in
  let name = Tid.name target |> fp_intrinsic_name in
  if Base.String.is_prefix (Tid.name target) ~prefix:"@interrupt:" then
    (* Interrupt calls trap. *)
    create_interrupt llvm_builder
  else
    match native_fp_op (Tid.name target) with
    | Some op -> create_native_fp_call llvm_builder blk_tid blk call op
    | None ->
        (* Unmapped intrinsics warn and degrade. *)
        if Convutils.is_intrinsic_name name then begin
          Hike_diag.warn
            "guarded: unmapped intrinsic call: %s (in sub %s) - emitting as external; result lanes are poison"
            name (Tid.name (Term.tid sub));
          create_external_intrinsic_call llvm_builder blk_tid call name
        end
        else (
        (* PLT callers pass through returns. *)
        match Call.return call with
        | Some l ->
            let fallthrough = Some (label_tid l) in
            create_func_call llvm_builder blk_tid sub fallthrough target fr
        | None ->
            if Bil2llvm_mem.is_plt_trampoline ctx sub then
              let* () =
                create_func_call ~emit_unreachable:false llvm_builder blk_tid sub
                  None target fr
              in
              create_return blk_tid llvm_builder sub
            else create_func_call llvm_builder blk_tid sub None target fr)
