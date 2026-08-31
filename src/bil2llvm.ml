open Bap.Std.Bil.Types
open Bap.Std
open Targetutils
open Convutils
module KB = Bap_knowledge.Knowledge
module Vsa = Cbat_vsa
module AI = Cbat_vsa.AI
module Mem = Cbat_vsa.Mem
module Ws = Cbat_clp_set_composite

(* The per-run emission context ([Convutils.emit_ctx], threaded as a KB Context var [emit_ctx_var]): the old module-level refs (ll_funcs / copy_reloc_addrs / symtab_ref / section_remap_ref / text_section_ref / guarded_warned) now live in that one record. *)

(* [lookup_native_fn llvm_module v]: The LLVM function whose object symbol starts at the native address [v] (the symtab [find_by_start]); None when [v] is not a function entry (or there is no symtab). *)
let lookup_native_fn ctx llvm_module v =
  match ctx.Convutils.symtab with
  | Some symtab -> (
      match Symtab.find_by_start symtab (Word.of_int64 ~width:64 v) with
      | Some (name, _, _) -> Llvm.lookup_function name llvm_module
      | None -> None)
  | None -> None

(* [remap_native_addr llvm_ctx llvm_module v]: a native address [v] to its lifted representation — a function entry (the symtab) as [ptrtoint @function], or a data-section address as [ptrtoint (@section + offset)]. None when [v] is not a known native address (raw data). *)
let remap_native_addr ctx llvm_ctx llvm_module v =
  match lookup_native_fn ctx llvm_module v with
  | Some f -> Some (Llvm.const_ptrtoint f (Llvm.i64_type llvm_ctx))
  | None -> (
      match
        Base.List.find ctx.Convutils.section_remap ~f:(fun (lo, hi, _) ->
            Int64.compare lo v <= 0 && Int64.compare v hi <= 0)
      with
      | Some (lo, _, g) ->
          let offset =
            Llvm.const_of_int64 (Llvm.i64_type llvm_ctx)
              (Int64.sub v lo) false
          in
          let gep =
            Llvm.const_in_bounds_gep (Llvm.i8_type llvm_ctx) g
              [| offset |]
          in
          Some (Llvm.const_ptrtoint gep (Llvm.i64_type llvm_ctx))
      | None -> None)

(* [create_section_global]: The DATA-section global, typed [n x i64] so the pointer slots can hold [ptrtoint] constants (the byte layout is preserved — the [n x i64] array's bytes are the section bytes in little-endian — and the byte-offset GEP loads ([resolve_addr]) read them unchanged). *)
let create_section_global llvm_ctx llvm_module size name ~is_const =
  let n64 = (size + 7) / 8 in
  let ret =
    Llvm.declare_global
      (Llvm.array_type (Llvm.i64_type llvm_ctx) n64)
      name llvm_module
  in
  Llvm.set_global_constant is_const ret;
  ret

(* [text_load_constant]: The inline .text constant-pool -- see [text_section_ref]. *)
let text_load_constant ctx llvm_builder llvm_ctx llvm_module addr w =
  let v = Word.to_int64_exn addr in
  match ctx.Convutils.text_section with
  | Some (arr, tmin, tmax)
    when Int64.compare v tmin >= 0 && Int64.compare v tmax <= 0 ->
      let off = Int64.to_int (Int64.sub v tmin) in
      let bytes = ref 0L in
      for i = 0 to (w / 8) - 1 do
        let b =
          if off + i < Array.length arr then
            Int64.of_int arr.(off + i) else 0L
        in
        bytes :=
          Int64.logor !bytes
            (Int64.shift_left b (i * 8))
      done;
      let remapped = lookup_native_fn ctx llvm_module !bytes in
      let c =
        match remapped with
        | Some f -> Llvm.const_ptrtoint f (Llvm.i64_type llvm_ctx)
        | None ->
            Llvm.const_of_int64 (Llvm.integer_type llvm_ctx w) !bytes false
      in
      Some c
  | _ -> None

(* [set_section_initializer]: the remapped i64-array initializer for the data-section global [g] built from the section BYTES [arr] (native base [min_addr]). Each 8-byte little-endian slot whose value is a native address is rewritten to the lifted address. *)
let set_section_initializer ctx llvm_ctx llvm_module g arr min_addr =
  let n64 = (Array.length arr + 7) / 8 in
  let slot_at i =
    let v = ref 0L in
    for k = 7 downto 0 do
      let b =
        if (i * 8) + k < Array.length arr then
          Int64.of_int arr.((i * 8) + k)
        else 0L
      in
      v := Int64.logor (Int64.shift_left !v 8) b
    done;
    match remap_native_addr ctx llvm_ctx llvm_module !v with
    | Some c -> c
    | None ->
        Llvm.const_of_int64 (Llvm.i64_type llvm_ctx) !v false
  in
  let slots = Array.init n64 slot_at in
  Llvm.set_initializer (Llvm.const_array (Llvm.i64_type llvm_ctx) slots) g

(* The per-sub FRAME state, threaded through the emission (no global refs — a failure between reset and bind cannot leave stale state): - [frame]/[min_lo]: the per-sub alloca + its cell origin (the negative cells — the. *)
type sub_frame = {
  frame : Llvm.llvalue option;
  min_lo : int64;
  (* [anchor_idx]: The ANCHOR's frame-relative byte index. *)
  anchor_idx : int64;
  anchor_i64 : Llvm.llvalue;
  stack : Llvm.llvalue option;
  regions : (Convutils.region * Llvm.llvalue) list;
  is_precise : bool;
}
let llvm_ctx_var : Llvm.llcontext KB.Context.var =
  KB.Context.declare ~package:"hike" "llvm-ctx" (KB.return (Obj.magic 0))

let llvm_module_var : Llvm.llmodule KB.Context.var =
  KB.Context.declare ~package:"hike" "llvm-module" (KB.return (Obj.magic 0))

let section_list_var : section list KB.Context.var =
  KB.Context.declare ~package:"hike" "section-list" (KB.return [])

(* the per-run emission context: [Convutils.empty_emit_ctx ()] is only the declare-time default; the convlir pass fills the config and threads the SAME record through [init_subs] + [create_prog] via [KB.Context.with_var emit_ctx_var ctx]. *)
let emit_ctx_var : Convutils.emit_ctx KB.Context.var =
  KB.Context.declare ~package:"hike" "emit-ctx"
    (KB.return (Convutils.empty_emit_ctx ()))

let typ_lltype_m typ =
  let open KB in
  let* llvm_ctx = Context.get llvm_ctx_var in
  match typ with
  | Imm n -> return @@ Llvm.integer_type llvm_ctx n
  | _ -> return @@ Llvm.pointer_type llvm_ctx

let var_lltype var = typ_lltype_m (Var.typ var)

(* [is_fp_param v]: The model's FP argument registers (the 256-bit YMM0-7) — the extern-call fallback signature carries them so the FP args of a printf-style call reach the real ABI's XMM slots. *)
let is_fp_param (v : var) : bool =
  Base.String.is_prefix (Var.name (Var.base v)) ~prefix:"YMM"

let is_extern ctx (sub_tid : tid) : bool =
  not (Core.Map.mem ctx.Convutils.subs sub_tid)

(* [fp_ret_kind]: The return width of a floating-point-returning EXTERN. *)
type fp_ret_kind = FpFloat | FpDouble | FpLongDouble

(* The DOUBLE-returning libm base names; the float ("f" suffix) and long-double ("l" suffix) variants are derived by suffix. *)
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

let strip_at (name : string) : string =
  if String.length name > 0 && name.[0] = '@' then
    String.sub name 1 (String.length name - 1)
  else name

let fp_ret_kind_of_extern ctx (sub_tid : tid) : fp_ret_kind option =
  if not (is_extern ctx sub_tid) then None
  else
    let name = strip_at (Tid.name sub_tid) in
    let mem = Base.List.mem ~equal:String.equal in
    if mem fp_double_libm name then Some FpDouble
    else if mem fp_double_parsing name then Some FpDouble
    else if mem fp_float_parsing name then Some FpFloat
    else if mem fp_longdouble_parsing name then Some FpLongDouble
    else if String.length name > 1 then
      let last = name.[String.length name - 1] in
      let base = String.sub name 0 (String.length name - 1) in
      if last = 'f' && mem fp_double_libm base then Some FpFloat
      else if last = 'l' && mem fp_double_libm base then Some FpLongDouble
      else None
    else None

let fp_lltype llvm_ctx = function
  | FpFloat -> Llvm.float_type llvm_ctx
  | FpDouble -> Llvm.double_type llvm_ctx
  | FpLongDouble -> Llvm.x86fp80_type llvm_ctx

let create_ret_type sub_tid =
  let open KB in
  let* llvm_ctx = Context.get llvm_ctx_var in
  let* ctx = Context.get emit_ctx_var in
  match fp_ret_kind_of_extern ctx sub_tid with
  | Some kind -> return @@ fp_lltype llvm_ctx kind
  | None ->
      let rets = get_rets ctx sub_tid in
      (match rets with
       | [] -> return @@ Llvm.void_type llvm_ctx
       | [ ret ] -> var_lltype (Arg.lhs ret)
       | rets ->
           let* rets_typs =
             KB.List.map rets ~f:(fun ret -> var_lltype (Arg.lhs ret))
           in
           return @@ Llvm.struct_type llvm_ctx (Array.of_list rets_typs))

let create_arg_types sub_tid =
  let open KB in
  let* llvm_ctx = Context.get llvm_ctx_var in
  let* ctx = Context.get emit_ctx_var in
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
  let* llvm_ctx = Context.get llvm_ctx_var in
  let* ctx = Context.get emit_ctx_var in
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
  (* the EXTERN declares are VARIADIC (printf-style: the real callee reads its FP args from the XMM save area per [%al]; LLVM computes the vector-arg count [al] for a call to a vararg function from the double-typed FP args). The model subs' stored signatures stay fixed-arity. *)
  let fn_typ =
    if is_extern ctx sub_tid then
      Llvm.var_arg_function_type ret_typ (Array.of_list args_typ)
    else Llvm.function_type ret_typ (Array.of_list args_typ)
  in
  let fn =
    Llvm.declare_function (sanitize_name @@ Tid.name sub_tid) fn_typ llvm_module
  in
  ctx.Convutils.ll_funcs :=
    Core.Map.add_exn !(ctx.Convutils.ll_funcs) ~key:sub_tid ~data:(fn, fn_typ);
  return ()

let create_fun sub_tid ~rets ~args =
  let open KB in
  let* llvm_ctx = Context.get llvm_ctx_var in
  let* llvm_module = Context.get llvm_module_var in
  let* ctx = Context.get emit_ctx_var in
  (* The ret/arg types derive from the EXPLICIT [rets]/[args] (computed by the caller in [compute_sub_sig]) — NOT via [get_rets]/[get_args], which would read [ctx.subs] before this sub's signature has been added (the. *)
  let* ret_typ =
    match rets with
    | [] -> return @@ Llvm.void_type llvm_ctx
    | [ ret ] -> var_lltype (Arg.lhs ret)
    | rets ->
        let* rets_typs =
          KB.List.map rets ~f:(fun ret -> var_lltype (Arg.lhs ret))
        in
        return @@ Llvm.struct_type llvm_ctx (Array.of_list rets_typs)
  in
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
  ctx.Convutils.ll_funcs :=
    Core.Map.add_exn !(ctx.Convutils.ll_funcs) ~key:sub_tid ~data:(fn, fn_typ);
  set_arg_attrs_of fn args >>= return

(* LLVM requires both operands of a binop to have the same type, while BIL allows operations on expressions of different sizes. *)
let coerce_to_same_type llvm_builder op llvm_val1 llvm_val2 =
  let open KB in
  let is_integer v =
    match Llvm.classify_type (Llvm.type_of v) with
    | Llvm.TypeKind.Integer -> true
    | _ -> false
  in
  let typ1 = Llvm.type_of llvm_val1 in
  let typ2 = Llvm.type_of llvm_val2 in
  if (not (is_integer llvm_val1)) || not (is_integer llvm_val2) then
    return (llvm_val1, llvm_val2)
  else
    let size1 = Llvm.integer_bitwidth typ1 in
    let size2 = Llvm.integer_bitwidth typ2 in
    if size1 = size2 then return (llvm_val1, llvm_val2)
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
      return (llvm_val1, llvm_val2)

let create_binop llvm_builder (op, llvm_val1, llvm_val2) =
  let open KB in
  let* llvm_val1, llvm_val2 =
    coerce_to_same_type llvm_builder op llvm_val1 llvm_val2
  in
  return
  @@
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
  KB.return
  @@
  match op with
  | NEG -> Llvm.build_neg llvm_val "" llvm_builder
  | NOT -> Llvm.build_not llvm_val "" llvm_builder

(* [exp_size e]: The bitwidth of a BIL expression, used by the [Concat] emission to detect ZERO-WIDTH operands (the x86 lifter's `high:0[x]`/`low:0[x]` empty-extract concat patterns — an `Extract (hi, lo, _)` with hi < lo contributes 0. *)
let rec exp_size (e : exp) : int =
  match e with
  | Bil.Extract (hi, lo, _) -> max 0 (hi - lo + 1)
  | Bil.Cast (_, i, _) -> i
  | _ -> (
    match Type.infer e with
    | Ok (Type.Imm n) -> n
    | _ -> 0)

let create_concat llvm_builder (llvm_var1, llvm_var2) =
  let open KB in
  let* llvm_ctx = Context.get llvm_ctx_var in
  let llvm_var1_size = Llvm.type_of llvm_var1 |> Llvm.integer_bitwidth in
  let llvm_var2_size = Llvm.type_of llvm_var2 |> Llvm.integer_bitwidth in
  let result_typ =
    Llvm.integer_type llvm_ctx (llvm_var1_size + llvm_var2_size)
  in
  let llvm_var2_sizeof = Llvm.const_int result_typ llvm_var2_size in
  let zext_var1 = Llvm.build_zext llvm_var1 result_typ "" llvm_builder in
  let shl_var1 = Llvm.build_shl zext_var1 llvm_var2_sizeof "" llvm_builder in
  let zext_var2 = Llvm.build_zext llvm_var2 result_typ "" llvm_builder in
  return @@ Llvm.build_or shl_var1 zext_var2 "" llvm_builder

let create_extract llvm_builder (hi, lo, llvm_var) =
  let open KB in
  let* llvm_ctx = Context.get llvm_ctx_var in
  let width = Llvm.integer_bitwidth (Llvm.type_of llvm_var) in
  let result_size = hi - lo + 1 in
  if lo >= width then
    (* the extract lies entirely ABOVE the operand (e.g. bits 63..32 of a 32-bit value) — the result is zero. *)
    return @@ Llvm.const_int (Llvm.integer_type llvm_ctx result_size) 0
  else
    let temp_var =
      Llvm.build_lshr llvm_var
        (Llvm.const_int (Llvm.type_of llvm_var) lo)
        "" llvm_builder
    in
    if result_size >= width then
      (* the extract range WIDENS the operand (e.g. `63:0[<32-bit>]` — BIL's Extract zero-extends past the operand's width) — zext, never a trunc. *)
      return
      @@ Llvm.build_zext temp_var
           (Llvm.integer_type llvm_ctx result_size) "" llvm_builder
    else
      return
      @@ Llvm.build_trunc temp_var
           (Llvm.integer_type llvm_ctx result_size) "" llvm_builder

let resolve_addr llvm_builder addr =
  let open KB in
  let* llvm_ctx = Context.get llvm_ctx_var in
  let* sections = Context.get section_list_var in
  let section =
    Base.List.find sections ~f:(fun section ->
        Word.between ~low:section.min_addr addr ~high:section.max_addr)
  in
  match section with
  | None -> failwith "load: addr not found"
  | Some section ->
      let offset =
        Llvm.const_of_int64 (Llvm.i64_type llvm_ctx)
          (Word.sub addr section.min_addr |> Word.to_int64_exn)
          false
      in
      return
      @@ Llvm.build_gep (Llvm.i8_type llvm_ctx) section.base [| offset |] ""
           llvm_builder

let create_inttoptr llvm_builder llvm_val =
  let open KB in
  let* llvm_ctx = Context.get llvm_ctx_var in
  return
  @@ Llvm.build_inttoptr llvm_val (Llvm.pointer_type llvm_ctx) "" llvm_builder

(* [section_load]: the section-GEP load (with the copy-relocation through-load for bss) -- the fallback of [create_load] / [create_rip_relative_addr] when the address is NOT in the inline .text constant-pool. *)
let section_load llvm_builder llvm_ctx addr addr_i64 size =
  let open KB in
  let* ctx = Context.get emit_ctx_var in
  let* base = resolve_addr llvm_builder addr in
  if
    Base.List.exists ctx.Convutils.copy_relocs ~f:(fun a ->
        Int64.equal a addr_i64)
  then
    (* the COPY-RELOCATED slot: the stored value is [ptrtoint (@extern)] -- load the pointer, then load the real value through it (the stdout FILE* -- the copy relocation's content). *)
    let p =
      Llvm.build_load (Llvm.i64_type llvm_ctx) base "" llvm_builder
    in
    let pp =
      Llvm.build_inttoptr p (Llvm.pointer_type llvm_ctx) "" llvm_builder
    in
    return
    @@ Llvm.build_load (Llvm.integer_type llvm_ctx size) pp ""
         llvm_builder
  else
    return
    @@ Llvm.build_load (Llvm.integer_type llvm_ctx size) base ""
         llvm_builder

let create_load llvm_builder (addr, size) =
  let open KB in
  let* llvm_ctx = Context.get llvm_ctx_var in
  let* llvm_module = Context.get llvm_module_var in
  let* ctx = Context.get emit_ctx_var in
  let* sections = Context.get section_list_var in
  match Llvm.int64_of_const addr with
  | Some v ->
      (* the inline .text constant-pool: .text is NOT in [section_list] (no @text global), so read the stashed .text bytes first (function entries -> [ptrtoint @fn], data -> the inlined integer constant). *)
      let addr_w = Word.of_int64 ~width:64 v in
      let* pre =
        match
          text_load_constant ctx llvm_builder llvm_ctx llvm_module addr_w size
        with
        | Some c -> return c
        | None ->
            if
              Base.List.exists sections ~f:(fun section ->
                  Word.between ~low:section.min_addr addr_w
                    ~high:section.max_addr)
            then section_load llvm_builder llvm_ctx addr_w v size
            else
              let* ptr = create_inttoptr llvm_builder addr in
              return
              @@ Llvm.build_load (Llvm.integer_type llvm_ctx size) ptr ""
                   llvm_builder
      in
      return pre
  | _ ->
      (* addr is not a constant -> inttoptr + load. *)
      let* addr = create_inttoptr llvm_builder addr in
      (match Llvm.int64_of_const addr with
       | Some v -> Printf.eprintf "hike: create_load DYN addr=%Ld\n" v
       | None -> ());
      return
      @@ Llvm.build_load (Llvm.integer_type llvm_ctx size) addr ""
           llvm_builder
let create_store llvm_builder (llvm_var, addr) =
  let open KB in
  let* llvm_ctx = Context.get llvm_ctx_var in
  let* sections = Context.get section_list_var in
  match Llvm.int64_of_const addr with
  | Some v when
      Base.List.exists sections ~f:(fun section ->
          Word.between ~low:section.min_addr
            (Word.of_int64 ~width:64 v) ~high:section.max_addr)
    ->
      let* base = resolve_addr llvm_builder (Word.of_int64 ~width:64 v) in
      return @@ Llvm.build_store llvm_var base llvm_builder
  | _ ->
      let* addr = create_inttoptr llvm_builder addr in
      return @@ Llvm.build_store llvm_var addr llvm_builder

let create_cast llvm_builder (cast, i, llvm_val) =
  let open KB in
  let* llvm_ctx = Context.get llvm_ctx_var in
  let width = Llvm.integer_bitwidth (Llvm.type_of llvm_val) in
  let target = Llvm.integer_type llvm_ctx i in
  let extend cast =
    match cast with SIGNED -> Llvm.build_sext | _ -> Llvm.build_zext
  in
  let coerce cast v =
    if i > width then extend cast v target "" llvm_builder
    else if i < width then Llvm.build_trunc v target "" llvm_builder
    else v
  in
  match cast with
  | UNSIGNED -> return @@ coerce UNSIGNED llvm_val
  | SIGNED -> return @@ coerce SIGNED llvm_val
  | LOW -> return @@ coerce UNSIGNED llvm_val
  | HIGH ->
      let shift = max 0 (width - i) in
      let shifted =
        if shift > 0 then
          Llvm.build_lshr llvm_val
            (Llvm.const_int (Llvm.type_of llvm_val) shift) "" llvm_builder
        else llvm_val
      in
      return @@ coerce UNSIGNED shifted

let create_immidiate word =
  let open KB in
  let* llvm_ctx = Context.get llvm_ctx_var in
  let* llvm_module = Context.get llvm_module_var in
  let* ctx = Context.get emit_ctx_var in
  (* The NATIVE function-pointer remap: a constant that EXACTLY matches a symbol-table function entry (the native `atexit (close_stdout)` arg 0x401d80 — the `mov $0x401d80,%rdi` lift) is emitted as the LIFTED function's. *)
  (* The native-function-pointer remap only makes sense for <=64-bit words (a function pointer is a 64-bit address); a wider word (e.g. *)
  let remapped =
    if Word.bitwidth word <= 64 then
      let v = Word.to_int64_exn word in
      Base.Option.map (lookup_native_fn ctx llvm_module v) ~f:(fun fn ->
          Llvm.const_ptrtoint fn (Llvm.i64_type llvm_ctx))
    else None
  in
  match remapped with
  | Some c -> return c
  | None ->
      return
      @@ Llvm.const_int_of_string
           (Llvm.integer_type llvm_ctx (Word.bitwidth word))
           (Word.string_of_value word)
           16

let rec create_exp llvm_builder blk_tid exp =
  let open KB in
  let* ctx = Context.get emit_ctx_var in
  match exp with
  | BinOp (op, e1, e2) ->
      let* var1 = create_exp llvm_builder blk_tid e1 in
      let* var2 = create_exp llvm_builder blk_tid e2 in
      create_binop llvm_builder (op, var1, var2)
  | UnOp (op, e) ->
      let* var = create_exp llvm_builder blk_tid e in
      create_unop llvm_builder (op, var)
  | Var v -> (
      match get_local ctx blk_tid v with
      | Some v -> return v
      | None -> !$Llvm.poison (typ_lltype_m (Var.typ v)))
  | Int i -> create_immidiate i
  | Cast (cast, i, exp) ->
      let* var = create_exp llvm_builder blk_tid exp in
      create_cast llvm_builder (cast, i, var)
  | Concat (exp1, exp2) ->
      let s1 = exp_size exp1 in
      let s2 = exp_size exp2 in
      if s1 = 0 then create_exp llvm_builder blk_tid exp2
      else if s2 = 0 then create_exp llvm_builder blk_tid exp1
      else
        let* llvm_var1 = create_exp llvm_builder blk_tid exp1 in
        let* llvm_var2 = create_exp llvm_builder blk_tid exp2 in
        create_concat llvm_builder (llvm_var1, llvm_var2)
  | Extract (hi, lo, exp) ->
      let* llvm_var = create_exp llvm_builder blk_tid exp in
      create_extract llvm_builder (hi, lo, llvm_var)
  | Store (_, addr, data, _, _) ->
      let* addr = create_exp llvm_builder blk_tid addr in
      let* data = create_exp llvm_builder blk_tid data in
      create_store llvm_builder (data, addr)
  | Load (_, addr, _, size) ->
      let* addr = create_exp llvm_builder blk_tid addr in
      create_load llvm_builder (addr, Size.in_bits size)
  | Let (var, exp, body) ->
      let* tv = Bap_core_theory.Theory.Var.fresh (Var.sort var) in
      let unique_var = Var.reify tv in
      let* v = create_exp llvm_builder blk_tid exp in
      insert_local ctx blk_tid unique_var v;
      let body = Exp.substitute (Var var) (Var unique_var) body in
      create_exp llvm_builder blk_tid body
  | Ite (cond, true_exp, false_exp) ->
      let* cond = create_exp llvm_builder blk_tid cond in
      let* true_exp = create_exp llvm_builder blk_tid true_exp in
      let* false_exp = create_exp llvm_builder blk_tid false_exp in
      return @@ Llvm.build_select cond true_exp false_exp "" llvm_builder
  | Unknown (_, typ) ->
      let* typ = typ_lltype_m typ in
      return @@ Llvm.poison typ


let rec create_rip_relative_addr llvm_builder blk_tid exp =
  let open KB in
  let* llvm_ctx = Context.get llvm_ctx_var in
  let* llvm_module = Context.get llvm_module_var in
  let* ctx = Context.get emit_ctx_var in
  let* sections = Context.get section_list_var in
  match exp with
  | Bil.Int w ->
      (* NATIVE address remap: function entry (symtab) -> [const_ptrtoint (@fn)]; data-section address -> [const_ptrtoint (section+offset)]; anything else (a .text data constant-pool address) -> the raw address. *)
      let v = Word.to_int64_exn w in
      let* addr =
        match remap_native_addr ctx llvm_ctx llvm_module v with
        | Some c -> return c
        | None ->
            return @@ Llvm.const_of_int64 (Llvm.i64_type llvm_ctx) v false
      in
      return addr
  | Store (_, addr, data, _, _) ->
      let* addr = create_exp llvm_builder blk_tid addr in
      let addr =
        Llvm.int64_of_const addr
        |> Base.Option.value_exn ~message:"Const addr is not an int"
        |> Word.of_int64 ~width:64
      in
      let* addr = resolve_addr llvm_builder addr in
      let* data = create_exp llvm_builder blk_tid data in
      return @@ Llvm.build_store data addr llvm_builder
  | Load (_, addr, _, size) ->
      let* addr = create_exp llvm_builder blk_tid addr in
      let addr =
        Llvm.int64_of_const addr
        |> Base.Option.value_exn ~message:"Const addr is not an int"
        |> Word.of_int64 ~width:64
      in
      let addr_i64 = Word.to_int64_exn addr in
      let size = Size.in_bits size in
      (* The inline .text constant-pool: a .text load is read at compile time (function entry -> [ptrtoint @fn]; data -> the integer), NOT a @text global GEP (that gives fptr_table raw misaligned pointers). *)
      let* loaded =
        match
          text_load_constant ctx llvm_builder llvm_ctx llvm_module addr size
        with
        | Some c -> return c
        | None -> section_load llvm_builder llvm_ctx addr addr_i64 size
      in
      return loaded
  | Cast (cast, i, (Load _ as load)) ->
      (* RIP-relative movzx/movsx: RDX := pad:64[mem[0x401C, el]:u32] *)
      let* v = create_rip_relative_addr llvm_builder blk_tid load in
      create_cast llvm_builder (cast, i, v)
  | _ -> create_exp llvm_builder blk_tid exp

let create_branches blk_tid llvm_builder branches =
  let open KB in
  let open Bap.Std in
  let* ctx = KB.Context.get emit_ctx_var in
  if Seq.length branches = 1 then (* unconditional branch *)
    (
    let br = Seq.hd_exn branches in
    let jmp_target = Jmp.kind br |> goto_label_exn in
    match jmp_target with
    | Direct tid ->
        let bb = get_bb ctx tid in
        Llvm.build_br bb llvm_builder |> ignore;
        KB.return ()
    | Indirect exp ->
        let* target_val = create_exp llvm_builder blk_tid exp in
        Llvm.build_indirect_br target_val 1 llvm_builder |> ignore;
        KB.return ())
  else if Seq.length branches = 2 then (
    (* conditional branch *)
    let br1 = Seq.hd_exn branches in
    let else_jmp = Seq.to_list branches |> Base.List.last_exn in
    let true_target = Jmp.kind br1 |> goto_label_exn |> label_tid in
    let false_target = Jmp.kind else_jmp |> goto_label_exn |> label_tid in
    let true_bb = get_bb ctx true_target in
    let false_bb = get_bb ctx false_target in
    let cond = Jmp.cond br1 in
    let* cond_res = create_exp llvm_builder blk_tid cond in
    Llvm.build_cond_br cond_res true_bb false_bb llvm_builder |> ignore;
    KB.return ())
  else failwith "pp_branches: more than 2 branches"

(* [find_def_tag sub_tid def]: Vsa_kind option — the VSA tag of [def] from [Convutils.vsa_info]: ANY tag, singleton (lo = hi) and interval (lo < hi) alike — the split happens in [create_def]. *)
let find_def_tag sub_info def =
  Base.Option.bind sub_info ~f:(fun info ->
      Base.List.find_map info.Convutils.offsets ~f:(fun (dtid, kind) ->
          if Tid.equal dtid (Term.tid def) then Some kind else None))

(* [find_def_k sub_tid def]: the def's k-range from the vsa pass's [k_ranges] (absent -> None, the conservative local treatment). *)
let find_def_k sub_info def =
  Base.Option.bind sub_info ~f:(fun info ->
      Base.List.find_map info.Convutils.k_ranges ~f:(fun (dtid, klo, khi) ->
          if Tid.equal dtid (Term.tid def) then Some (klo, khi) else None))

(* [is_abi_visible ctx sub_info def]: does the access touch caller/callee-visible
   storage? Finding 1: this is NO LONGER a second copy of the rule — it is
   [Hike_stack_to_locals]'s, the module that owns the stack model. The emitter
   is a consumer. *)
let is_abi_visible ctx sub_info def =
  match sub_info with
  | None -> false
  | Some info ->
      Hike_stack_to_locals.abi_visibility_of (sp ctx.Convutils.target) info def

(* [is_stack_access def]: is [def] a Stack Access — the [stack_access]
   tag the relevance pass set on Stack Accesses, the only source of
   truth. (The legacy [addr_is_stack] two-predicate form was redundant:
   the relevance pass already filters by address derivation, so a
   tagged def is a Stack Access by construction. Inlined here.) *)
let is_stack_access def = Hike_vsa_relevance.has_stack_access def

(* [sub_degraded sub_tid]: The sub's VSA results are unusable for the narrow-tag / dead-path decisions (the D.1 non-convergent fixpoint or the D.2 indirect-jump incomplete-CFG cases — see [Convutils.vsa_info.degraded]): untagged stack accesses. *)
let sub_degraded sub_info =
  Base.Option.value_map sub_info ~default:false ~f:(fun info ->
      info.Convutils.degraded)

(* [is_plt_trampoline sub]: The BAP-resolved PLT stubs (the atexit/setlocale class) — a DEFINED sub whose BIL is `...; call @real with noreturn` — see the PLT-trampoline signature fix in hike.ml's [compute_sub_sig] and the noreturn-call fix in [create_call]. *)
let is_plt_trampoline ctx (sub : sub term) : bool =
  let free_vars =
    Sub.free_vars sub
    |> Core.Set.filter ~f:(fun var -> not @@ is_mem var)
    |> Core.Set.to_list
  in
  let reg_vars =
    Base.List.filter free_vars ~f:(fun reg ->
        not
          (Var.same reg (sp ctx.Convutils.target)
          || Var.same reg (fp ctx.Convutils.target)))
  in
  reg_vars = []
  && Term.enum blk_t sub
     |> Seq.exists ~f:(fun blk ->
            Term.enum jmp_t blk
            |> Seq.exists ~f:(fun j ->
                   match Jmp.kind j with
                   | Call _ -> true
                   | _ -> false))

(* [create_static_mem_access llvm_builder blk_tid fr lo exp]: Emit a
   Load/Store for the SINGLETON-tagged def at the entry- anchored
   offset [lo] — the MAP SOLUTION at the emitter: ONE [Exp.mapper]
   replaces ONLY the matched memory node with a marker var whose local
   is the built GEP access; ALL enclosing structure (the cast-wrapped
   [pad:64[mem[RBP-4]:u32]] keeps its cast — [create_cast] then emits
   the zext right at the load; loads nested in binops keep the binop)
   is preserved and emitted by the ordinary [create_exp]. No AST
   pattern matching on BIL constructors beyond the marker dispatch
   (the node finder is the [Exp.visitor], per Principle 8 /
   CONTEXT.md). *)
let create_static_mem_access llvm_builder blk_tid fr lo exp =
  let open KB in
  let* llvm_ctx = Context.get llvm_ctx_var in
  let* ctx = Context.get emit_ctx_var in
  let gep_opt =
    if Int64.compare lo 0L > 0 then
      match fr.stack with
      | Some stack ->
          let addr =
            Llvm.build_add stack
              (Llvm.const_of_int64 (Llvm.i64_type llvm_ctx) lo false)
              "" llvm_builder
          in
          Some (Llvm.build_inttoptr addr (Llvm.pointer_type llvm_ctx) "" llvm_builder)
      | None -> None
    else
      match fr.frame with
      | Some frame ->
          Some
            (Llvm.build_gep (Llvm.i8_type llvm_ctx) frame
               [|
                 Llvm.const_of_int64 (Llvm.i64_type llvm_ctx)
                   (Int64.add fr.anchor_idx lo) false;
               |]
               "" llvm_builder)
      | None -> None
  in
  match gep_opt with
  | Some gep ->
      (* The FIRST memory node of the rhs (the tagged access), found
         visitor-based; its address expression identifies every node
         of the SAME access (uniform-address def shapes). *)
      let access : [ `Load of exp * Size.t | `Store of exp * exp * Size.t ] option =
        let vis =
          object
            inherit
              [ [ `Load of exp * Size.t | `Store of exp * exp * Size.t ] option ]
              Exp.visitor
            method! visit_load ~mem:_ ~addr _ size acc =
              Base.Option.first_some acc (Some (`Load (addr, size)))
            method! visit_store ~mem:_ ~addr ~exp _ size acc =
              Base.Option.first_some acc (Some (`Store (addr, exp, size)))
          end
        in
        vis#visit_exp exp None
      in
      (match access with
       | Some (`Load (addr, size)) ->
           let marker =
             Var.create ~is_virtual:true ~fresh:false "hike_acc"
               (Type.Imm (Size.in_bits size))
           in
           let acc_v =
             Llvm.build_load
               (Llvm.integer_type llvm_ctx (Size.in_bits size))
               gep "" llvm_builder
           in
           insert_local ctx blk_tid marker acc_v;
           let v =
             object
               inherit Exp.mapper
               method! map_load ~mem ~addr:a e s =
                 if Exp.equal a addr && Size.equal s size then Bil.Var marker
                 else Bil.Load (mem, a, e, s)
             end
           in
           create_exp llvm_builder blk_tid (v#map_exp exp)
       | Some (`Store (addr, data, size)) ->
           let marker =
             Var.create ~is_virtual:true ~fresh:false "hike_acc"
               (Type.Imm (Size.in_bits size))
           in
           let* d = create_exp llvm_builder blk_tid data in
           let _ : Llvm.llvalue = Llvm.build_store d gep llvm_builder in
           (* the store's value semantics: the stored data (a store
              node as a value binds the data, never the void store
              instruction — the badref chain). *)
           insert_local ctx blk_tid marker d;
           let v =
             object
               inherit Exp.mapper
               method! map_store ~mem ~addr:a ~exp:x e s =
                 if Exp.equal a addr && Size.equal s size then Bil.Var marker
                 else Bil.Store (mem, a, x, e, s)
             end
           in
           create_exp llvm_builder blk_tid (v#map_exp exp)
       | None -> create_exp llvm_builder blk_tid exp)
  | None ->
      if Sys.getenv_opt "HIKE_VSA_DEBUG" <> None then
        Printf.eprintf "hike: create_static_mem_access fallback lo=%Ld no frame/stack -> dynamic\n" lo;
      create_exp llvm_builder blk_tid exp

(* The three-way emission branch of the UNFLAGGED defs (the rip_relative_addr branch stays above): - SINGLETON tag (lo = hi): the const-GEP static access into the per-sub frame. *)
(* [rebase_addr llvm_builder fr addr]: The positive-interval address re-base — [stack + (addr - anchor)]: the model's address (computed from the per-sub anchor-based RSP/RBP locals) minus the anchor = the offset from the sub's ENTRY; adding the. *)
let rebase_addr llvm_builder fr addr =
  let open KB in
  let stack =
    Base.Option.value_exn fr.stack
      ~message:"rebase_addr: positive interval but no stack param"
  in
  let offset = Llvm.build_sub addr fr.anchor_i64 "arg_off" llvm_builder in
  return @@ Llvm.build_add stack offset "arg_addr" llvm_builder

(* [create_dynamic_alloc llvm_builder blk_tid exp]: The stack-model Phase 1 emission — the runtime-sized stack allocation (VLA/alloca, the [dynamic_alloc]-tagged def) becomes a REAL LLVM dynamic alloca: `%vla = alloca i8, i64 <size>, align 16`, and the def's lhs (RSP for. *)
let create_dynamic_alloc llvm_builder blk_tid exp =
  let open KB in
  match exp with
  | Bil.BinOp (Bil.MINUS, _, size) ->
      let* llvm_ctx = Context.get llvm_ctx_var in
      let* size_v = create_exp llvm_builder blk_tid size in
      let vla =
        Llvm.build_array_alloca (Llvm.i8_type llvm_ctx) size_v "vla"
          llvm_builder
      in
      Llvm.set_alignment 16 vla;
      return
      @@ Llvm.build_ptrtoint vla (Llvm.i64_type llvm_ctx) "vla_i64"
           llvm_builder
  | _ -> create_exp llvm_builder blk_tid exp

(* [mem_access_via_ptr llvm_builder blk_tid addr_v exp]: inttoptr an already-computed runtime address ([addr_v], an i64) and load/store through it — the shared tail of the outgoing-cell and positive- interval branches in [create_def]. *)
let mem_access_via_ptr llvm_builder blk_tid addr_v exp =
  let open KB in
  let* llvm_ctx = Context.get llvm_ctx_var in
  let p =
    Llvm.build_inttoptr addr_v (Llvm.pointer_type llvm_ctx) "" llvm_builder
  in
  match exp with
  | Bil.Load (_, _, _, size) ->
      return
      @@ Llvm.build_load (Llvm.integer_type llvm_ctx (Size.in_bits size)) p
           "" llvm_builder
  | Bil.Store (_, _, data, _, _) ->
      let* d = create_exp llvm_builder blk_tid data in
      return @@ Llvm.build_store d p llvm_builder
  | Bil.Cast (c, w, Bil.Load (_, _, _, size)) ->
      let v =
        Llvm.build_load (Llvm.integer_type llvm_ctx (Size.in_bits size)) p
          "" llvm_builder
      in
      create_cast llvm_builder (c, w, v)
  | Bil.Cast (c, w, Bil.Store (_, _, data, _, _)) ->
      let* d = create_exp llvm_builder blk_tid data in
      let s = Llvm.build_store d p llvm_builder in
      create_cast llvm_builder (c, w, s)
  | _ -> create_exp llvm_builder blk_tid exp

(* [region_of_offset regions lo]: the ALLOCATED region ([stack_rN]) whose
   span contains the singleton offset [lo] — the split model's access
   resolution. The region list is exactly the plan the vsa pass produced
   ([stack_plan_of]), so this is a lookup, never a decision. *)
let region_of_offset (regions : (Convutils.region * Llvm.llvalue) list)
    (lo : int64) : (Convutils.region * Llvm.llvalue) option =
  Base.List.find regions ~f:(fun (r, _) ->
      let rlo, rhi = r.Convutils.span in
      Int64.compare lo rlo >= 0 && Int64.compare lo rhi <= 0)

(* [mem_access ...]: THE per-access memory dispatcher — the ONE place the
   emitter classifies how a tagged stack access resolves to storage. Both
   the split model's region misses and the whole fallback model route
   here, so the classification exists once (previously the precise and
   non-precise arms of [create_def] each carried a near-verbatim copy —
   Finding 1). The classification itself is the VSA's (the tag) plus the
   ABI-visibility rule; this function only EXECUTES it. *)
let mem_access llvm_builder blk_tid sub_tid sub_info fr (def : def term)
    (exp : exp) =
  let open KB in
  let* ctx = Context.get emit_ctx_var in
  let var = Def.lhs def in
  match find_def_tag sub_info def with
  | Some (Convutils.Range (lo, hi))
    when Int64.equal lo hi && is_stack_access def ->
      if Int64.compare lo 0L > 0 then
        (* The callee's incoming-arg cell (lo > 0 — read at its entry,
           where the anchored [lo] IS the ABI offset): [%hike_stack + lo]. *)
        (match fr.stack with
        | Some _ -> create_static_mem_access llvm_builder blk_tid fr lo exp
        | None -> create_exp llvm_builder blk_tid exp)
      else if is_abi_visible ctx sub_info def then
        (* The OUTGOING cell (k = addr − RSP at the def ≥ 0, lo ≤ 0): the
           caller's arg-area stores AND the sub's own pushes at [RSP] —
           the TRUE runtime address is the rhs's own address expression. *)
        (match Def.rhs def with
        | Bil.Load (_, addr, _, _) | Bil.Store (_, addr, _, _, _) ->
            let* addr_v = create_exp llvm_builder blk_tid addr in
            mem_access_via_ptr llvm_builder blk_tid addr_v exp
        | _ -> create_exp llvm_builder blk_tid exp)
      else
        (* the true local (k < 0): the static frame GEP. *)
        create_static_mem_access llvm_builder blk_tid fr lo exp
  | Some (Convutils.Range (lo, _) | Convutils.Infinite (lo, _))
    when Int64.compare lo 0L > 0 && is_stack_access def ->
      (* The POSITIVE-interval class (varargs reads etc.): the address
         re-based onto the stack-threading value — [stack + (addr -
         anchor)] — the offset from the entry is preserved while the base
         moves from the per-sub frame to the caller's frame. *)
      (match Def.rhs def with
      | Bil.Load (_, addr, _, _) | Bil.Store (_, addr, _, _, _) ->
          let* addr_v = create_exp llvm_builder blk_tid addr in
          let* addr_v = rebase_addr llvm_builder fr addr_v in
          mem_access_via_ptr llvm_builder blk_tid addr_v exp
      | _ -> create_exp llvm_builder blk_tid exp)
  | Some (Convutils.VLA _) -> create_exp llvm_builder blk_tid exp
  | Some Convutils.Unbounded ->
      if is_stack_access def then begin
        if not (Core.Set.mem !(ctx.Convutils.guarded_warned) sub_tid) then begin
          ctx.Convutils.guarded_warned :=
            Core.Set.add !(ctx.Convutils.guarded_warned) sub_tid;
          Printf.eprintf
            "hike: guarded: sub %s: stack access is Unbounded (unconstrained / TOP): def %s rhs=%s\n"
            (Tid.name sub_tid) (Var.name var) (Format.asprintf "%a" Exp.pp exp)
        end
      end;
      create_exp llvm_builder blk_tid exp
  | Some (Convutils.Range _) | Some (Convutils.Infinite _) ->
      create_exp llvm_builder blk_tid exp
  | Some Convutils.Dead ->
      let* typ = typ_lltype_m (Var.typ var) in
      return @@ Llvm.poison typ
  | None ->
      if is_stack_access def then
        failwith
          (Printf.sprintf
             "hike: 100%% VSA Tagging invariant violated: sub %s def %s has no VSA tag"
             (Tid.name sub_tid) (Tid.name (Term.tid def)))
      else create_exp llvm_builder blk_tid exp

let create_def blk_tid llvm_builder sub_tid sub_info fr def =
  let open KB in
  let* ctx = Context.get emit_ctx_var in
  let var = Def.lhs def in
  let v = Def.value def in
  let exp = Def.rhs def in
  let _ = (ctx, var) in
  let* res =
    if Term.has_attr def Hike_vsa_relevance.dynamic_alloc then
      create_dynamic_alloc llvm_builder blk_tid exp
    else if KB.Value.get rip_relative_addr v then
      create_rip_relative_addr llvm_builder blk_tid exp
    else if fr.is_precise then
      (* SPLIT model: the plan's regions are the storage. A singleton
         access inside an allocated region is a [stack_rN] GEP; every
         other shape falls through to the shared dispatcher below (one
         classification, not a second copy of it). *)
      (match find_def_tag sub_info def with
       | Some (Convutils.Range (lo, hi))
         when Int64.equal lo hi && is_stack_access def ->
           (match region_of_offset fr.regions lo with
            | Some (r, base) ->
                let offset = Int64.sub lo (fst r.Convutils.span) in
                let* llvm_ctx = Context.get llvm_ctx_var in
                let gep =
                  Llvm.build_gep (Llvm.i8_type llvm_ctx) base
                    [| Llvm.const_of_int64 (Llvm.i64_type llvm_ctx) offset false |]
                    "" llvm_builder
                in
                (match Def.rhs def with
                | Bil.Load (_, _, _, s) ->
                    return
                    @@ Llvm.build_load
                         (Llvm.integer_type llvm_ctx (Size.in_bits s))
                         gep "" llvm_builder
                | Bil.Store (_, _, data, _, _) ->
                    let* d = create_exp llvm_builder blk_tid data in
                    return @@ Llvm.build_store d gep llvm_builder
                | Bil.Cast (c, w, Bil.Load (_, _, _, s)) ->
                    let v =
                      Llvm.build_load
                        (Llvm.integer_type llvm_ctx (Size.in_bits s))
                        gep "" llvm_builder
                    in
                    create_cast llvm_builder (c, w, v)
                | _ -> create_exp llvm_builder blk_tid exp)
            | None -> mem_access llvm_builder blk_tid sub_tid sub_info fr def exp)
       | _ -> mem_access llvm_builder blk_tid sub_tid sub_info fr def exp)
    else mem_access llvm_builder blk_tid sub_tid sub_info fr def exp
  in
  insert_local ctx blk_tid var res;
  return ()

(* [restore_sp_after_call llvm_builder ctx sub_tid fr fallthrough_tid]:
   L-E1e — the call-block's push defs (RSP := RSP - 8; mem[RSP] := retaddr)
   leave the caller's SP local at pre_call_rsp - 8. The callee's "return"
   pops its own lane, not the caller's; the lifted callee starts from a
   fresh anchor (`build_entry_block`) and external callees have no model
   lane at all. So the caller's SP must be restored manually: at the
   fallthrough block, RSP := post_push + 8 = pre_call_rsp.

   We compute `post_push + 8` while the builder is still in the call block
   (so the add instruction lives there), then `insert_local` binds the SP
   var in the fallthrough's local table. The phi resolution at the
   fallthrough reads this binding.

   Skipped on the precise path (the precise path erases RSP/RBP from the
   sub's locals; only the `hike_stack` arg survives; no SP local to rebind).
   Skipped when there is no fallthrough (noreturn / tail call — execution
   never returns). Skipped when the SP local is unbound in the call block
   (defensive: should not happen, but a no-op is sound). *)
let restore_sp_after_call llvm_builder ctx sub_tid fr fallthrough_tid =
  let open KB in
  if fr.is_precise then return ()
  else
    let sp_key = sp ctx.Convutils.target in
    match get_local ctx sub_tid sp_key with
    | None -> return ()
    | Some post_push ->
        let* llvm_ctx = Context.get llvm_ctx_var in
        let restored =
          Llvm.build_add post_push
            (Llvm.const_int (Llvm.i64_type llvm_ctx) 8) "sp_restored"
            llvm_builder
        in
        insert_local ctx fallthrough_tid sp_key restored;
        return ()

let create_call_args blk_tid llvm_builder sub call_tid fr =
  let open KB in
  let* ctx = Context.get emit_ctx_var in
  let* llvm_ctx = Context.get llvm_ctx_var in
  let args = get_args ctx call_tid in
  let extern = is_extern ctx call_tid in
  KB.List.map args ~f:(fun arg ->
      let exp = Arg.rhs arg in
      if Var.same (Arg.lhs arg) Convutils.hike_stack_var then
        (* M2: thread hike_stack — precise caller passes its own hike_stack (no current RSP), degraded passes current RSP. *)
        let v_opt =
          if fr.is_precise then get_local ctx blk_tid Convutils.hike_stack_var
          else get_local ctx blk_tid (sp ctx.Convutils.target)
        in
        let v_opt = match v_opt with Some _ -> v_opt | None -> get_local ctx blk_tid Convutils.hike_stack_var in
        let v_opt = match v_opt with Some _ -> v_opt | None -> get_local ctx blk_tid (sp ctx.Convutils.target) in
        match v_opt with
        | Some v -> return v
        | None ->
            let* llvm_ctx = Context.get llvm_ctx_var in
            return @@ Llvm.poison (Llvm.i64_type llvm_ctx)
      else if extern && is_fp_param (Arg.lhs arg) then
        (* the FP arg of an EXTERN call (printf-style): the model's YMM local (i256) must reach the real ABI's XMM register — emit `bitcast (trunc i256 to i64) to double`. Model-to- model calls keep the i256 pass-through (their stored signatures bind the YMM params directly). *)
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

let get_func tid =
  let open KB in
  let* ctx = Context.get emit_ctx_var in
  match Core.Map.find !(ctx.Convutils.ll_funcs) tid with
  | Some v -> return v
  | None ->
      let* _ = create_fun_declaration tid in
      return @@ Core.Map.find_exn !(ctx.Convutils.ll_funcs) tid
let create_indirect_call llvm_builder blk_tid sub call fr =
  let open KB in
  let* ctx = Context.get emit_ctx_var in
  let target = Call.target call |> label_exp in
  let fallthrough =
    Call.return call
    |> Base.Option.value_exn ~message:"Create call: expected call got return"
    |> label_tid
  in
  let* target_exp = create_exp llvm_builder blk_tid target in
  let* func_ptr = create_inttoptr llvm_builder target_exp in
  let* fn, fn_typ = get_func (Tid.for_name "indirect_call") in
  let bb = get_bb ctx fallthrough in
  let rets = get_rets ctx (Tid.for_name "indirect_call") in
  let* args =
    create_call_args blk_tid llvm_builder sub (Tid.for_name "indirect_call") fr
  in
  let ret_struct =
    Llvm.build_call fn_typ func_ptr (Array.of_list args) "" llvm_builder
  in
  Base.List.iteri rets ~f:(fun i ret ->
      let ret_val = Llvm.build_extractvalue ret_struct i "" llvm_builder in
      insert_local ctx blk_tid (Arg.lhs ret) ret_val);
  let* () = restore_sp_after_call llvm_builder ctx blk_tid fr fallthrough in
  Llvm.build_br bb llvm_builder |> ignore;
  return ()

let create_func_call ?(emit_unreachable = true) llvm_builder blk_tid sub
    fallthrough target fr =
  let open KB in
  let* llvm_ctx = Context.get llvm_ctx_var in
  let* ctx = Context.get emit_ctx_var in
  let* args = create_call_args blk_tid llvm_builder sub target fr in
  let rets = get_rets ctx target in
  let* fn, fn_typ = get_func target in
  (match (fp_ret_kind_of_extern ctx target, rets) with
  | Some kind, ret :: _ ->
      (* The FP-returning extern: the real callee returns float/double/ x86_fp80 (XMM0 / x87 ST0), NOT the model's {i64,i64}. *)
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
                insert_local ctx blk_tid (Arg.lhs rd)
                  (Llvm.poison (Llvm.i64_type llvm_ctx))
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
      Base.List.iteri rets ~f:(fun i ret ->
          let ret_val = Llvm.build_extractvalue ret_struct i "" llvm_builder in
          insert_local ctx blk_tid (Arg.lhs ret) ret_val));
  (match fallthrough with
  | Some fallthrough ->
      let* () = restore_sp_after_call llvm_builder ctx blk_tid fr fallthrough in
      let bb = get_bb ctx fallthrough in
      let _ = Llvm.build_br bb llvm_builder in
      return ()
  | None ->
      if emit_unreachable then begin
        let _ = Llvm.build_unreachable llvm_builder in
        return ()
      end else return ())

let create_return blk_tid llvm_builder cur_sub =
  let open KB in
  let* ctx = Context.get emit_ctx_var in
  let* rets =
    KB.List.map (get_rets ctx (Term.tid cur_sub)) ~f:(fun ret ->
        (* the [%YMM0] FP-return member (the model subs' rets carry it so a double-returning callee — the -O0 `return expr` leaves the value in XMM0 with NO RAX binding — delivers the value to the caller). An int-returning callee never defines YMM0 — poison. *)
        match get_local ctx blk_tid (Arg.lhs ret) with
        | Some v -> return v
        | None ->
            let* typ = var_lltype (Arg.lhs ret) in
            return @@ Llvm.poison typ)
  in
  (match rets with
  | [] -> Llvm.build_ret_void llvm_builder |> ignore
  | [ ret ] -> Llvm.build_ret ret llvm_builder |> ignore
  | rets -> Llvm.build_aggregate_ret (Array.of_list rets) llvm_builder |> ignore);
  return ()

(* [create_interrupt llvm_builder]: The interrupt edge — the lifted `call @interrupt:#N with noreturn` (the hlt/ud2 trap class: BAP lifts `hlt` to a noreturn call to the [interrupt:#N] label, whose sub is filtered out of the program) and the genuine Int jmps. *)
let create_interrupt llvm_builder =
  let open KB in
  let* llvm_ctx = Context.get llvm_ctx_var in
  let* llvm_module = Context.get llvm_module_var in
  let trap_ty = Llvm.function_type (Llvm.void_type llvm_ctx) [||] in
  let trap = Llvm.declare_function "llvm.trap" trap_ty llvm_module in
  ignore
    (Llvm.build_call trap_ty trap [||] "" llvm_builder);
  ignore (Llvm.build_unreachable llvm_builder);
  KB.return ()

(* The FP-intrinsic → native LLVM FP-op mapping (the user's design, 2026-08-16): BAP declares the x86 FP instructions as CALLS to the [intrinsic:*] soft-float subs. *)
type native_fp = FMUL | FADD | FSUB | FDIV | FREM | SFLOAT | SINT

let fp_intrinsic_name = strip_at

let native_fp_op (name : string) : native_fp option =
  match fp_intrinsic_name name with
  | "intrinsic:fmul_rne_ieee754_binary" -> Some FMUL
  | "intrinsic:fadd_rne_ieee754_binary" -> Some FADD
  | "intrinsic:fsub_rne_ieee754_binary" -> Some FSUB
  | "intrinsic:fdiv_rne_ieee754_binary" -> Some FDIV
  | "intrinsic:frem_rne_ieee754_binary" -> Some FREM
  | "intrinsic:cast_sfloat_rne_ieee754_binary_64" -> Some SFLOAT
  | "intrinsic:cast_sint_rne_ieee754_binary_64" -> Some SINT
  | _ -> None

(* [has_32bit_extract e]: the [intrinsic:x0] setup for the i32→double casts — the lifter's `63:0[31:0[RAX]]` shape reveals the 32-bit source (the sign-extension the soft-float needs). *)
let rec has_32bit_extract (e : exp) : bool =
  match e with
  | Bil.Extract (31, _, _) -> true
  | Bil.Extract (_, _, e') -> has_32bit_extract e'
  | Bil.BinOp (_, a, b) -> has_32bit_extract a || has_32bit_extract b
  | Bil.Cast (_, _, e') -> has_32bit_extract e'
  | _ -> false

(* [cast_source_width sub blk]: The source width of the [cast_sfloat] call in [blk] — 32 when the [intrinsic:x0] def's rhs reveals a 32-bit source (the register-extract shape OR an 8-byte load from an RBP slot that was WRITTEN as u32 — the `cvtsi2sdl addr` memory-operand shape), else 64. *)
let cast_source_width (sub : sub term) (blk : blk term) : int =
  let u32_slots =
    Term.enum blk_t sub
    |> Seq.fold ~init:[] ~f:(fun acc b ->
        Term.enum def_t b
        |> Seq.fold ~init:acc ~f:(fun acc d ->
            match Def.rhs d with
            | Bil.Store (_, addr, _, _, s) when Size.in_bits s = 32 -> (
                match addr with
                | Bil.BinOp (Bil.PLUS, Bil.Var bv, Bil.Int w)
                  when String.equal (Var.name (Var.base bv)) "RBP" ->
                    Word.to_int64_exn w :: acc
                | Bil.Var bv when String.equal (Var.name (Var.base bv)) "RBP" ->
                    0L :: acc
                | _ -> acc)
            | _ -> acc))
  in
  match
    Term.enum def_t blk
    |> Seq.find ~f:(fun d ->
        String.equal (Var.name (Var.base (Def.lhs d))) "intrinsic:x0")
  with
  | None -> 64
  | Some d -> (
      match Def.rhs d with
      | e when has_32bit_extract e -> 32
      | Bil.Load (_, addr, _, _) -> (
          match addr with
          | Bil.BinOp (Bil.PLUS, Bil.Var bv, Bil.Int w)
            when String.equal (Var.name (Var.base bv)) "RBP" ->
              if Base.List.mem ~equal:Int64.equal u32_slots (Word.to_int64_exn w)
              then 32
              else 64
          | _ -> 64)
      | _ -> 64)

let build_fp_binop llvm_builder op a b =
  let open KB in
  let* llvm_ctx = Context.get llvm_ctx_var in
  let bitcast v =
    if Llvm.classify_type (Llvm.type_of v) = Llvm.TypeKind.Integer then
      Llvm.build_bitcast v (Llvm.double_type llvm_ctx) "" llvm_builder
    else v
  in
  let da = bitcast a in
  let db = bitcast b in
  let d =
    match op with
    | FMUL -> Llvm.build_fmul da db "" llvm_builder
    | FADD -> Llvm.build_fadd da db "" llvm_builder
    | FSUB -> Llvm.build_fsub da db "" llvm_builder
    | FDIV -> Llvm.build_fdiv da db "" llvm_builder
    | FREM -> Llvm.build_frem da db "" llvm_builder
    | SFLOAT | SINT -> assert false
  in
  return
  @@ Llvm.build_bitcast d (Llvm.i64_type llvm_ctx) "" llvm_builder

(* [create_native_fp_call llvm_builder blk_tid blk sub call op]: the mapped FP-intrinsic call — no function call, the native LLVM FP op inline, the result bound to [intrinsic:y0]. *)
let create_native_fp_call llvm_builder blk_tid blk sub call op =
  let open KB in
  let* llvm_ctx = Context.get llvm_ctx_var in
  let* ctx = Context.get emit_ctx_var in
  let fallthrough = Option.map label_tid (Call.return call) in
  let target = Call.target call |> label_tid in
  let args = get_args ctx target in
  let arg_value (i : int) : Llvm.llvalue KB.t =
    (* Resolve x-operand from the most-recent intrinsic:xN_* def in blk (width-suffixed). *)
    let prefix = Printf.sprintf "intrinsic:x%d_" i in
    let x_def_opt =
      Term.enum def_t blk
      |> Base.Sequence.to_list
      |> Base.List.filter ~f:(fun d -> Base.String.is_prefix (Var.name (Def.lhs d)) ~prefix)
      |> Base.List.last
    in
    match x_def_opt with
    | Some d -> create_exp llvm_builder blk_tid (Def.rhs d)
    | None ->
      let arg = Base.List.nth_exn args i in
      create_exp llvm_builder blk_tid (Arg.rhs arg)
  in
  let result =
    match op with
    | FMUL | FADD | FSUB | FDIV | FREM ->
        let* a = arg_value 0 in
        let* b = arg_value 1 in
        build_fp_binop llvm_builder op a b
    | SFLOAT ->
        let* x = arg_value 0 in
        let width = cast_source_width sub blk in
        if width = 32 then
          let* t =
            KB.return
            @@ Llvm.build_trunc x (Llvm.i32_type llvm_ctx) "" llvm_builder
          in
          let* d =
            KB.return
            @@ Llvm.build_sitofp t (Llvm.double_type llvm_ctx) "" llvm_builder
          in
          return
          @@ Llvm.build_bitcast d (Llvm.i64_type llvm_ctx) "" llvm_builder
        else
          let* d =
            KB.return
            @@ Llvm.build_sitofp x (Llvm.double_type llvm_ctx) "" llvm_builder
          in
          return
          @@ Llvm.build_bitcast d (Llvm.i64_type llvm_ctx) "" llvm_builder
    | SINT ->
        let* x = arg_value 0 in
        let* d =
          KB.return
          @@ Llvm.build_bitcast x (Llvm.double_type llvm_ctx) "" llvm_builder
        in
        let* r =
          KB.return
          @@ Llvm.build_fptosi d (Llvm.i64_type llvm_ctx) "" llvm_builder
        in
        return r
  in
  let* r = result in
  (match get_rets ctx target with
   | [ ret ] ->
     insert_local ctx blk_tid (Arg.lhs ret) r;
     (* Bind every consumer-width view of y0 (y0_64/y0_32/y0_1) — the BIR after rename_intrinsics has distinct y0_* lanes, but the soft-float result is a single i64/i32 value that must be visible at all widths. *)
     let y0_64 = Var.create "intrinsic:y0_64" (Imm 64) in
     let y0_32 = Var.create "intrinsic:y0_32" (Imm 32) in
     let y0_1 = Var.create "intrinsic:y0_1" (Imm 1) in
     let r_ty = Llvm.type_of r in
     let r_bits = try Llvm.integer_bitwidth r_ty with _ -> 64 in
     (* y0_64 *)
     if not (Var.same (Arg.lhs ret) y0_64) then (
       let v64 = if r_bits = 64 then r else if r_bits > 64 then Llvm.build_trunc r (Llvm.i64_type llvm_ctx) "" llvm_builder else Llvm.build_zext r (Llvm.i64_type llvm_ctx) "" llvm_builder in
       insert_local ctx blk_tid y0_64 v64
     );
     (* y0_32 *)
     if not (Var.same (Arg.lhs ret) y0_32) then (
       let v32 = if r_bits = 32 then r else if r_bits > 32 then Llvm.build_trunc r (Llvm.i32_type llvm_ctx) "" llvm_builder else Llvm.build_zext r (Llvm.i32_type llvm_ctx) "" llvm_builder in
       insert_local ctx blk_tid y0_32 v32
     );
     (* y0_1 *)
     if not (Var.same (Arg.lhs ret) y0_1) then (
       let v1 = if r_bits = 1 then r else if r_bits > 1 then Llvm.build_trunc r (Llvm.i1_type llvm_ctx) "" llvm_builder else Llvm.build_zext r (Llvm.i1_type llvm_ctx) "" llvm_builder in
       insert_local ctx blk_tid y0_1 v1
     )
   | _ -> ());
  (match fallthrough with
   | Some ft ->
       let bb = get_bb ctx ft in
       ignore (Llvm.build_br bb llvm_builder);
       KB.return ()
   | None ->
       ignore (Llvm.build_unreachable llvm_builder);
       KB.return ())

let create_call llvm_builder blk_tid blk sub call fr =
  let open KB in
  let* ctx = Context.get emit_ctx_var in
  let target = Call.target call |> label_tid in
  let name = Tid.name target |> fp_intrinsic_name in
  if Base.String.is_prefix (Tid.name target) ~prefix:"@interrupt:" then
    (* the lifted interrupt edge: `call @interrupt:#N with noreturn` (the hlt/ud2 trap class — the callee sub is filtered out, so the call would be an undefined symbol). The trap model above. *)
    create_interrupt llvm_builder
  else
    match native_fp_op name with
    | Some op -> create_native_fp_call llvm_builder blk_tid blk sub call op
    | None ->
        (* FAIL LOUDLY on an unmapped intrinsic (the no-silent-fallback doctrine): an [intrinsic:*] call hike cannot map to a native op — the x87 80-bit [llvm-x86_64:*] class surfaced by [--bil-enable-intrinsics=:unknown], or any. *)
        if Base.String.is_prefix name ~prefix:"intrinsic:" then
          failwith
            (Printf.sprintf "hike: unmapped intrinsic call: %s (in sub %s)" name
               (Tid.name (Term.tid sub)))
        else (
        (* The PLT-TRAMPOLINE callers (the model's atexit/setlocale class): the BAP rewrote the PLT stub into `...; call @real with noreturn` — the noreturn marking is a LIFTER heuristic (the stub's jmp-through-GOT tail-call looks like a noreturn edge), but the REAL callee (__cxa_atexit) RETURNS. *)
        match Call.return call with
        | Some l ->
            let fallthrough = Some (label_tid l) in
            create_func_call llvm_builder blk_tid sub fallthrough target fr
        | None ->
            if is_plt_trampoline ctx sub then
              let* () =
                create_func_call ~emit_unreachable:false llvm_builder blk_tid sub
                  None target fr
              in
              create_return blk_tid llvm_builder sub
            else create_func_call llvm_builder blk_tid sub None target fr)

let update_phi transfer_vars blk_incoming blk_tid =
  let open KB in
  let* ctx = Context.get emit_ctx_var in
  KB.List.iter transfer_vars ~f:(fun var ->
      let phi_llvar = get_phi ctx blk_tid var in
      Seq.iter blk_incoming ~f:(fun tid ->
          let phi_reg = get_local ctx tid var in
          match phi_reg with
          | Some phi_reg ->
              Llvm.add_incoming (phi_reg, get_bb ctx tid) phi_llvar;
              return ()
          | None -> failwith "update_phi: phi_reg not found"))

let update_phis transfer_vars blks sub () =
  let open KB in
  let cfg = Sub.to_graph sub in
  Seq.iter blks ~f:(fun blk ->
      let blk_tid = Term.tid blk in
      let blk_incoming = Graphs.Tid.Node.preds (Term.tid blk) cfg in
      update_phi transfer_vars blk_incoming blk_tid)

(* [create_control_flow ...]: see [create_interrupt] above — the Int jmp (a trap edge) emits the same trap + unreachable. *)
let create_control_flow llvm_builder blk sub fr () =
  let control_flow = Term.enum jmp_t blk in
  let tid = Term.tid blk in
  if Seq.is_empty control_flow then
    (* a def-only block with no jmps (the FP-soft-float intrinsic models: the single `intrinsic:y0 := <body>` def, no control flow) — the implicit return of the sub's rets. *)
    create_return tid llvm_builder sub
  else
  match cf_type control_flow with
  | Br -> create_branches tid llvm_builder control_flow
  | Int -> create_interrupt llvm_builder
  | Ret -> create_return tid llvm_builder sub
  | CallIndirect ->
      let call = Bap.Std.Seq.hd_exn control_flow |> call_exn in
      create_indirect_call llvm_builder (Term.tid blk) sub call fr
  | CallFun | CallFunVoid ->
      let call = Bap.Std.Seq.hd_exn control_flow |> call_exn in
      create_call llvm_builder (Term.tid blk) blk sub call fr

let transfer_with_phis transfer_vars llvm_builder blk_tid () =
  let open KB in
  let* ctx = Context.get emit_ctx_var in
  KB.List.iter transfer_vars ~f:(fun var ->
      let* typ = var_lltype var in
      let res = Llvm.build_empty_phi typ "" llvm_builder in
      insert_phi ctx blk_tid var res;
      insert_local ctx blk_tid var res;
      return ())

let create_elts llvm_builder blk sub_tid sub_info fr () =
  let open KB in
  let tid = Term.tid blk in
  Blk.elts blk
  |> Seq.iter ~f:(fun elt ->
      match elt with
      | `Def def -> create_def tid llvm_builder sub_tid sub_info fr def
      | `Phi _ -> return ()
      | `Jmp _ -> return ())

let populate_blks transfer_vars blks sub sub_info fr () =
  let open KB in
  let* llvm_ctx = Context.get llvm_ctx_var in
  let* ctx = Context.get emit_ctx_var in
  let sub_tid = Term.tid sub in
  Seq.iter blks ~f:(fun blk ->
      let llvm_builder =
        Llvm.builder_at_end llvm_ctx (get_bb ctx (Term.tid blk))
      in
      transfer_with_phis transfer_vars llvm_builder (Term.tid blk) ()
      >>= create_elts llvm_builder blk sub_tid sub_info fr
      >>= create_control_flow llvm_builder blk sub fr)

(* go from entry to first bb *)
let exit_entry llvm_builder sub () =
  let open KB in
  let* ctx = Context.get emit_ctx_var in
  KB.return
  @@ Llvm.build_br (get_bb ctx (entry_blk_tid sub)) llvm_builder

let build_entry_block llvm_builder transfer_vars fr sub fn () =
  let open KB in
  let* ctx = Context.get emit_ctx_var in
  let tid = Graphs.Tid.start in
  KB.List.iter transfer_vars ~f:(fun var ->
      let arg =
        Base.List.find (get_args ctx (Term.tid sub)) ~f:(fun arg ->
            Var.same (Arg.lhs arg) var)
      in
      let llval =
        match arg with
        | Some arg -> create_exp llvm_builder tid (Arg.rhs arg)
        | None -> !$Llvm.poison (var_lltype var)
      in
      !$(insert_local ctx tid var) llval)
  >>= fun () ->
  if fr.is_precise then (
    (* M2: precise keeps hike_stack for incoming (lo>0) via GEP, RSP/RBP erased *)
    let fr = { fr with stack = get_local ctx tid Convutils.hike_stack_var } in
    exit_entry llvm_builder sub () >>= fun _ -> return fr
  ) else (
  (* The sp/fp params are gone (compute_sub_sig filters RSP/RBP out of the arg list), so the transfer-vars loop above poisoned RSP/RBP — they are block-free vars but no longer args. *)
  insert_local ctx tid (sp ctx.Convutils.target) fr.anchor_i64;
  (* the stack-threading param: the bound [hike_stack] argument (if the sub's signature has it) — the entry RSP, a real pointer into the CALLER's frame. The positive-offset (incoming-arg) accesses read it via [fr.stack]. *)
  let fr =
    { fr with stack = get_local ctx tid Convutils.hike_stack_var }
  in
  let* fp_anchor =
    let* llvm_ctx = Context.get llvm_ctx_var in
    return
    @@ Llvm.build_sub fr.anchor_i64 (Llvm.const_int (Llvm.i64_type llvm_ctx) 8)
         "" llvm_builder
  in
  insert_local ctx tid (fp ctx.Convutils.target) fp_anchor;
  exit_entry llvm_builder sub ()
  >>= fun _ -> return fr
  )

(* R4 — single-pass per-sub data: create each LLVM basic block + its llval map AND accumulate the register-transfer set in ONE walk over [blks] (previously [initialize_bbs] and [sub_transfer_vars] each enumerated [blks] separately). *)
let collect_sub_data ctx llvm_ctx blks fn =
  insert_bb ctx Graphs.Tid.start (Llvm.entry_block fn);
  init_blk_llvals ctx Graphs.Tid.start;
  (* The per-sub register-transfer set: the block free vars ∪ the call-ARG registers (the BIR call jmp carries no argument list — a call's args are the callee's signature vars, read at the call but INVISIBLE to the. *) 
  Seq.fold blks
    ~f:(fun reg_set blk ->
      let tid = Term.tid blk in
      init_blk_llvals ctx tid;
      insert_bb ctx tid (Llvm.append_block llvm_ctx (Term.name blk) fn);
      let blk_free = Blk.free_vars blk in
      let call_args =
        Term.enum jmp_t blk
        |> Seq.fold ~init:Var.Set.empty ~f:(fun acc jmp ->
            match Jmp.kind jmp with
            | Call c -> (
                match Call.target c with
                | Direct ctid ->
                    let args = get_args ctx ctid in
                    Base.List.fold args ~init:acc ~f:(fun acc arg ->
                        Core.Set.add acc (Var.base (Arg.lhs arg)))
                | Indirect _ -> acc)
            | _ -> acc)
      in
      Core.Set.union reg_set (Core.Set.union blk_free call_args))
    ~init:Var.Set.empty
  |> Core.Set.union (ret_set ctx)
  |> Core.Set.filter ~f:(fun var ->
      (not @@ is_mem var) || Var.same var (pc ctx.Convutils.target))
  |> Core.Set.to_list


(* [build_frame_anchor llvm_ctx llvm_builder n anchor_idx min_lo]: Allocates the per-sub [%frame] alloca ([n] bytes, 16-ALIGNED), GEPs to the anchor cell at [anchor_idx], and returns the [(frame, min_lo, anchor_idx, anchor_i64)] frame tuple. *)
let build_frame_anchor llvm_ctx llvm_builder n anchor_idx min_lo =
  let frame =
    Llvm.build_alloca
      (Llvm.array_type (Llvm.i8_type llvm_ctx) (Int64.to_int n))
      "frame" llvm_builder
  in
  Llvm.set_alignment 16 frame;
  let anchor =
    Llvm.build_gep (Llvm.i8_type llvm_ctx) frame
      [| Llvm.const_of_int64 (Llvm.i64_type llvm_ctx) anchor_idx false |]
      "anchor" llvm_builder
  in
  let anchor_i64 =
    Llvm.build_ptrtoint anchor (Llvm.i64_type llvm_ctx) "anchor_i64"
      llvm_builder
  in
  (Some frame, min_lo, anchor_idx, anchor_i64)

let degraded_geometry (sub : sub term) : int64 * int64 * int64 =
  let max_dec = ref 0L in
  let max_neg = ref 0L in
  let max_pos = ref 0L in
  let is_sp_or_fp v =
    let n = Var.name (Var.base v) in
    String.equal n "RSP" || String.equal n "RBP"
  in
  Term.enum blk_t sub
  |> Seq.iter ~f:(fun blk ->
      Term.enum def_t blk
      |> Seq.iter ~f:(fun d ->
          (match Def.rhs d with
          | Bil.BinOp (Bil.MINUS, Bil.Var r, Bil.Int w) when is_sp_or_fp r ->
              let k = Word.to_int64_exn w in
              if Int64.compare k !max_dec > 0 then max_dec := k
          | _ -> ());
          (match Def.rhs d with
          | Bil.Load (_, addr, _, s)
          | Bil.Store (_, addr, _, _, s) ->
              let sz = Int64.of_int (Size.in_bytes s) in
              (match addr with
              | Bil.BinOp (Bil.PLUS, Bil.Var b, Bil.Int w) when is_sp_or_fp b ->
                  let disp = Word.to_int64_exn w in
                  if Int64.compare disp 0L < 0 then
                    let need = Int64.sub (Int64.neg disp) 0L in
                    let need = Int64.add need sz in
                    if Int64.compare need !max_neg > 0 then max_neg := need
                  else
                    let need = Int64.add disp sz in
                    if Int64.compare need !max_pos > 0 then max_pos := need
              | Bil.Int w ->
                  (* absolute address not relevant for frame size *)
                  ()
              | _ -> ())
          | _ -> ())));
  (!max_dec, !max_neg, !max_pos)

let degraded_dims (sub : sub term) : int64 * int64 * int64 * int64 =
  let max_dec, max_neg, max_pos = degraded_geometry sub in
  let deepest = Int64.max max_dec max_neg in
  let deepest = Int64.max deepest 8L in
  let need = Int64.add deepest 8L in
  let n =
    let r = Int64.rem need 16L in
    if Int64.equal r 0L then need else Int64.add need (Int64.sub 16L r)
  in
  let n = Int64.max n 8192L in
  let grown = Int64.add n max_pos in
  let grown =
    let r = Int64.rem grown 16L in
    if Int64.equal r 0L then grown else Int64.add grown (Int64.sub 16L r)
  in
  let anchor_idx = Int64.sub n 8L in
  (n, grown, max_pos, anchor_idx)

(* ------------------------------------------------------------------ *)
(* THE STACK MODEL DECISION — this module is a CONSUMER.                *)
(*                                                                     *)
(* [Hike_stack_to_locals.split_plan] is the single producer; the        *)
(* emitter reads the result it carried in [Convutils.stack_plan] and     *)
(* ALLOCATES what the plan says. The whole-sub rules (degraded,         *)
(* SP-escape, untagged/Infinite/Unbounded/VLA accesses, VLA overlap,    *)
(* the inside/disjoint tag coverage, the region size guard) previously  *)
(* lived here as [region_split_plan] with a SECOND, different escape    *)
(* analysis; they are gone from the emitter — one producer, three       *)
(* consumers (Finding 1).                                              *)
(* ------------------------------------------------------------------ *)

(* [stack_plan_of sub_info]: the sub's stack model decision — the regions
   that become per-region [stack_rN] allocas, or [[]] for the sound
   single-frame fallback. *)
let stack_plan_of (sub_info : Convutils.vsa_info option) : Convutils.split_plan =
  match sub_info with
  | None -> []
  | Some info -> info.Convutils.stack_plan

(* [region_bytes r]: the alloca size of region [r] (16-aligned, at least
   one byte). The one geometric fact the emitter still owns — the
   analysis-side size GUARD ([region_size_ok]) lives with the producer. *)
let region_bytes (r : Convutils.region) : int64 =
  let lo, hi = r.Convutils.span in
  let span_len = Int64.add (Int64.sub hi lo) 1L in
  let raw = Int64.div (Int64.mul span_len (Int64.of_int r.Convutils.max_width)) 8L in
  let raw = if Int64.compare raw 0L <= 0 then 1L else raw in
  let r = Int64.rem raw 16L in
  if Int64.equal r 0L then raw else Int64.add raw (Int64.sub 16L r)

(* [def_tags_of info_opt]: the per-def VSA tag map (the tag lookup the
   emitter needs for its own per-access dispatch). *)
let def_tags_of (info_opt : Convutils.vsa_info option) : Convutils.vsa_kind Tid.Map.t =
  match info_opt with
  | None -> Tid.Map.empty
  | Some info ->
      Base.List.fold info.Convutils.offsets ~init:Tid.Map.empty ~f:(fun m (tid, k) ->
          Core.Map.set m ~key:tid ~data:k)


let create_sub sub =
  let open KB in
  if is_empty sub then (
    Format.eprintf "Skipping sub %s, has no blks\n" (Term.name sub);
    return ())
  else if
    (* the NATIVE-FP-mapped intrinsic subs: their calls are intercepted in [create_call] (the LLVM FP op inline); the soft-float body is never emitted (dead weight — the mapped calls never reach it). *)
    Base.Option.is_some (native_fp_op (Tid.name (Term.tid sub)))
  then (
    Printf.eprintf "Skipping sub %s (native LLVM FP op)\n" (Term.name sub);
    return ())
  else
    let* llvm_ctx = Context.get llvm_ctx_var in
    let* llvm_module = Context.get llvm_module_var in
    let* ctx = Context.get emit_ctx_var in
    Printf.eprintf "Converting sub %s\n" (Term.name sub);
    let blks = Term.enum blk_t sub in
    let fn, _ =
      Core.Map.find !(ctx.Convutils.ll_funcs) (Term.tid sub)
      |> Base.Option.value_exn ~message:"create sub : function not found"
    in
    let llvm_builder = Llvm.builder_at_end llvm_ctx (Llvm.entry_block fn) in
    (* reset llvals and bbs *)
    clear_bbs ctx;
    clear_blk_llvals ctx;
    let transfer_vars = collect_sub_data ctx llvm_ctx blks fn in
    (* The per-sub VSA frame: the tag span [min_lo, max_hi] of [Convutils.vsa_offsets] — every stack access of the sub lands in this alloca (the singleton GEPs and the interval-path dynamic addresses both). *)
    let sub_info = Core.Map.find (Hike_kb.vsa_info ()) (Term.tid sub) in
    let tags =
      sub_info
      |> Base.Option.map ~f:(fun info -> info.Convutils.offsets)
      |> Base.Option.value ~default:[]
    in
    (* THE STACK MODEL DECISION — consumed, not computed (Finding 1):
       [Hike_stack_to_locals.split_plan] produced it in the vsa pass and
       carried it in [vsa_info.stack_plan]. *)
    let plan = stack_plan_of sub_info in
    let is_precise = plan <> [] in
    let frame, min_lo, anchor_idx, anchor_i64 =
      if is_precise then (None, 0L, 0L, Llvm.const_int (Llvm.i64_type llvm_ctx) 0)
      else
        match tags with
        | [] ->
          if sub_degraded sub_info then
            let n, _, _, anchor_idx = degraded_dims sub in
            let frame, _, _, anchor_i64 = build_frame_anchor llvm_ctx llvm_builder n anchor_idx (Int64.neg n) in
            (frame, Int64.neg n, anchor_idx, anchor_i64)
          else (None, 0L, 0L, Llvm.const_int (Llvm.i64_type llvm_ctx) 0)
        | _ ->
          let min_lo, max_hi =
            Base.List.fold tags ~init:(0L, 0L) ~f:(fun (lo, hi) (_, kind) ->
                match kind with
                | Convutils.Range (l, h) | Convutils.Infinite (l, h) ->
                    if Int64.compare l 0L <= 0 then
                      (Int64.min lo l, Int64.max hi h)
                    else (lo, hi)
                | Convutils.Unbounded | Convutils.Dead | Convutils.VLA _ -> (lo, hi))
          in
          let max_hi =
            let clamp_hi h =
              if Int64.compare h 0x40000000L > 0 then min_lo else h
            in
            Base.List.fold tags ~init:0L ~f:(fun acc (_, kind) ->
                match kind with
                | Convutils.Range (l, h) | Convutils.Infinite (l, h) ->
                    if Int64.compare l 0L <= 0 then Int64.max acc (clamp_hi h)
                    else acc
                | Convutils.Unbounded | Convutils.Dead | Convutils.VLA _ -> acc)
          in
          let span = Int64.sub max_hi min_lo in
          let need = Int64.max (Int64.sub 8L min_lo) (Int64.add span 1L) in
          let n =
            Int64.add need 15L |> fun n ->
            Int64.mul (Int64.div n 16L) 16L
          in
          let anchor_idx = Int64.sub n 8L in
          build_frame_anchor llvm_ctx llvm_builder n anchor_idx min_lo
    in
    let regions =
      if is_precise then
        Base.List.mapi plan ~f:(fun _ r ->
            let n = region_bytes r in
            let base =
              Llvm.build_alloca
                (Llvm.array_type (Llvm.i8_type llvm_ctx) (Int64.to_int n))
                (Printf.sprintf "stack_r%d" r.Convutils.id)
                llvm_builder
            in
            Llvm.set_alignment 16 base;
            (r, base))
      else []
    in
    let fr : sub_frame =
      { frame; min_lo; anchor_idx; anchor_i64; stack = None; regions; is_precise }
    in
    add_args_to_vars llvm_builder Graphs.Tid.start (Term.tid sub) fn ()
    >>= build_entry_block llvm_builder transfer_vars fr sub fn
    >>= fun fr -> populate_blks transfer_vars blks sub sub_info fr ()
    >>= update_phis transfer_vars blks sub

let create_empty_llvm_i8array llvm_ctx size =
  Array.init size (fun _ -> Llvm.const_int (Llvm.i8_type llvm_ctx) 0)
  |> Llvm.const_array (Llvm.i8_type llvm_ctx)

let create_uninitialized_global llvm_ctx llvm_module size name =
  let size = Int64.to_int size in
  let ret =
    Llvm.declare_global
      (Llvm.array_type (Llvm.i8_type llvm_ctx) size)
      name llvm_module
  in
  Llvm.set_initializer (create_empty_llvm_i8array llvm_ctx size) ret;
  Llvm.set_global_constant false ret;
  ret

(* [create_copy_reloc_bss ...]: The bss global with the COPY-RELOCATED slots initialized to the extern symbols' addresses (see [Hike.get_copy_relocations]). *)
let create_copy_reloc_bss llvm_ctx llvm_module size name copy_relocs =
  let size = Int64.to_int size in
  let n64 = (size + 7) / 8 in
  let ret =
    Llvm.declare_global
      (Llvm.array_type (Llvm.i64_type llvm_ctx) n64)
      name llvm_module
  in
  let arr =
    Array.init n64 (fun _ -> Llvm.const_int (Llvm.i64_type llvm_ctx) 0)
  in
  Base.List.iter copy_relocs ~f:(fun (off, sym_name) ->
      let extern =
        Llvm.declare_global (Llvm.i8_type llvm_ctx) sym_name llvm_module
      in
      arr.(off / 8)
      <- Llvm.const_ptrtoint extern (Llvm.i64_type llvm_ctx));
  Llvm.set_initializer (Llvm.const_array (Llvm.i64_type llvm_ctx) arr) ret;
  Llvm.set_global_constant false ret;
  ret

let create_prog ctx llvm_ctx llvm_module section_list proj =
  Toplevel.exec
    begin
      KB.Context.with_var emit_ctx_var ctx (fun () ->
          KB.Context.with_var llvm_ctx_var llvm_ctx (fun () ->
              KB.Context.with_var llvm_module_var llvm_module (fun () ->
                  KB.Context.with_var section_list_var section_list (fun () ->
                      KB.Seq.iter
                        (Term.enum sub_t (Project.program proj))
                        ~f:(fun s -> create_sub s)))))
    end
