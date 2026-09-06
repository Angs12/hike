open Bap.Std.Bil.Types
open Bap.Std
open Hike_abi
module Abi = Hike_abi
open Convutils

(* Core Hashtbl with the deprecated warning off. *)
module EHashtbl = Core_kernel.Hashtbl[@warning "-D"]
module KB = Bap_knowledge.Knowledge
module Vsa = Cbat_vsa
module AI = Cbat_vsa.AI
module Mem = Cbat_vsa.Mem
module Ws = Cbat_clp_set_composite

(* Emission context threaded as a KB var. *)

(* Finds the LLVM function at a native address. *)
let lookup_native_fn ctx llvm_module v =
  match ctx.Convutils.symtab with
  | Some symtab -> (
      match Symtab.find_by_start symtab (Word.of_int64 ~width:64 v) with
      | Some (name, _, _) -> Llvm.lookup_function name llvm_module
      | None -> None)
  | None -> None

(* Remaps a native address to its lifted value. *)
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

(* Declares a section global as [n x i64]. *)
let create_section_global llvm_ctx llvm_module size name ~is_const =
  let n64 = (size + 7) / 8 in
  let ret =
    Llvm.declare_global
      (Llvm.array_type (Llvm.i64_type llvm_ctx) n64)
      name llvm_module
  in
  Llvm.set_global_constant is_const ret;
  ret

(* Reads a stashed .text constant. *)
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

(* Builds a remapped section initializer. *)
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

(* Per-sub frame state. *)
type sub_frame = {
  frame : Llvm.llvalue option;
  (* Anchor byte index. *)
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

(* Default emission context. *)
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

(* Tests for FP arg registers. *)
let is_fp_param (v : var) : bool =
  Base.String.is_prefix (Var.name (Var.base v)) ~prefix:Abi.vector_param_prefix

let is_extern ctx (sub_tid : tid) : bool =
  not (Core.Map.mem ctx.Convutils.subs sub_tid)

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
  (* Extern declares are variadic. *)
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
  (* Uses explicit rets/args. *)
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

(* Coerces binop operands to one type. *)
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

(* Returns an expression bitwidth. *)
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
    (* Out-of-range extracts yield zero. *)
    return @@ Llvm.const_int (Llvm.integer_type llvm_ctx result_size) 0
  else
    let temp_var =
      Llvm.build_lshr llvm_var
        (Llvm.const_int (Llvm.type_of llvm_var) lo)
        "" llvm_builder
    in
    if result_size >= width then
      (* Wide extracts zero-extend. *)
      return
      @@ Llvm.build_zext temp_var
           (Llvm.integer_type llvm_ctx result_size) "" llvm_builder
    else
      return
      @@ Llvm.build_trunc temp_var
           (Llvm.integer_type llvm_ctx result_size) "" llvm_builder

(* Finds the section containing a word address. *)
let section_of_addr sections (addr : word) =
  Base.List.find sections ~f:(fun section ->
      Word.between ~low:section.min_addr addr ~high:section.max_addr)

let resolve_addr llvm_builder addr =
  let open KB in
  let* llvm_ctx = Context.get llvm_ctx_var in
  let* sections = Context.get section_list_var in
  let section = section_of_addr sections addr in
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

(* Section load with copy-reloc through-load. *)
let section_load llvm_builder llvm_ctx addr addr_i64 size =
  let open KB in
  let* ctx = Context.get emit_ctx_var in
  let* base = resolve_addr llvm_builder addr in
  if
    Base.List.exists ctx.Convutils.copy_relocs ~f:(fun a ->
        Int64.equal a addr_i64)
  then
    (* Loads through copy-relocated pointers. *)
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
      (* Reads stashed .text bytes first. *)
      let addr_w = Word.of_int64 ~width:64 v in
      let* pre =
        match
          text_load_constant ctx llvm_builder llvm_ctx llvm_module addr_w size
        with
        | Some c -> return c
        | None ->
            if Option.is_some (section_of_addr sections addr_w)
            then section_load llvm_builder llvm_ctx addr_w v size
            else
              let* ptr = create_inttoptr llvm_builder addr in
              return
              @@ Llvm.build_load (Llvm.integer_type llvm_ctx size) ptr ""
                   llvm_builder
      in
      return pre
  | _ ->
      (* Non-constant addresses use inttoptr. *)
      let* addr = create_inttoptr llvm_builder addr in
      return
      @@ Llvm.build_load (Llvm.integer_type llvm_ctx size) addr ""
           llvm_builder
let create_store llvm_builder (llvm_var, addr) =
  let open KB in
  let* llvm_ctx = Context.get llvm_ctx_var in
  let* sections = Context.get section_list_var in
  match Llvm.int64_of_const addr with
  | Some v
    when Option.is_some
           (section_of_addr sections (Word.of_int64 ~width:64 v)) ->
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
  (* Remaps native function constants. *)
  (* Remap applies to <=64-bit words. *)
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

(* Warns on reads of never-defined vars. *)
let warn_undef_read ctx var blk_tid =
  let v = Var.base var in
  let abi = Abi.of_target ctx.Convutils.target in
  let is_lane = Abi.is_vector_param_reg abi v || Abi.is_return_reg abi v in
  let sub_key = blk_tid in
  let warned_vars =
    match Core.Map.find !(ctx.Convutils.undef_warned) sub_key with
    | Some r -> r
    | None ->
        let r = ref Var.Set.empty in
        ctx.Convutils.undef_warned :=
          Core.Map.set !(ctx.Convutils.undef_warned) ~key:sub_key ~data:r;
        r
  in
  if not (Core.Set.mem !warned_vars v) then begin
    warned_vars := Core.Set.add !warned_vars v;
    if not is_lane then
      Hike_diag.warn "undef-read: blk %s: var %s never defined"
        (Tid.name blk_tid) (Var.name v)
  end

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
      (* Width-family fallback, else undef. *)
      match get_local ctx blk_tid v with
      | Some x -> return x
      | None ->
          let* llvm_ctx' = Context.get llvm_ctx_var in
          let want_w =
            match Var.typ v with Type.Imm w -> w | _ -> 64
          in
          match Convutils.probe_local_family ctx blk_tid v ~want_w with
          | Some (val_at_w, bound_w) ->
              let want_ty = Llvm.integer_type llvm_ctx' want_w in
              if bound_w = want_w then return val_at_w
              else if bound_w > want_w then
                return @@ Llvm.build_trunc val_at_w want_ty "" llvm_builder
              else
                return @@ Llvm.build_zext val_at_w want_ty "" llvm_builder
          | None ->
              warn_undef_read ctx v blk_tid;
              !$Llvm.undef (typ_lltype_m (Var.typ v)))
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
  (* Fissioned AND ordinary memory ops emit identically: the rewrite
     already materialized region storage into the address, so by emission
     there is nothing left to dispatch on (the former mem-operand guard
     arms were byte-identical to these fallthroughs and are deleted). *)
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
      (* Remaps function and section addresses. *)
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
      (match Llvm.int64_of_const addr with
       | Some i64 ->
           let* addr = resolve_addr llvm_builder (Word.of_int64 ~width:64 i64) in
           let* data = create_exp llvm_builder blk_tid data in
           return @@ Llvm.build_store data addr llvm_builder
       | None ->
           (* Stores through remapped constants. *)
           let* data = create_exp llvm_builder blk_tid data in
           create_store llvm_builder (data, addr))
  | Load (_, addr, _, size) ->
      let* addr = create_exp llvm_builder blk_tid addr in
      (match Llvm.int64_of_const addr with
       | Some i64 ->
           let addr = Word.of_int64 ~width:64 i64 in
           let addr_i64 = Word.to_int64_exn addr in
           let size = Size.in_bits size in
           (* Reads .text loads at compile time. *)
           let* loaded =
             match
               text_load_constant ctx llvm_builder llvm_ctx llvm_module addr size
             with
             | Some c -> return c
             | None -> section_load llvm_builder llvm_ctx addr addr_i64 size
           in
           return loaded
       | None ->
           (* Loads via inttoptr on remapped constants. *)
           create_load llvm_builder (addr, Size.in_bits size))
  | Cast (cast, i, (Load _ as load)) ->
      (* RIP-relative widening loads. *)
      let* v = create_rip_relative_addr llvm_builder blk_tid load in
      create_cast llvm_builder (cast, i, v)
  | _ -> create_exp llvm_builder blk_tid exp

let create_branches blk_tid llvm_builder branches =
  let open KB in
  let open Bap.Std in
  let* ctx = KB.Context.get emit_ctx_var in
  if Seq.length branches = 1 then 
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

(* Looks up a def VSA tag. *)
let find_def_tag sub_info def =
  Base.Option.bind sub_info ~f:(fun info ->
      Core.Map.find info.Convutils.offsets (Term.tid def))



(* Tests for visible storage via the stack model. *)
let is_abi_visible ctx sub_info def =
  match sub_info with
  | None -> false
  | Some info ->
      Hike_stack_model.abi_visibility_of (sp ctx.Convutils.target) info def

(* A stack access carries a [vsa_info] tag — the invariant is structural
   (spec §2.2): an access is a stack access iff it is tagged. *)
let has_vsa_info sub_info def = Option.is_some (find_def_tag sub_info def)

(* Tests for PLT stubs. *)
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

(* Emits a singleton-tagged access. *)
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
      (* Finds the first memory node. *)
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
           (* Store nodes bind data, not void stores. *)
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
#ifdef VSA_DEBUG
      Printf.eprintf "hike: create_static_mem_access fallback lo=%Ld no frame/stack -> dynamic\n" lo;
#endif
      create_exp llvm_builder blk_tid exp

(* Singleton tags use const GEPs. *)
(* Rebases positive-interval addresses onto the stack. *)
let rebase_addr llvm_builder fr addr =
  let open KB in
  let stack =
    Base.Option.value_exn fr.stack
      ~message:"rebase_addr: positive interval but no stack param"
  in
  let offset = Llvm.build_sub addr fr.anchor_i64 "arg_off" llvm_builder in
  return @@ Llvm.build_add stack offset "arg_addr" llvm_builder

(* Emits runtime-sized allocas. *)
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

(* Loads/stores through a computed address. *)
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

(* Finds the region containing an offset. *)
let region_of_offset (regions : (Convutils.region * Llvm.llvalue) list)
    (lo : int64) : (Convutils.region * Llvm.llvalue) option =
  Base.List.find regions ~f:(fun (r, _) ->
      let rlo, rhi = r.Convutils.span in
      Int64.compare lo rlo >= 0 && Int64.compare lo rhi <= 0)

(* Dispatches tagged accesses to storage. *)
let mem_access llvm_builder blk_tid sub_tid sub_info fr
    (def : def term) (exp : exp) =
  
  let open KB in
  let* ctx = Context.get emit_ctx_var in
  let var = Def.lhs def in
  match find_def_tag sub_info def with
  | Some (Convutils.Range (lo, hi))
    when Int64.equal lo hi && has_vsa_info sub_info def ->
      if Int64.compare lo 0L > 0 then
        (* Incoming-arg cells read via [hike_stack]. *)
        (match fr.stack with
        | Some _ -> create_static_mem_access llvm_builder blk_tid fr lo exp
        | None -> create_exp llvm_builder blk_tid exp)
      else if is_abi_visible ctx sub_info def then
        (* Outgoing cells use their own address. *)
        (match Def.rhs def with
        | Bil.Load (_, addr, _, _) | Bil.Store (_, addr, _, _, _) ->
            let* addr_v = create_exp llvm_builder blk_tid addr in
            mem_access_via_ptr llvm_builder blk_tid addr_v exp
        | _ -> create_exp llvm_builder blk_tid exp)
      else
        (* Locals use static frame GEPs. *)
        create_static_mem_access llvm_builder blk_tid fr lo exp
  | Some (Convutils.Range (lo, _) | Convutils.Infinite (lo, _))
    when Int64.compare lo 0L > 0 && has_vsa_info sub_info def ->
      (* Positive intervals rebase onto the stack. *)
      (match Def.rhs def with
      | Bil.Load (_, addr, _, _) | Bil.Store (_, addr, _, _, _) ->
          let* addr_v = create_exp llvm_builder blk_tid addr in
          let* addr_v = rebase_addr llvm_builder fr addr_v in
          mem_access_via_ptr llvm_builder blk_tid addr_v exp
      | _ -> create_exp llvm_builder blk_tid exp)
  | Some (Convutils.VLA _) -> create_exp llvm_builder blk_tid exp
  | Some Convutils.Unbounded ->
      if has_vsa_info sub_info def then begin
        if not (Core.Set.mem !(ctx.Convutils.guarded_warned) sub_tid) then begin
          ctx.Convutils.guarded_warned :=
            Core.Set.add !(ctx.Convutils.guarded_warned) sub_tid;
          (* Warning text is a grepped contract. *)
          Hike_diag.warn
            "guarded: sub %s: stack access is Unbounded (unconstrained / TOP): def %s rhs=%s"
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
      if has_vsa_info sub_info def then
        failwith
          (Printf.sprintf
             "hike: 100%% VSA Tagging invariant violated: sub %s def %s has no VSA tag"
             (Tid.name sub_tid) (Tid.name (Term.tid def)))
      else create_exp llvm_builder blk_tid exp

let create_def blk_tid llvm_builder sub_tid sub_info fr alloc_tids def =
  
  let open KB in
  let* ctx = Context.get emit_ctx_var in
  let var = Def.lhs def in
  let v = Def.value def in
  let exp = Def.rhs def in
  let* res =
    (* Runtime-sized SP decrements become real allocas (spec §2.3). *)
    if Core.Set.mem alloc_tids (Term.tid def) then
      create_dynamic_alloc llvm_builder blk_tid exp
    else if KB.Value.get rip_relative_addr v then
      create_rip_relative_addr llvm_builder blk_tid exp
    else if fr.is_precise then
      (* Split-model accesses use region GEPs. *)
      (match find_def_tag sub_info def with
       | Some (Convutils.Range (lo, hi))
         when Int64.equal lo hi && has_vsa_info sub_info def ->
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

(* Restores SP after calls. *)
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
  let* ctx = Context.get emit_ctx_var in
  let* llvm_ctx = Context.get llvm_ctx_var in
  let args = get_args ctx call_tid in
  let extern = is_extern ctx call_tid in
  KB.List.map args ~f:(fun arg ->
      let exp = Arg.rhs arg in
      if Var.same (Arg.lhs arg) Convutils.hike_stack_var then
        (* Threads [hike_stack] to callees. *)
        let first, second =
          if fr.is_precise then Convutils.hike_stack_var, sp ctx.Convutils.target
          else sp ctx.Convutils.target, Convutils.hike_stack_var
        in
        let v_opt =
          match get_local ctx blk_tid first with
          | Some _ as v -> v
          | None -> get_local ctx blk_tid second
        in
        match v_opt with
        | Some v -> return v
        | None ->
            let* llvm_ctx = Context.get llvm_ctx_var in
            (* Missing [hike_stack] lanes yield undef. *)
            return @@ Llvm.undef (Llvm.i64_type llvm_ctx)
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

let get_func tid =
  let open KB in
  let* ctx = Context.get emit_ctx_var in
  match Core.Map.find !(ctx.Convutils.ll_funcs) tid with
  | Some v -> return v
  | None ->
      let* _ = create_fun_declaration tid in
      return @@ Core.Map.find_exn !(ctx.Convutils.ll_funcs) tid
let create_indirect_call llvm_builder blk_tid call fr =
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
    create_call_args blk_tid llvm_builder (Tid.for_name "indirect_call") fr
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

(* Emits trap edges. *)
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

(* Tests for 32-bit sources. *)
let rec has_32bit_extract (e : exp) : bool =
  match e with
  | Bil.Extract (31, _, _) -> true
  | Bil.Extract (_, _, e') -> has_32bit_extract e'
  | Bil.BinOp (_, a, b) -> has_32bit_extract a || has_32bit_extract b
  | Bil.Cast (_, _, e') -> has_32bit_extract e'
  | _ -> false

(* Returns a cast source width. *)
let cast_source_width ~(abi : Abi.t) (sub : sub term) (blk : blk term) : int =
  let u32_slots =
    Term.enum blk_t sub
    |> Seq.fold ~init:[] ~f:(fun acc b ->
        Term.enum def_t b
        |> Seq.fold ~init:acc ~f:(fun acc d ->
            match Def.rhs d with
            | Bil.Store (_, addr, _, _, s) when Size.in_bits s = 32 -> (
                match addr with
                | Bil.BinOp (Bil.PLUS, Bil.Var bv, Bil.Int w)
                  when Abi.is_fp abi (Var.base bv) ->
                    Word.to_int64_exn w :: acc
                | Bil.Var bv when Abi.is_fp abi (Var.base bv) ->
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
            when Abi.is_fp abi (Var.base bv) ->
              if Base.List.mem ~equal:Int64.equal u32_slots (Word.to_int64_exn w)
              then 32
              else 64
          | _ -> 64)
      | _ -> 64)

(* Builds a width-aware FP binop. *)
(* Returns width-derived FP/int types. *)
let fp_ty_of (llvm_ctx : Llvm.llcontext) (w : int) :
    Llvm.lltype * Llvm.lltype =
  ( (if w <= 32 then Llvm.float_type llvm_ctx
     else Llvm.double_type llvm_ctx),
    (if w <= 32 then Llvm.i32_type llvm_ctx else Llvm.i64_type llvm_ctx) )

let build_fp_binop llvm_builder op a b ~(w : int) =
  let open KB in
  let* llvm_ctx = Context.get llvm_ctx_var in
  let fp_ty, ret_ty = fp_ty_of llvm_ctx w in
  let bitcast v =
    if Llvm.classify_type (Llvm.type_of v) = Llvm.TypeKind.Integer then
      Llvm.build_bitcast v fp_ty "" llvm_builder
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
    | SFLOAT | SINT | FORDER | FHLT | ISNAN -> assert false
  in
  return
  @@ Llvm.build_bitcast d ret_ty "" llvm_builder

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
let create_native_fp_call llvm_builder blk_tid blk sub call op =
  let open KB in
  let* llvm_ctx = Context.get llvm_ctx_var in
  let* ctx = Context.get emit_ctx_var in
  let abi = Abi.of_target ctx.Convutils.target in
  let fallthrough = Option.map label_tid (Call.return call) in
  let target = Call.target call |> label_tid in
  let args = get_args ctx target in
  (* Widths come from declared types. *)
  let rets = get_rets ctx target in
  let in_w, res_w = fp_intrinsic_sizes args rets in
  let arg_value (i : int) : Llvm.llvalue KB.t =
    (* Resolves operands from declared arg vars. *)
    let arg = Base.List.nth_exn args i in
    let av = Var.base (Arg.lhs arg) in
    let x_def_opt =
      Term.enum def_t blk
      |> Base.Sequence.to_list
      |> Base.List.filter ~f:(fun d -> Var.same (Var.base (Def.lhs d)) av)
      |> Base.List.last
    in
    match x_def_opt with
    | Some d -> create_exp llvm_builder blk_tid (Def.rhs d)
    | None -> create_exp llvm_builder blk_tid (Arg.rhs arg)
  in
  (* Integer width of a value, defaulting to the declared input width. *)
  let w_of v =
    match Llvm.classify_type (Llvm.type_of v) with
    | Llvm.TypeKind.Integer -> Llvm.integer_bitwidth (Llvm.type_of v)
    | _ -> in_w
  in
  let result =
    match op with
    | FMUL | FADD | FSUB | FDIV | FREM ->
        (* Operand width comes from values. *)
        let* a = arg_value 0 in
        let* b = arg_value 1 in
        let w = min (w_of a) (w_of b) in
        build_fp_binop llvm_builder op a b ~w
    | SFLOAT ->
        (* Int-to-FP casts use source width. *)
        let* x = arg_value 0 in
        let src_w = cast_source_width ~abi sub blk in
        let int_src_ty =
          if src_w = 32 then Llvm.i32_type llvm_ctx
          else Llvm.i64_type llvm_ctx
        in
        let x =
          if src_w = 32
             && Llvm.classify_type (Llvm.type_of x) = Llvm.TypeKind.Integer
             && Llvm.integer_bitwidth (Llvm.type_of x) > 32
          then Llvm.build_trunc x int_src_ty "" llvm_builder
          else x
        in
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
        let src_w =
          match Llvm.classify_type (Llvm.type_of x) with
          | Llvm.TypeKind.Integer -> Llvm.integer_bitwidth (Llvm.type_of x)
          | _ -> in_w
        in
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
        let bitcast v =
          if Llvm.classify_type (Llvm.type_of v) = Llvm.TypeKind.Integer then
            Llvm.build_bitcast v src_fp_ty "" llvm_builder
          else v
        in
        let* p =
          KB.return
          @@ Llvm.build_fcmp Llvm.Fcmp.Olt (bitcast a) (bitcast b) ""
               llvm_builder
        in
        return @@ Llvm.build_zext p (Llvm.i64_type llvm_ctx) "" llvm_builder
    | ISNAN ->
        (* NaN test via fcmp uno. *)
        let* x = arg_value 0 in
        let w =
          match Llvm.classify_type (Llvm.type_of x) with
          | Llvm.TypeKind.Integer -> Llvm.integer_bitwidth (Llvm.type_of x)
          | _ -> in_w
        in
        let src_fp_ty, _ = fp_ty_of llvm_ctx w in
        let xf =
          if Llvm.classify_type (Llvm.type_of x) = Llvm.TypeKind.Integer then
            Llvm.build_bitcast x src_fp_ty "" llvm_builder
          else x
        in
        let* p =
          KB.return
          @@ Llvm.build_fcmp Llvm.Fcmp.Uno xf xf "" llvm_builder
        in
        return @@ Llvm.build_zext p (Llvm.i64_type llvm_ctx) "" llvm_builder
    | FHLT ->
        (* Halt traps without binding results. *)
        let* () = create_interrupt llvm_builder in
        return (Llvm.poison (Llvm.i64_type llvm_ctx))
  in
  let* r = result in
  (match get_rets ctx target with
   | [ ret ] ->
     (* Binds the primary ret lane width-aware. *)
     let lane_w =
       match Var.typ (Arg.lhs ret) with Type.Imm w -> w | _ -> 64
     in
     let r_bits = try Llvm.integer_bitwidth (Llvm.type_of r) with _ -> 64 in
     let r_lane =
       if r_bits = lane_w then r
       else if r_bits > lane_w then
         Llvm.build_trunc r (Llvm.integer_type llvm_ctx lane_w) "" llvm_builder
       else
         Llvm.build_zext r (Llvm.integer_type llvm_ctx lane_w) ""
           llvm_builder
     in
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
           let v =
             if r_bits = lw then r
             else if r_bits > lw then
               Llvm.build_trunc r (Llvm.integer_type llvm_ctx lw) ""
                 llvm_builder
             else
               Llvm.build_zext r (Llvm.integer_type llvm_ctx lw) ""
                 llvm_builder
           in
           insert_local ctx blk_tid (Arg.lhs ret2) v
         end)
   | _ -> ());
  (match fallthrough with
   | Some ft ->
       let bb = get_bb ctx ft in
       ignore (Llvm.build_br bb llvm_builder);
       KB.return ()
   | None ->
       ignore (Llvm.build_unreachable llvm_builder);
       KB.return ())

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
        let v_ty = Llvm.type_of v in
        let ty_cls = Llvm.classify_type v_ty in
        if ty_cls = Llvm.TypeKind.Integer
           && Llvm.integer_bitwidth v_ty < 64 then
          KB.return @@ Llvm.build_zext v (Llvm.i64_type llvm_ctx) ""
            llvm_builder
        else if ty_cls = Llvm.TypeKind.Integer
                && Llvm.integer_bitwidth v_ty > 64 then
          KB.return @@ Llvm.build_trunc v (Llvm.i64_type llvm_ctx) ""
            llvm_builder
        else KB.return v)
      args
  in
  let r = Llvm.build_call fn_ty callee
      (Array.of_list arg_vals) "" llvm_builder in
  (match get_rets ctx target with
   | [ ret ] -> insert_local ctx blk_tid (Arg.lhs ret) r
   | _ -> ());
  (match Option.map label_tid (Call.return call) with
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
    (* Interrupt calls trap. *)
    create_interrupt llvm_builder
  else
    match native_fp_op (Tid.name target) with
    | Some op -> create_native_fp_call llvm_builder blk_tid blk sub call op
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
  (* Consults edge-keyed restores first. *)
  let edge_val (pred_tid : tid) (var : var) : Llvm.llvalue option =
    if Var.same var (sp ctx.Convutils.target) then
      match EHashtbl.find !(ctx.edge_sp_restores) pred_tid with
      | Some inner -> EHashtbl.find inner blk_tid
      | None -> None
    else None
  in
  KB.List.iter transfer_vars ~f:(fun var ->
      let phi_llvar = get_phi ctx blk_tid var in
      Seq.iter blk_incoming ~f:(fun tid ->
          let phi_reg =
            match edge_val tid var with
            | Some v -> Some v
            | None -> get_local ctx tid var
          in
          match phi_reg with
          | Some phi_reg ->
              Llvm.add_incoming (phi_reg, get_bb ctx tid) phi_llvar;
              return ()
          | None -> failwith "update_phi: phi_reg not found"))

(* Counts edge multiplicities. *)
let edge_counts_of_sub (sub : sub term) :
    (Tid.t, (Tid.t, int) EHashtbl.t) EHashtbl.t =
  let edge_count = EHashtbl.create (module Tid) in
  let bump (ptid : Tid.t) (t : Tid.t) : unit =
    let inner =
      match EHashtbl.find edge_count ptid with
      | Some h -> h
      | None ->
          let h = EHashtbl.create (module Tid) in
          EHashtbl.set edge_count ~key:ptid ~data:h;
          h
    in
    let cur = match EHashtbl.find inner t with Some n -> n | None -> 0 in
    EHashtbl.set inner ~key:t ~data:(cur + 1)
  in
  Term.enum blk_t sub
  |> Seq.iter ~f:(fun pb ->
      let ptid = Term.tid pb in
      Term.enum jmp_t pb
      |> Seq.iter ~f:(fun j ->
          match Jmp.kind j with
          | Goto (Direct t) | Ret (Direct t) -> bump ptid t
          | _ -> ()));
  edge_count

let update_phis transfer_vars blks sub () =
  let open KB in
  let edge_count = edge_counts_of_sub sub in
  let cfg = Sub.to_graph sub in
  Seq.iter blks ~f:(fun blk ->
      let blk_tid = Term.tid blk in
      (* Phis need one entry per edge. *)
      let blk_incoming =
        Graphs.Tid.Node.preds blk_tid cfg
        |> Base.Sequence.to_list
        |> Base.List.concat_map ~f:(fun ptid ->
            let n =
              match
                EHashtbl.find edge_count ptid
                |> Base.Option.bind ~f:(fun h -> EHashtbl.find h blk_tid)
              with
              | Some n -> n
              | None -> 1
            in
            Base.List.init n ~f:(fun _ -> ptid))
        |> Base.Sequence.of_list
      in
      update_phi transfer_vars blk_incoming blk_tid)

(* Int edges trap. *)
let create_control_flow llvm_builder blk sub fr () =
  let control_flow = Term.enum jmp_t blk in
  let tid = Term.tid blk in
  if Seq.is_empty control_flow then
    (* Def-only blocks return implicitly. *)
    create_return tid llvm_builder sub
  else
  match cf_type control_flow with
  | Br -> create_branches tid llvm_builder control_flow
  | Int -> create_interrupt llvm_builder
  | Ret -> create_return tid llvm_builder sub
  | CallIndirect ->
      let call = Bap.Std.Seq.hd_exn control_flow |> call_exn in
      create_indirect_call llvm_builder (Term.tid blk) call fr
  | CallFun ->
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

let create_elts llvm_builder blk sub_tid sub_info fr alloc_tids () =
  let open KB in
  let tid = Term.tid blk in
  Blk.elts blk
  |> Seq.iter ~f:(fun elt ->
      match elt with
      | `Def def -> create_def tid llvm_builder sub_tid sub_info fr alloc_tids def
      | `Phi _ -> return ()
      | `Jmp _ -> return ())

let populate_blks transfer_vars blks sub sub_info fr () =
  let open KB in
  let* llvm_ctx = Context.get llvm_ctx_var in
  let* ctx = Context.get emit_ctx_var in
  let sub_tid = Term.tid sub in
  (* VLA tids travel in vsa_info (spec §2.3): the producer detected them
     once on the pre-rewrite sub. Missing info degrades to none. *)
  let alloc_tids =
    Base.Option.value_map sub_info ~default:Tid.Set.empty
      ~f:(fun info -> info.Convutils.vla_alloc_tids)
  in
  Seq.iter blks ~f:(fun blk ->
      let llvm_builder =
        Llvm.builder_at_end llvm_ctx (get_bb ctx (Term.tid blk))
      in
      transfer_with_phis transfer_vars llvm_builder (Term.tid blk) ()
      >>= create_elts llvm_builder blk sub_tid sub_info fr alloc_tids
      >>= create_control_flow llvm_builder blk sub fr)


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
        | None ->
            (* Unbound transfer vars yield undef. *)
            !$Llvm.undef (var_lltype var)
      in
      !$(insert_local ctx tid var) llval)
  >>= fun () ->
  if fr.is_precise then (
    (* Precise subs keep [hike_stack], erase SP. *)
    let fr = { fr with stack = get_local ctx tid Convutils.hike_stack_var } in
    exit_entry llvm_builder sub () >>= fun _ -> return fr
  ) else (
  (* SP/FP are not args. *)
  insert_local ctx tid (sp ctx.Convutils.target) fr.anchor_i64;
  (* [hike_stack] is the caller entry RSP. *)
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

(* Builds blocks and transfer set in one walk. *)
let collect_sub_data ctx llvm_ctx blks fn sub =
  insert_bb ctx Graphs.Tid.start (Llvm.entry_block fn);
  init_blk_llvals ctx Graphs.Tid.start;
  (* Transfer set includes call-arg regs. *)
  (* Phi lanes need definedness. *)
  let defined_and_transfered =
    Seq.fold blks
      ~f:(fun (reg_set, def_set) blk ->
        let tid = Term.tid blk in
        init_blk_llvals ctx tid;
        insert_bb ctx tid (Llvm.append_block llvm_ctx (Term.name blk) fn);
        let blk_free = Blk.free_vars blk in
        let call_args, call_rets =
          Term.enum jmp_t blk
          |> Seq.fold ~init:(Var.Set.empty, Var.Set.empty) ~f:(fun (acc, rets) jmp ->
              match Jmp.kind jmp with
              | Call c -> (
                  let rets, args =
                    match Call.target c with
                    | Direct ctid ->
                        ( Base.List.fold (get_rets ctx ctid) ~init:rets
                            ~f:(fun acc arg -> Core.Set.add acc (Var.base (Arg.lhs arg))),
                          get_args ctx ctid )
                    | Indirect _ ->
                        (* Indirect callees bind all ret regs. *)
                        ( Core.Set.union rets (ret_set ctx),
                          [] )
                  in
                  ( Base.List.fold args ~init:acc ~f:(fun acc arg ->
                        Core.Set.add acc (Var.base (Arg.lhs arg))),
                    rets ))
              | _ -> (acc, rets))
        in
        let blk_defs =
          Blk.elts blk
          |> Seq.fold ~init:Var.Set.empty ~f:(fun acc elt ->
                 match elt with
                 | `Def def -> Core.Set.add acc (Var.base (Def.lhs def))
                 (* Phi lhs counts as defined. *)
                 | `Phi phi -> Core.Set.add acc (Var.base (Phi.lhs phi))
                 | _ -> acc)
        in
        ( Core.Set.union (Core.Set.union reg_set (Core.Set.union blk_free call_args))
            call_rets,
          Core.Set.union (Core.Set.union def_set blk_defs) call_rets ))
      ~init:(Var.Set.empty, Var.Set.empty)
  in
  let reg_set, def_set = defined_and_transfered in
  let arg_set =
    Base.List.fold (get_args ctx (Term.tid sub)) ~init:Var.Set.empty
      ~f:(fun acc arg -> Core.Set.add acc (Var.base (Arg.lhs arg)))
  in
  (* [def_set] never joins the transfer set. *)
  reg_set
  |> Core.Set.union (ret_set ctx)
  |> Core.Set.union arg_set
  |> Core.Set.filter ~f:(fun var ->
      ((not @@ is_mem var) || Var.same var (pc ctx.Convutils.target))
      (* Keeps SP/FP lanes. *)
      || Var.same var (sp ctx.Convutils.target)
      || Var.same var (fp ctx.Convutils.target))
  |> Core.Set.filter ~f:(fun var ->
      (* Drops never-defined vars from transfer. *)
      Core.Set.mem def_set var
      || Hike_stack_model.is_region_base var
      || Core.Set.mem arg_set var
      || Var.same var (sp ctx.Convutils.target)
      || Var.same var (fp ctx.Convutils.target))
  |> Core.Set.to_list


(* Allocates the per-sub frame. *)
let build_frame_anchor llvm_ctx llvm_builder n anchor_idx =
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
  (Some frame, anchor_idx, anchor_i64)

let degraded_geometry ~(abi : Abi.t) (sub : sub term) : int64 * int64 * int64 =
  let max_dec = ref 0L in
  let max_neg = ref 0L in
  let max_pos = ref 0L in
  let is_sp_or_fp v = Abi.is_stack_reg abi (Var.base v) in
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
                  
                  ()
              | _ -> ())
          | _ -> ())));
  (!max_dec, !max_neg, !max_pos)

let degraded_dims ?(abi : Abi.t = Abi.x86_64_sysv)
    (sub : sub term) : int64 * int64 * int64 * int64 =
  let max_dec, max_neg, max_pos = degraded_geometry ~abi sub in
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


(* Stack model decision is consumed here. *)











let create_sub sub =
  let open KB in
  if is_empty sub then return ()
  else if
    (* Skips soft-float bodies for mapped intrinsics. *)
    Base.Option.is_some (native_fp_op (Tid.name (Term.tid sub)))
  then return ()
  else
    let* llvm_ctx = Context.get llvm_ctx_var in
    let* llvm_module = Context.get llvm_module_var in
    let* ctx = Context.get emit_ctx_var in
    let blks = Term.enum blk_t sub in
    let fn, _ =
      Core.Map.find !(ctx.Convutils.ll_funcs) (Term.tid sub)
      |> Base.Option.value_exn ~message:"create sub : function not found"
    in
    let llvm_builder = Llvm.builder_at_end llvm_ctx (Llvm.entry_block fn) in
    
    clear_bbs ctx;
    clear_blk_llvals ctx;
    let abi = Abi.of_target ctx.Convutils.target in
    let transfer_vars = collect_sub_data ctx llvm_ctx blks fn sub in
    (* Frame spans all tagged accesses. *)
    let sub_info = Core.Map.find (Hike_kb.vsa_info ()) (Term.tid sub) in
    
    let tags = match sub_info with
      | Some info -> info.Convutils.offsets
      | None -> Tid.Map.empty
    in    (* Consumes the stack plan. *)
    let plan =
      match sub_info with
      | None -> []
      | Some info -> info.Convutils.stack_plan
    in
    let is_precise = plan <> [] in
    let frame, anchor_idx, anchor_i64 =
      if is_precise then (None, 0L, Llvm.const_int (Llvm.i64_type llvm_ctx) 0)
      else if Core.Map.is_empty tags then begin
          if Base.Option.value_map sub_info ~default:false ~f:(fun info ->
                info.Convutils.degraded) then begin            let n, _, _, anchor_idx = degraded_dims ~abi sub in
            let frame, _, anchor_i64 = build_frame_anchor llvm_ctx llvm_builder n anchor_idx in
            (frame, anchor_idx, anchor_i64)
          end
          else (None, 0L, Llvm.const_int (Llvm.i64_type llvm_ctx) 0)
        end
        else begin          let min_lo, max_hi =
            Core.Map.fold tags ~init:(0L, 0L)
              ~f:(fun ~key:_ ~data:kind (lo, hi) ->
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
            Core.Map.fold tags ~init:0L
              ~f:(fun ~key:_ ~data:kind acc ->                match kind with
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
          build_frame_anchor llvm_ctx llvm_builder n anchor_idx
        end
    in
    let regions =
      if is_precise then
        Base.List.mapi plan ~f:(fun _ r ->
            let n = Hike_stack_model.region_bytes r in
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
    (* Binds region bases to alloca cell-0. *)
    let* () =
      let rec bind_regions = function
        | [] -> return ()
        | (r, base) :: rest ->
            let base_var = Hike_stack_model.region_base r.Convutils.id in
            insert_local ctx Graphs.Tid.start base_var base;
            bind_regions rest
      in
      bind_regions regions
    in
    let fr : sub_frame =
      { frame; anchor_idx; anchor_i64; stack = None; regions; is_precise }
    in
    add_args_to_vars llvm_builder Graphs.Tid.start (Term.tid sub) fn ()
    >>= build_entry_block llvm_builder transfer_vars fr sub fn
    >>= fun fr -> populate_blks transfer_vars blks sub sub_info fr ()
    >>= update_phis transfer_vars blks sub
    >>= fun () ->
    (* Summarizes model-ABI undef reads. *)
    let sub_tid = Term.tid sub in
    let lane_reads =
      Core.Map.fold !(ctx.Convutils.undef_warned) ~init:Var.Set.empty
        ~f:(fun ~key:_ ~data:warned_vars acc ->
          Core.Set.union acc !warned_vars)
      |> Core.Set.filter ~f:(fun v ->
             let abi = Abi.of_target ctx.Convutils.target in
             Abi.is_vector_param_reg abi v || Abi.is_return_reg abi v)
    in
    if not (Core.Set.is_empty lane_reads) then
      Hike_diag.warn
        "undef-read: sub %s: %d never-defined model-ABI lane read(s) [undef]"
        (Tid.name sub_tid) (Core.Set.length lane_reads);
    return ()

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

(* Builds bss with copy-relocated slots. *)
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
