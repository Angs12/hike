(* Emitter expression lane: pure exp emission (no calls, no mem dispatch). *)

open Bap.Std
open Bap.Std.Bil.Types
open Convutils
module Abi = Hike_abi
module KB = Bap_knowledge.Knowledge
open Bil2llvm_env
open Bil2llvm_section


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

let create_load llvm_builder (addr, size) =
  let open KB in
  match Llvm.int64_of_const addr with
  | Some v ->
      const_addr_load llvm_builder (Word.of_int64 ~width:64 v) size
        ~fallback:(fun () ->
          let* llvm_ctx = Context.get llvm_ctx_var in
          let* ptr = create_addr_ptr llvm_builder addr in
          return
          @@ Llvm.build_load (Llvm.integer_type llvm_ctx size) ptr ""
               llvm_builder)
  | _ ->
      (* Non-constant addresses materialize through [create_addr_ptr]
         (frame GEP for frame addresses, inttoptr for foreign ones). *)
      let* addr = create_addr_ptr llvm_builder addr in
      let* llvm_ctx = Context.get llvm_ctx_var in
      return
      @@ Llvm.build_load (Llvm.integer_type llvm_ctx size) addr ""
           llvm_builder

let create_store llvm_builder (llvm_var, addr) =
  let open KB in
  match Llvm.int64_of_const addr with
  | Some v ->
      const_addr_store llvm_builder (Word.of_int64 ~width:64 v)
        ~data:(fun () -> KB.return llvm_var)
        ~fallback:(fun () ->
          let* addr = create_addr_ptr llvm_builder addr in
          return @@ Llvm.build_store llvm_var addr llvm_builder)
  | _ ->
      let* addr = create_addr_ptr llvm_builder addr in
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
  let abi = ctx.Convutils.abi in
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
           let addr_w = Word.of_int64 ~width:64 i64 in
           const_addr_store llvm_builder addr_w
             ~data:(fun () -> create_exp llvm_builder blk_tid data)
             ~fallback:(fun () ->
               let* base = resolve_addr llvm_builder addr_w in
               let* data = create_exp llvm_builder blk_tid data in
               return @@ Llvm.build_store data base llvm_builder)
       | None ->
           (* Stores through remapped constants. *)
           let* data = create_exp llvm_builder blk_tid data in
           create_store llvm_builder (data, addr))
  | Load (_, addr, _, size) ->
      let* addr = create_exp llvm_builder blk_tid addr in
      (match Llvm.int64_of_const addr with
       | Some i64 ->
           let addr_w = Word.of_int64 ~width:64 i64 in
           (* Reads .text loads at compile time. *)
           const_addr_load llvm_builder addr_w (Size.in_bits size)
             ~fallback:(fun () ->
               let* llvm_ctx = Context.get llvm_ctx_var in
               section_load llvm_builder llvm_ctx addr_w i64
                 (Size.in_bits size))
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
