(* Emitter expression lane: pure exp emission (no calls, no mem dispatch). *)

open Bap.Std
open Bap.Std.Bil.Types
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

(* True when the address expression bases on the target's TLS
   register: the access renders as the thread-local anchor read. *)
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

(* The TLS anchor: a thread_local global's address is not a constant —
   it depends on the calling thread — and llvm.threadlocal.address is
   its accessor.  A TLS-register-relative access reads the anchor's
   per-thread cell; the binary's offset drops with the base. *)
let tls_anchor_addr llvm_builder =
  let open KB in
  let* llvm_ctx = Context.get llvm_ctx_var in
  let* llvm_module = Context.get llvm_module_var in
  let g =
    Llvm.declare_global (Llvm.i64_type llvm_ctx) "hike_tls_anchor" llvm_module
  in
  Llvm.set_thread_local_mode Llvm.ThreadLocalMode.GeneralDynamic g;
  Llvm.set_initializer (Llvm.const_int (Llvm.i64_type llvm_ctx) 0) g;
  let tp = Llvm.pointer_type llvm_ctx in
  let fty = Llvm.function_type tp [| tp |] in
  let f = Llvm.declare_function "llvm.threadlocal.address" fty llvm_module in
  KB.return
  @@ Llvm.build_call fty f [| g |] "tls_anchor" llvm_builder

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
          let _ : Llvm.llvalue = Llvm.build_store llvm_var addr llvm_builder in
          KB.return llvm_var)
  | _ ->
      let* addr = create_addr_ptr llvm_builder addr in
      let _ : Llvm.llvalue = Llvm.build_store llvm_var addr llvm_builder in
      KB.return llvm_var

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

(* The immediate constant: the NATIVE bits, always — the data/access
   domain's one world.  A data word that names code renders the lifted
   address only in the section initializers (the function domain's
   thunk boundary); an immediate in address arithmetic must stay in
   the native world the section map resolves in. *)
let create_immidiate word =
  let open KB in
  let* llvm_ctx = Context.get llvm_ctx_var in
  return
  @@ Llvm.const_int_of_string
       (Llvm.integer_type llvm_ctx (Word.bitwidth word))
       (Word.string_of_value word)
       16

(* Warns on reads of never-defined vars. *)
let warn_undef_read ctx var blk_tid =
  let v = Var.base var in
  let abi = ctx.abi in
  let is_lane = Abi.is_vector_param_reg abi v || Abi.is_return_reg abi v in
  let sub_key = blk_tid in
  let warned_vars =
    match Core.Map.find !(ctx.undef_warned) sub_key with
    | Some r -> r
    | None ->
        let r = ref Var.Set.empty in
        ctx.undef_warned :=
          Core.Map.set !(ctx.undef_warned) ~key:sub_key ~data:r;
        r
  in
  if not (Core.Set.mem !warned_vars v) then begin
    warned_vars := Core.Set.add !warned_vars v;
    if not is_lane then
      Hike_diag.warn "undef-read: blk %s: var %s never defined"
        (Tid.name blk_tid) (Var.name v)
  end

(* The first memory node of an exp (the access lanes' one node — the
   fission invariant keeps a def's rhs single-node). *)
type mem_node = [ `Load of exp * Size.t | `Store of exp * exp * Size.t ]

let find_mem_node (exp : exp) : mem_node option =
  let vis =
    object
      inherit [ mem_node option ] Exp.visitor
      method! visit_load ~mem:_ ~addr _ size acc =
        Base.Option.first_some acc (Some (`Load (addr, size)))
      method! visit_store ~mem:_ ~addr ~exp:x _ size acc =
        Base.Option.first_some acc (Some (`Store (addr, x, size)))
    end
  in
  vis#visit_exp exp None

(* Name of the accumulator marker var an access lane binds. *)
let marker_name = "hike_acc"

let marker_of_size size =
  Var.create ~is_virtual:true ~fresh:false marker_name
    (Type.Imm (Size.in_bits size))

(* Maps only the mem node matching (addr, size) to a var, preserving
   the enclosing structure — the one rewrite every access-serving lane
   uses. *)
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
            match Var.typ v with Type.Imm w -> w | _ -> 8 * ctx.abi.Abi.word
          in
          match probe_local_family ctx blk_tid v ~want_w with
          | Some (val_at_w, bound_w) ->
              let want_ty = Llvm.integer_type llvm_ctx' want_w in
              if bound_w = want_w then return val_at_w
              else if bound_w > want_w then
                return @@ Llvm.build_trunc val_at_w want_ty "" llvm_builder
              else
                return @@ Llvm.build_zext val_at_w want_ty "" llvm_builder
          | None ->
              warn_undef_read ctx v blk_tid;
              frozen_undef ctx v)
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
  (* Fissioned AND ordinary memory ops: a named section component
     routes by name through its own global; everything else
     emits identically — the rewrite already materialized region
     storage into the address. *)
  | Store (Bil.Var mv, addr, data, _, _)
    when Hike_stack_model.is_region_mem mv
         || Hike_stack_model.is_window_mem mv ->
      region_window_access llvm_builder blk_tid mv exp
        ~raw:(fun () ->
          let* addr = create_exp llvm_builder blk_tid addr in
          let* data = create_exp llvm_builder blk_tid data in
          create_store llvm_builder (data, addr))
  | Store (Bil.Var mv, addr, data, _, s)
    when Hike_stack_model.is_sec_comp_mem mv ->
      sec_comp_access llvm_builder blk_tid ~store:true mv addr
        ~data:(Some data) (Size.in_bits s)
  | Store (_, addr, data, _, _) when is_tls_addr ctx addr ->
      let* ptr = tls_anchor_addr llvm_builder in
      let* data = create_exp llvm_builder blk_tid data in
      KB.return
      @@ Llvm.build_store data ptr llvm_builder
  | Store (_, addr, data, _, _) ->
      let* addr = create_exp llvm_builder blk_tid addr in
      let* data = create_exp llvm_builder blk_tid data in
      create_store llvm_builder (data, addr)
  | Load (Bil.Var mv, addr, _, size)
    when Hike_stack_model.is_region_mem mv
         || Hike_stack_model.is_window_mem mv ->
      region_window_access llvm_builder blk_tid mv exp
        ~raw:(fun () ->
          let* addr = create_exp llvm_builder blk_tid addr in
          create_load llvm_builder (addr, Size.in_bits size))
  | Load ((Bil.Var mv), addr, _, size)
    when Hike_stack_model.is_sec_comp_mem mv ->
      sec_comp_access llvm_builder blk_tid ~store:false mv addr
        ~data:None (Size.in_bits size)
  | Load (_, addr, _, size) when is_tls_addr ctx addr ->
      let* ptr = tls_anchor_addr llvm_builder in
      let* llvm_ctx = Context.get llvm_ctx_var in
      KB.return
      @@ Llvm.build_load (Llvm.integer_type llvm_ctx (Size.in_bits size)) ptr
           "" llvm_builder
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


(* The NAMED-COMPONENT lane (the section routing): the BIL memory var
   IS the component's identity — the spec setup binds each component
   mem var to its global and native base; the address expr evaluates
   to NATIVE bits (the rewrite kept the constant-chain arithmetic), so
   the GEP index is the exact native delta. *)
and sec_comp_access llvm_builder blk_tid ~(store : bool)
    (mv : var) (addr : exp) ~(data : exp option) (size : int) :
    Llvm.llvalue KB.t =
  let open KB in
  let* ctx, llvm_ctx = emit_env () in
  match Base.List.Assoc.find ~equal:Var.equal !(ctx.sec_comps) mv with
  | Some (base, own_lo) ->
    let* a = create_exp llvm_builder blk_tid addr in
    let idx =
      Llvm.build_sub a
        (Llvm.const_of_int64 (Llvm.i64_type llvm_ctx) own_lo false)
        "" llvm_builder
    in
    let p =
      Llvm.build_gep (Llvm.i8_type llvm_ctx) base [| idx |] ""
        llvm_builder
    in
    if store then
      (match data with
       | Some d ->
         let* v = create_exp llvm_builder blk_tid d in
         let _ : Llvm.llvalue = Llvm.build_store v p llvm_builder in
         KB.return v
       | None -> assert false)
    else
      KB.return
      @@ Llvm.build_load (Llvm.integer_type llvm_ctx size) p ""
           llvm_builder
  | None ->
    (* Unknown component: the generic memory lane — the address
       stays native bits and materializes unremapped. *)
    if store then
      (match data with
       | Some d ->
         let* a = create_exp llvm_builder blk_tid addr in
         let* v = create_exp llvm_builder blk_tid d in
         create_store llvm_builder (v, a)
       | None -> assert false)
    else
      let* a = create_exp llvm_builder blk_tid addr in
      create_load llvm_builder (a, size)

and create_rip_relative_addr llvm_builder blk_tid exp =
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
  | Store (Bil.Var mv, addr, data, _, s)
    when Hike_stack_model.is_sec_comp_mem mv ->
      sec_comp_access llvm_builder blk_tid ~store:true mv addr
        ~data:(Some data) (Size.in_bits s)
  | Load (Bil.Var mv, addr, _, s)
    when Hike_stack_model.is_sec_comp_mem mv ->
      sec_comp_access llvm_builder blk_tid ~store:false mv addr
        ~data:None (Size.in_bits s)
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
               let _ : Llvm.llvalue =
                 Llvm.build_store data base llvm_builder in
               KB.return data)
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
           (* Non-constant addresses: the ordinary [create_load] path. *)
           create_load llvm_builder (addr, Size.in_bits size))
  | Cast (cast, i, (Load _ as load)) ->
      (* RIP-relative widening loads. *)
      let* v = create_rip_relative_addr llvm_builder blk_tid load in
      create_cast llvm_builder (cast, i, v)
  | _ -> create_exp llvm_builder blk_tid exp

(* Shared skeleton: bind the arm's value to the marker, then re-emit
   with the arm's rewrite. Insertion order is the arm's order. *)
and emit_with_marker llvm_builder blk_tid ctx marker ~emit ~rewrite =
  let open KB in
  let* v = emit () in
  insert_local ctx blk_tid marker v;
  create_exp llvm_builder blk_tid (rewrite marker)

(* The region lane: the BIL's [stack_rN_mem] routes to the region's
   own alloca.  The address expression evaluates to the anchor-based
   runtime integer (the model arithmetic resolves against the SP
   Slot's anchor), so the GEP index is the entry-relative offset of
   the access minus the region's entry-relative base — the same
   relative byte, exact for dynamic indices and displacement. *)
(* The incoming-window lane: the callee's above-entry accesses read the
   CALLER's window through the hike_window parameter — the same
   normalization (the access's anchor-relative offset), one base
   different: the parameter integer, not an alloca. *)
and window_mem_access llvm_builder blk_tid fr mv exp =
  let open KB in
  match Hike_stack_model.is_window_mem mv with
  | false -> create_exp llvm_builder blk_tid exp
  | true -> (
      let* ctx, llvm_ctx = emit_env () in
      let* w_int =
        let w = Hike_stack_model.hike_window_var ~word:ctx.abi.Abi.word in
        match get_local ctx blk_tid w with
        | Some v -> KB.return v
        | None -> KB.return @@ Llvm.const_int (Llvm.i64_type llvm_ctx) 0
      in
      let off a =
        let stack0 =
          match fr.stack0 with
          | Some v -> v
          | None -> fr.anchor_i64
        in
        Llvm.build_sub a stack0 "" llvm_builder
      in
      match find_mem_node exp with
      | Some (`Load (addr, size)) ->
          let marker = marker_of_size size in
          let* a = create_exp llvm_builder blk_tid addr in
          let p =
            Llvm.build_inttoptr
              (Llvm.build_add w_int (off a) "" llvm_builder)
              (Llvm.pointer_type llvm_ctx) "" llvm_builder
          in
          let emit () =
            KB.return
            @@ Llvm.build_load
                 (Llvm.integer_type llvm_ctx (Size.in_bits size))
                 p "" llvm_builder
          in
          let rewrite marker = rewrite_mem_node exp addr size marker in
          emit_with_marker llvm_builder blk_tid ctx marker ~emit ~rewrite
      | Some (`Store (addr, data, size)) ->
          let marker = marker_of_size size in
          let* a = create_exp llvm_builder blk_tid addr in
          let p =
            Llvm.build_inttoptr
              (Llvm.build_add w_int (off a) "" llvm_builder)
              (Llvm.pointer_type llvm_ctx) "" llvm_builder
          in
          let emit () =
            let* d = create_exp llvm_builder blk_tid data in
            let _ : Llvm.llvalue = Llvm.build_store d p llvm_builder in
            KB.return d
          in
          let rewrite marker = rewrite_mem_node exp addr size marker in
          emit_with_marker llvm_builder blk_tid ctx marker ~emit ~rewrite
      | None -> create_exp llvm_builder blk_tid exp)

and region_mem_access llvm_builder blk_tid fr mv exp =
  let open KB in
  let stack0 =
    match fr.stack0 with Some v -> v | None -> fr.anchor_i64
  in
  let region_index llvm_builder rel_rlo a =
    let* llvm_ctx = Context.get llvm_ctx_var in
    let rel = Llvm.build_sub a stack0 "reg_rel" llvm_builder in
    KB.return
    @@ Llvm.build_sub rel
         (Llvm.const_of_int64 (Llvm.i64_type llvm_ctx) rel_rlo false)
         "" llvm_builder
  in
  match Base.List.Assoc.find ~equal:Var.equal fr.regions mv with
  | None -> create_exp llvm_builder blk_tid exp
  | Some (base, rel_rlo) -> (
      match find_mem_node exp with
      | Some (`Load (addr, size)) ->
          let marker = marker_of_size size in
          let* ctx = Context.get emit_ctx_var in
          let* llvm_ctx = Context.get llvm_ctx_var in
          let* a = create_exp llvm_builder blk_tid addr in
          let* idx = region_index llvm_builder rel_rlo a in
          let p =
            Llvm.build_gep (Llvm.i8_type llvm_ctx) base [| idx |] ""
              llvm_builder
          in
          let emit () =
            KB.return
            @@ Llvm.build_load
                 (Llvm.integer_type llvm_ctx (Size.in_bits size))
                 p "" llvm_builder
          in
          let rewrite marker = rewrite_mem_node exp addr size marker in
          emit_with_marker llvm_builder blk_tid ctx marker ~emit ~rewrite
      | Some (`Store (addr, data, size)) ->
          let marker = marker_of_size size in
          let* ctx = Context.get emit_ctx_var in
          let* llvm_ctx = Context.get llvm_ctx_var in
          let* a = create_exp llvm_builder blk_tid addr in
          let* idx = region_index llvm_builder rel_rlo a in
          let p =
            Llvm.build_gep (Llvm.i8_type llvm_ctx) base [| idx |] ""
              llvm_builder
          in
          let emit () =
            let open KB in
            let* d = create_exp llvm_builder blk_tid data in
            let _ : Llvm.llvalue = Llvm.build_store d p llvm_builder in
            return d
          in
          let rewrite marker = rewrite_mem_node exp addr size marker in
          emit_with_marker llvm_builder blk_tid ctx marker ~emit ~rewrite
      | None -> create_exp llvm_builder blk_tid exp)

(* The region/window twin of the generic exp lane (defense in depth):
   a fissioned mem var reaching this lane still routes to its storage;
   with no frame bound (outside a body) or no such region, the raw
   lane serves the access. *)
and region_window_access llvm_builder blk_tid mv exp ~raw =
  match !Bil2llvm_env.cur_frame with
  | Some fr when Hike_stack_model.is_region_mem mv ->
      region_mem_access llvm_builder blk_tid fr mv exp
  | Some fr when Hike_stack_model.is_window_mem mv ->
      window_mem_access llvm_builder blk_tid fr mv exp
  | _ -> raw ()

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
