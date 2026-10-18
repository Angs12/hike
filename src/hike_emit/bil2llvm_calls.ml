(* Emitter call lane: sub declarations, call arms, dispatch. *)

open Bap.Std
open Bap.Std.Bil.Types
module Abi = Hike_abi
open Bil2llvm_env
open Bil2llvm_exp
open Bil2llvm_fp
open Bil2llvm_access

(* The main-role sub is the module's C entry, whatever the decode named it. *)
let is_main_role ctx (sub_tid : tid) : bool =
  match Core.Map.find ctx.sub_of sub_tid with
  | Some s -> Term.has_attr s Hike_stack_model.main_role
  | None -> false

let create_call_args ctx scope blk_tid llvm_builder call_tid =
  let args = get_args ctx call_tid in
  let extern = is_extern ctx call_tid in
  let slot_args =
    Base.List.filter args ~f:(fun a ->
        Hike_stack_model.is_arg_slot ctx.synth (Arg.lhs a))
  in
  (* The caller-window base is the caller's SP at the call: its position
     in the caller's residue (the shadow that covers the above-entry
     window). *)
  let window_ptr () =
    match !(scope.cur_frame) with
    | Some _ -> (
        let sp_ver =
          match lane_version scope blk_tid ctx.sp with
          | Some v -> v
          | None -> ctx.sp
        in
        match get_ptr_offset scope sp_ver with
        | Some off ->
          Some
            (Bil2llvm_synth.materialize ctx scope llvm_builder blk_tid
               Hike_stack_model.Ptr_residue off)
        | None -> Some (as_ptr llvm_builder (lane_value ctx scope blk_tid ctx.sp)))
    | None -> None
  in
  (* Slot parameter i binds the block's [call_arg i] def; both names
     derive from the index, so the binding is order-independent.  A slot
     the site never stored still has its window cell: the address is the
     window at the slot's own offset (the stored-address defs are the
     refinement of exactly that). *)
  let slot_ptr i =
    match
      get_local scope blk_tid
        (Hike_stack_model.call_arg ~addr_bits:ctx.addr_bits i)
    with
    | Some v -> as_ptr llvm_builder v
    | None -> (
        match window_ptr () with
        | None -> Llvm.undef (Llvm.pointer_type ctx.llvm_ctx)
        | Some w ->
          let off =
            Llvm.const_of_int64 (Llvm.i64_type ctx.llvm_ctx)
              (Hike_stack_model.slot_offset ~word:ctx.abi.Abi.word i)
              false
          in
          Llvm.build_gep (Llvm.i8_type ctx.llvm_ctx) w [| off |] ""
            llvm_builder)
  in
  Base.List.map args ~f:(fun arg ->
      (* Every lane read resolves through the block's version stamp —
         including the fp-lowered extern lanes. *)
      let exp = lane_exp scope blk_tid (Arg.rhs arg) in
      if Var.same (Arg.lhs arg)
          (Hike_stack_model.hike_window_var ~word:ctx.abi.Abi.word)
      then
        (match window_ptr () with
         | Some w -> w
         | None -> Llvm.undef (var_lltype ctx (Arg.lhs arg)))
      else if Hike_stack_model.is_arg_slot ctx.synth (Arg.lhs arg) then
        let i =
          Base.Option.value ~default:0
            (Base.List.findi slot_args
               ~f:(fun _ a -> Var.equal (Arg.lhs a) (Arg.lhs arg))
               |> Base.Option.map ~f:fst)
        in
        slot_ptr i
      else if extern && is_fp_param ctx (Arg.lhs arg) then
        (* Lowers YMM args to doubles for externs. *)
        let v = as_int ctx llvm_builder (create_exp ctx scope llvm_builder blk_tid exp) in
        let v =
          if Llvm.integer_bitwidth (Llvm.type_of v) = 256 then
            Llvm.build_trunc v (ctx.i64_ty) "" llvm_builder
          else v
        in
        Llvm.build_bitcast v (Llvm.double_type ctx.llvm_ctx) ""
          llvm_builder
      else if lane_is_ptr ctx arg then
        (* A stack address is passed as a pointer into the caller's
           own storage.  The kind is a callee-side may — a site whose
           value is not itself a stack address passes the register's
           bits, coerced to the lane's pointer type. *)
        as_ptr llvm_builder (create_exp ctx scope llvm_builder blk_tid exp)
      else as_int ctx llvm_builder (create_exp ctx scope llvm_builder blk_tid exp))

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

let create_ret_type ctx sub_tid = ret_type_of_rets ctx (get_rets ctx sub_tid)

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
  Base.List.iteri (get_args ctx sub_tid) ~f:(fun i arg ->
      let value = lane_value_of ctx arg (Llvm.param fn i) in
      insert_local scope blk_tid (Arg.lhs arg) value;
      (* A parameter dominates every reader: bind it sub-wide too. *)
      bind_ssaval scope (Arg.lhs arg) value)

let create_fun_declaration ?name ctx sub_tid =
  let name = Base.Option.value name ~default:(Tid.name sub_tid) in
  let ret_typ = create_ret_type ctx sub_tid in
  let args_typ = create_arg_types ctx sub_tid in
  (* Extern declares are variadic. *)
  let fn_typ =
    if is_extern ctx sub_tid then
      Llvm.var_arg_function_type ret_typ (Array.of_list args_typ)
    else Llvm.function_type ret_typ (Array.of_list args_typ)
  in
  Hike_diag.debug ~tag:"hike-dbg-tail" (fun () ->
      Printf.sprintf "decl %s extern=%b blocks=%s"
        (Tid.name sub_tid) (is_extern ctx sub_tid)
        (match Core.Map.find ctx.sub_of sub_tid with
         | Some s ->
           Base.List.length (Term.enum blk_t s |> Seq.to_list) |> string_of_int
         | None -> "absent"));
  let fn =
    Llvm.declare_function (sanitize_name name) fn_typ
      ctx.llvm_module
  in
  register_fn ctx sub_tid fn fn_typ

let create_fun ctx sub_tid ~rets ~args ~variadic =
  let ret_typ = ret_type_of_rets ctx rets in
  let args_typ = arg_types_of ctx sub_tid args in
  (* A lifted variadic body declares a real variadic definition; its
     named lanes are the ABI's. *)
  let fn_typ =
    if variadic then
      Llvm.var_arg_function_type ret_typ (Array.of_list args_typ)
    else Llvm.function_type ret_typ (Array.of_list args_typ)
  in
  (* The main-role sub is the C entry the native crt1 calls: it is the
     module's `main` whatever the decode named it. *)
  let fn_name = if is_main_role ctx sub_tid then "main" else Tid.name sub_tid in
  let fn =
    Llvm.define_function (sanitize_name fn_name) fn_typ ctx.llvm_module
  in
  (* The module's entry is the lifted main and the consumer enters
     nothing else, so every other definition is internal: the system
     crt's own _init/_fini do not collide with kept-by-refusal stubs,
     and the optimizer may cross the boundaries. *)
  if not (is_main_role ctx sub_tid) then Llvm.set_linkage Llvm.Linkage.Internal fn;
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
  (* A vector return lane binds as the register's integer bits. *)
  let bind_call_ret ctx scope blk_tid ret v =
    let v =
      match lane_vector ctx ret with
      | Some _ ->
        Bil2llvm_value.Int
          (Llvm.build_bitcast v (typ_lltype ctx (Var.typ (Arg.lhs ret))) ""
             llvm_builder)
      | None -> lane_value_of ctx ret v
    in
    bind_call_ret ctx scope blk_tid ret v
  in
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
      (match Var.typ (Arg.lhs ret) with
       | Type.Imm w when w < ctx.addr_bits && not (lane_is_ptr ctx ret) ->
         Llvm.add_call_site_attr ret_var
           (Llvm.create_enum_attr ctx.llvm_ctx "zeroext" 0L)
           Llvm.AttrIndex.Return
       | _ -> ());
      bind_call_ret ctx scope blk_tid ret ret_var
  | rets ->
      let ret_struct =
        Llvm.build_call fn_typ fn (Array.of_list args) "" llvm_builder
      in
      Base.List.iteri rets ~f:(fun i ret ->
          let ret_val = Llvm.build_extractvalue ret_struct i "" llvm_builder in
          bind_call_ret ctx scope blk_tid ret ret_val)

(* The outgoing stack args in slot order: [call_arg k] defs
  enumerated by index, stopping at the first absent slot.  An extern
  consumes stack slots after the register args, so the window stores
  are its trailing varargs. *)
let extern_stack_args ctx scope llvm_builder blk_tid (blk : blk term) =
  let word = ctx.abi.Abi.word in
  (* The block's defined lhs vars, one pass; the slot walk conses and
     one rev restores slot order. *)
  let defined_vars =
    Term.enum def_t blk
    |> Seq.fold ~init:Var.Set.empty ~f:(fun acc d ->
        Core.Set.add acc (Def.lhs d))
  in
  let rec slots i acc =
    let v = Hike_stack_model.call_arg ~addr_bits:ctx.addr_bits i in
    if Core.Set.mem defined_vars v then
      match get_local scope blk_tid v with
      | Some value ->
          (* The call-arg def is the caller's slot ADDRESS; the vararg
             is the value stored there. *)
          let loaded =
            Bil2llvm_memory.load_ptr llvm_builder
              (Llvm.integer_type ctx.llvm_ctx
                 (Hike_stack_model.word_bits word))
              (as_ptr llvm_builder value)
          in
          slots (i + 1) (loaded :: acc)
      | None -> acc
    else List.rev acc
  in
  slots 0 []

let create_func_call ?(emit_unreachable = true) ctx scope llvm_builder blk_tid blk
    fallthrough target =
  let args = create_call_args ctx scope blk_tid llvm_builder target in
  let args =
    if is_extern ctx target then
      args @ extern_stack_args ctx scope llvm_builder blk_tid blk
    else args
  in
  let rets = get_rets ctx target in
  let fn, fn_typ = get_func ctx target in
  bind_call_rets ctx scope blk_tid llvm_builder fn_typ fn args rets;
  (match fallthrough with
  | Some fallthrough -> finish_call scope llvm_builder (Some fallthrough)
  | None -> if emit_unreachable then finish_call scope llvm_builder None)

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
  let func_ptr =
    as_ptr llvm_builder (create_exp ctx scope llvm_builder blk_tid target)
  in
  let fn, fn_typ = get_func ctx icall_tid in
  let rets = get_rets ctx icall_tid in
  let args = create_call_args ctx scope blk_tid llvm_builder icall_tid in
  bind_call_rets ctx scope blk_tid llvm_builder fn_typ func_ptr args rets;
  finish_call scope llvm_builder (Some fallthrough)

(* The Thunk — the memory-convention twin of a promoted sub. *)

let thunk_name_of (sub_tid : tid) : string =
  sanitize_name (Tid.name sub_tid) ^ "_hike_thunk"

let thunk_tid_of (sub_tid : tid) : tid =
  Tid.for_name (Tid.name sub_tid ^ ":thunk")

(* Whether [sub_tid] gets a twin.  Every non-entry sub carries one when
   the synthetic indirect convention can serve it: an address handed to
   an external (a data word, a call argument) is callable through the
   machine convention.  An external has no body to forward to; a
   signature with lanes the convention does not carry (a promoted
   pointer parameter) stays untwinned. *)
let thunk_eligible ctx (sub_tid : tid) : bool =
  let conv_lane v =
    Hike_stack_model.is_arg_slot ctx.synth (Var.base v)
    || Var.same v (Hike_stack_model.hike_window_var ~word:ctx.abi.Abi.word)
    || Base.List.exists
         (window_conv_args ~word:ctx.abi.Abi.word ctx.abi)
         ~f:(fun a -> Var.same (Arg.lhs a) v)
  in
  (not (is_extern ctx sub_tid))
  && (not (Core.Map.mem !(ctx.ll_funcs) (thunk_tid_of sub_tid)))
  && Base.List.for_all (get_args ctx sub_tid) ~f:(fun a ->
         conv_lane (Arg.lhs a))

(* The twin unpacks the window into the promoted body's slot
   parameters and forwards the register lanes.  Internal linkage: the
   consumer's optimizer inlines it where the call site resolves. *)
let create_thunk ctx (sub_tid : tid) =
  if not (thunk_eligible ctx sub_tid) then ()
  else
  let llvm_ctx = ctx.llvm_ctx in
  let llvm_module = ctx.llvm_module in
  let arity = count_slot_args ctx.synth (get_args ctx sub_tid) in
  let args = get_args ctx sub_tid in
  let rets = get_rets ctx sub_tid in
  (* The twin is the machine-convention face: its return is the
     synthetic convention's (the ABI's integer return registers),
     never the callee's own carrier list.  Its body extracts the
     lanes the convention can carry and drops the rest (the vector
     return has no synthetic carrier). *)
  let conv_rets =
    Base.List.map ctx.abi.Abi.return_regs ~f:(fun reg ->
        Arg.create ~intent:Out reg (Var reg))
  in
  let word = ctx.abi.Abi.word in
  let window_var = Hike_stack_model.hike_window_var ~word in
  (* The twin carries the synthetic indirect convention — exactly
     what a pointer call passes. *)
  let conv = ctx.abi in
  let twin_args = window_conv_args ~word conv in
  let ret_typ = ret_type_of_rets ctx conv_rets in
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
        (* The slot lane is the caller's cell address: the twin
           forwards the window GEP'd at the slot. *)
        Llvm.build_gep (Llvm.i8_type llvm_ctx) window [| off |] ""
          builder)
  in
  (* Forwards [sub]'s own parameter order: each register lane by name
     from the twin's convention, each slot as the window GEP'd at its
     cell, and the window itself. *)
  let param_named (v : var) : Llvm.llvalue =
    let n = Var.name v in
    match
      Base.List.findi twin_args ~f:(fun _ a -> Var.name (Arg.lhs a) = n)
    with
    | Some (i, _) -> Llvm.param fn i
    | None ->
        failwith
          ("hike-emit: thunk: the lane " ^ n
          ^ " is not in the twin's convention (sub "
          ^ Tid.name sub_tid ^ ")")
  in
  (* A forwarded value takes its lane's type: the twin's convention
     is integer-honest, and a callee lane the kind pass typed ptr
     receives the register's bits as a pointer. *)
  let forward (a : Arg.t) (v : Bil2llvm_value.t) : Llvm.llvalue =
    Bil2llvm_value.ll
      (Bil2llvm_value.coerce ~addr_bits:ctx.addr_bits builder
         ~ptr:(lane_is_ptr ctx a) v)
  in
  let call_args =
    Base.List.map args ~f:(fun a ->
        let v = Arg.lhs a in
        if Hike_stack_model.is_arg_slot ctx.synth v then
          let i =
            match Hike_synth.index_of ctx.synth v with
            | Some i -> i
            | None ->
                failwith
                  ("hike-emit: thunk: the slot parameter "
                 ^ Var.name v
                 ^ " carries no slot index")
          in
          (match Base.List.nth slot_vals i with
           | Some s -> s
           | None ->
               failwith
                 ("hike-emit: thunk: the slot "
                ^ Int.to_string i
                ^ " is outside the twin's slots"))
        else if Var.same v window_var then window
        else forward a (Bil2llvm_value.Int (param_named v)))
  in
  let callee_fn, callee_typ = get_func ctx sub_tid in
  let r =
    Llvm.build_call callee_typ callee_fn
      (Array.of_list call_args) "" builder
  in
  let n_callee = Base.List.length rets in
  let lane_value (i : int) (a : Arg.t) : Llvm.llvalue =
    let v =
      if i >= n_callee then lane_value_of ctx a (Llvm.undef (lane_type ctx a))
      else
        lane_value_of ctx (Base.List.nth_exn rets i)
          (match rets with
           | [ _ ] -> r
           | _ -> Llvm.build_extractvalue r i "" builder)
    in
    (* The synthetic lane is integer-honest; a callee lane the kind
       pass typed ptr is re-coerced like a forwarded argument. *)
    forward a v
  in
  (match conv_rets with
   | [] -> ignore (Llvm.build_ret_void builder)
   | [ a ] -> ignore (Llvm.build_ret (lane_value 0 a) builder)
   | _ ->
     let agg = ref (Llvm.undef ret_typ) in
     Base.List.iteri conv_rets ~f:(fun i a ->
         agg := Llvm.build_insertvalue !agg (lane_value i a) i "" builder);
     ignore (Llvm.build_ret !agg builder));
  ctx.thunks :=
    (sanitize_name (Tid.name sub_tid), fn) :: !(ctx.thunks)


let create_return ctx scope blk_tid llvm_builder cur_sub =
  let rets =
    Base.List.map (get_rets ctx (Term.tid cur_sub)) ~f:(fun ret ->
        let lane = Arg.lhs ret in
        (* A ret lane read at its own call site carries the mint. *)
        let v =
          match
            Base.Option.bind (mint_version scope blk_tid lane)
              ~f:(get_ssaval scope)
          with
          | Some x -> x
          | None -> lane_value ctx scope blk_tid lane
        in
        (* The ret lane's type drives: pointer lanes return the pointer,
           the vector carrier the integer bits as its vector, integer
           lanes the integer form. *)
        if lane_is_ptr ctx ret then as_ptr llvm_builder v
        else
          match lane_vector ctx ret with
          | Some ty ->
            Llvm.build_bitcast (as_int ctx llvm_builder v) ty "" llvm_builder
          | None -> as_int ctx llvm_builder v)
  in
  match rets with
  | [] -> Llvm.build_ret_void llvm_builder |> ignore
  | [ ret ] -> Llvm.build_ret ret llvm_builder |> ignore
  | rets -> Llvm.build_aggregate_ret (Array.of_list rets) llvm_builder |> ignore

(* The external-symbol slot a target exp reads, as the symbol's name:
   the slot rule resolves the target's load through the sub's own defs
   (the load may sit in any block of the sub — the split pieces
   separate a load from the transfer it feeds), and the slot addresses
   the module's externals name. *)
let external_slot_target ctx ?(sub : sub term option) (target : exp) :
    string option =
  (* A resolved access is component-relative; the component's module
     origin recovers the absolute slot the loader's externals name. *)
  let origin v = Bil2llvm_synth.storage_origin ctx v in
  match Hike_transfer.slot_of_target ~synth:ctx.synth ~origin ?sub target with
  | Some a -> Core.Map.find ctx.address.externals a
  | None -> None

(* The boundary-class indirect transfer: the target leaves the program
   through an external-symbol slot, so the module calls the symbol the
   slot binds — the machine's integer lanes pass as the arguments, the
   result binds the sub's return lanes, and the sub returns (the
   transfer is a tail transfer). *)
let create_external_boundary ctx scope llvm_builder blk_tid sub name =
  let word = ctx.abi.Abi.word in
  let window_var = Hike_stack_model.hike_window_var ~word in
  let conv_args = synthetic_args ctx in
  (* The register lanes only: the window stays the caller's private
     shadow, and the external sees the machine's own ABI registers. *)
  let reg_args = Base.List.take conv_args (Base.List.length conv_args - 1) in
  let arg_typs =
    Base.List.map reg_args ~f:(fun a ->
        if Var.same (Arg.lhs a) window_var then ctx.ptr_ty
        else lane_type ctx a)
  in
  let fn_typ =
    Llvm.var_arg_function_type ctx.i64_ty (Array.of_list arg_typs)
  in
  (* The slot's symbol may already carry the extern_weak data binding the
     initializer gives it; the call goes through it, so the module holds
     ONE symbol and the slot's weak-undefined resolution (null) stays
     the link-time answer, as the loader would leave it. *)
  let callee =
    match Llvm.lookup_function (sanitize_name name) ctx.llvm_module with
    | Some fn -> fn
    | None -> (
      match Llvm.lookup_global (sanitize_name name) ctx.llvm_module with
      | Some g -> Llvm.const_bitcast g (Llvm.pointer_type ctx.llvm_ctx)
      | None ->
        let f = Llvm.declare_function (sanitize_name name) fn_typ ctx.llvm_module in
        Llvm.set_linkage Llvm.Linkage.External_weak f;
        f)
  in
  let args =
    Base.List.map reg_args ~f:(fun a ->
        let exp = lane_exp scope blk_tid (Arg.rhs a) in
        as_int ctx llvm_builder (create_exp ctx scope llvm_builder blk_tid exp))
  in
  let r = Llvm.build_call fn_typ callee (Array.of_list args) "" llvm_builder in
  match get_rets ctx (Term.tid sub) with
  | [ ret ] -> bind_call_ret ctx scope blk_tid ret (Bil2llvm_value.Int r)
  | _ -> ();
  create_return ctx scope blk_tid llvm_builder sub

let create_indirect_tail ctx scope llvm_builder blk_tid blk sub (j : jmp term) =
  let call = call_exn j in
  match Call.target call with
  | Indirect (Bil.Unknown _) ->
      (* The target cannot be denoted: the identity at the boundary is
         the return. *)
      Hike_diag.warn
        "emit: indirect tail call at block %s has an unknown target — rendered as a return"
        (Tid.name blk_tid);
      create_return ctx scope blk_tid llvm_builder sub
  | Indirect target -> (
      match external_slot_target ctx ~sub target with
      | Some name -> create_external_boundary ctx scope llvm_builder blk_tid sub name
      | None ->
        Hike_diag.debug ~tag:"hike-dbg-tail" (fun () ->
            Printf.sprintf "sub %s blk %s target %s defs=[%s]"
              (Tid.name (Term.tid sub)) (Tid.name blk_tid) (Exp.to_string target)
              (Term.enum blk_t sub
               |> Seq.concat_map ~f:(Term.enum def_t)
               |> Seq.filter_map ~f:(fun d ->
                   if
                     match target with
                     | Bil.Var v -> Var.equal (Def.lhs d) v
                     | _ -> false
                   then Some (Exp.to_string (Def.rhs d))
                   else None)
               |> Seq.to_list
               |> String.concat "; "));
        (* A dispatch with no enumerated destinations is UB the moment it
           is taken; the module never carries it behind a warning. *)
        failwith
          (Printf.sprintf
             "hike: indirect tail call at block %s (sub %s) has no enumerated destinations: target %s"
             (Tid.name blk_tid) (Tid.name (Term.tid sub))
             (Exp.to_string target)))
  | Direct _ -> failwith "create_indirect_tail: expected an indirect target"

(* Marker calls retain only their continuation; fences emit their exact ordering. *)
let create_atomic_intrinsic_call ctx scope llvm_builder ~sub_tid name call =
  (match Abi.strip_at name with
   | "intrinsic:x86:lock" | "intrinsic:x86:unlock" ->
     failwith "hike-emit: legacy atomic markers: install the paired BAP producer"
   | "intrinsic:mfence" -> Bil2llvm_atomic.fence Llvm.AtomicOrdering.SequentiallyConsistent llvm_builder
   | "intrinsic:lfence" -> Bil2llvm_atomic.fence Llvm.AtomicOrdering.Acquire llvm_builder
   | "intrinsic:sfence" -> Bil2llvm_atomic.fence Llvm.AtomicOrdering.Release llvm_builder
   | other ->
     failwith
       (Printf.sprintf
          "hike-emit: unmapped atomic intrinsic call: %s (in sub %s)"
          other (Tid.name sub_tid)));
  let fallthrough = Option.map label_tid (Call.return call) in
  finish_call scope llvm_builder fallthrough

let create_call ctx scope llvm_builder blk_tid blk sub call =
  let target = Call.target call |> label_tid in
  let name = Tid.name target |> fp_intrinsic_name in
  if Hike_abi.is_interrupt_name (Tid.name target) then
    create_interrupt ctx llvm_builder
  else if Hike_abi.is_atomic_intrinsic_name (Tid.name target) then
    create_atomic_intrinsic_call ctx scope llvm_builder
      ~sub_tid:(Term.tid sub) (Tid.name target) call
  else
    match native_fp_op (Tid.name target) with
    | Some op ->
        create_native_fp_call ctx scope llvm_builder blk_tid blk call op
    | None ->
        if Hike_abi.is_intrinsic_name name then
          failwith
            (Printf.sprintf
               "hike-emit: unmapped intrinsic call: %s (in sub %s) - no \
                lowering exists; refusing to emit an external"
               name (Tid.name (Term.tid sub)))
        else (
        match Call.return call with
        | Some l ->
            let fallthrough = Some (label_tid l) in
            create_func_call ctx scope llvm_builder blk_tid blk fallthrough target
        | None ->
            create_func_call ~emit_unreachable:false ctx scope llvm_builder blk_tid
              blk None target;
            create_return ctx scope blk_tid llvm_builder sub)
