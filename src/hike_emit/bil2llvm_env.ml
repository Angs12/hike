(* Emitter environment: the emission run's value ctx, the per-sub
   scope, LLtype helpers, the WVar/blk-llvals machinery, signature and
   label helpers, name minting. *)

open Bap.Std
open Bap.Std.Bil.Types
open Bap_core_theory
module Abi = Hike_abi

module EHashtbl = Core.Hashtbl

type wvar = Var.t

let wvar_of (v : Var.t) : wvar = v

module WVar = struct
  type t = wvar
  let compare = Var.compare
end

module WVarMap = Map.Make (WVar)

type llvalue_map = Llvm.llvalue WVarMap.t

(* A var's bound value, typed. *)
type value_map = Bil2llvm_value.t WVarMap.t

type blk_llvals = { locals : value_map ref }

(* One owner of a byte range of a section: a component or a gap
   run.  [own_id] is the component id ([None] for a gap run). *)
type sec_owner = {
  own_id : int option;
  own_lo : int64;               (* native byte range [own_lo, own_hi] *)
  own_hi : int64;
  base : Llvm.llvalue;
  (* The component's emission decision (components only). *)
  typed_w : int;                (* bytes per element: 8/4/2/1 *)
}

type section = {
  base : Llvm.llvalue;
  min_addr : word;
  max_addr : word;
  (* The byte image; initializers render inside [emit_program],
     where the address map lives. *)
  bytes : Bytes.t option;
  (* The byte-exact tiling: every address resolves through exactly
     one owner.  Empty = the identity (the one array in [base]). *)
  owners : sec_owner list;
}
(* The shared section vocabulary (the producer/emitter contract point);
   the section table carries the data sections only. *)
type section_type = Hike_stack_model.sec

(* The section spec's one definition is [Hike_spec] (the lower library);
   this re-export keeps the type and its labels reachable here. *)
include Hike_spec

type sub_frame = {
  (* The model entry line: the seeded SP's absolute address.  A constant,
      so every address is derived from the model offsets, and every
      storage GEP's index is [address − entry_line − rel]. *)
  entry_line : Llvm.llvalue;
  (* The entry line as a pointer into the residue (None = no storage). *)
  entry_ptr : Llvm.llvalue option;
}

(* The one emission address index: the exact section tiling and each
   section's owners, keyed by base for a closest-key lookup, plus the
   loader's relocation facts.  Built once per run; every address
   resolution and initializer word reads it. *)
type address_index = {
  sections : section Core.Int64.Map.t;
  owners : sec_owner Core.Int64.Map.t Core.Int64.Map.t;
  relative : int64 Core.Int64.Map.t;             (* site -> runtime value *)
  externals : string Core.Int64.Map.t;           (* site -> symbol *)
}

(* The emission run: static per-binary facts and the cross-phase
   state.  One value, created by [emit_program], threaded through the
   lanes; the caller owns the LLVM context and module. *)
type emit_ctx = {
  symtab : Symtab.t option;
  (* The loader's relocation facts, section tiling and owner tiling:
     one immutable index for the whole run. *)
  address : address_index;
  target : Theory.Target.t;
  (* ABI projection of [target], static per binary. *)
  abi : Abi.t;
  sp : var;
  addr_bits : int;
  (* A lifted sub's own term, so its signature is read off its [arg]
     terms; the synthetic conventions (the indirect call and the twins)
     are DERIVED — [synthetic] names them, nothing is stored. *)
  sub_of : sub term Tid.Map.t;
  synthetic : Tid.Set.t;
  (* The KB's synthetic-variable table: every synthetic var's kind, so
     the evaluator resolves through one function. *)
  synth : Hike_synth.table;
  (* Bound once per emission. *)
  llvm_ctx : Llvm.llcontext;
  llvm_module : Llvm.llmodule;
  sections : section list;
  (* Cross-phase state: declarations fill [ll_funcs], the thunk phase
     fills [thunks], the synth phase fills [synth_vals]/[synth_origins];
     later phases read them. *)
  ll_funcs : (Llvm.llvalue * Llvm.lltype) Tid.Map.t ref;
  thunks : (string * Llvm.llvalue) list ref;
  (* The component vars' native byte origins, beside their values in
     [synth_vals]. *)
  synth_origins : int64 Var.Map.t ref;
  (* The synth vars that name a module value: each one's LLVM value,
     bound once before any body emits (module address vars, component
     globals). *)
  synth_vals : Llvm.llvalue Var.Map.t ref;
  (* One executable TLS image with its original Variant-II layout. *)
  tls : (Llvm.llvalue * Hike_spec.tls_spec) option ref;
  trap_fn : Llvm.llvalue option ref;
  (* The hot LLVM types, bound once per emission. *)
  i64_ty : Llvm.lltype;
  ptr_ty : Llvm.lltype;
  word_ty : Llvm.lltype;
  (* The symtab's function-start addresses: the initializer path's
     remap queries precheck this set before touching the symtab. *)
  native_starts : Core.Int64.Set.t;
  (* Every sub's entry address to its tid: the address-to-function
     binding for binaries with no symbol table (a stripped binary's
     re-lifted subs are nameless but their starts are callable). *)
  sub_starts : Tid.t Core.Int64.Map.t;
}

type atomic_kind =
  | Rmw of Llvm.AtomicRMWBinOp.t * exp
  | Compare_exchange of exp * exp
  | Negate

type atomic_action =
  | Atomic_begin of {
      kind : atomic_kind;
      mem : exp;
      addr : exp;
      size : Size.t;
    }
  | Atomic_value of exp

(* The sub-emission scope: every per-sub emission state.  [emit_program]'s
   body loop opens one per sub and drops it at the boundary — nothing
   here survives the sub that created it, so no field needs a clear. *)
type sub_scope = {
  ll_bbs : Llvm.llbasicblock Tid.Map.t ref;
  blk_llvals : blk_llvals Tid.Map.t ref;
  (* Dedups [hike: undef-read:] warnings per (block, var). *)
  undef_warned : Var.Set.t ref Tid.Map.t ref;
  (* The body's frame: routes region/window mem vars; bound around
     body emission. *)
  cur_frame : sub_frame option ref;
  (* One frozen value per never-defined var, so two reads of the same
     undefined register observe identical bits (LLVM's per-use undef
     would fold a self-comparison). *)
  undef_vals : value_map ref;
  (* The Let-temp counter: names need only sub-scoped uniqueness. *)
  let_counter : int ref;
  (* The lock-marker brackets' per-def plans, computed once per sub
     before any body emits.  Key: the def's tid. *)
  atomic_plan : atomic_action Tid.Map.t ref;
  (* Sub-wide SSA bindings: a phi lhs, a versioned def, or a stamped
     call ret — one var, one value, valid wherever the def dominates. *)
  ssavals : value_map ref;
  (* The BIR phi terms' own llvalues, per block. *)
  bir_phis : llvalue_map ref Tid.Map.t ref;
  (* The SSA version maps, read off the blocks' [hike-ssa-versions]
     stamps before any body emits. *)
  ssa_versions : Hike_stack_model.Versions.t Tid.Map.t ref;
  (* Each ptr value's entry-line offset (i64), where it is structurally
     known; a load / parameter / phi has none (the value is a real
     pointer and arithmetic GEPs it). *)
  ptr_offsets : llvalue_map ref;
  (* The per-sub storages: each storage var binds its alloca and
     entry-line base — the lane's per-sub storage bindings. *)
  storages : (Llvm.llvalue * int64) WVarMap.t ref;
}

let fresh_scope () : sub_scope =
  { ll_bbs = ref Tid.Map.empty;
    blk_llvals = ref Tid.Map.empty;
    undef_warned = ref Tid.Map.empty;
    cur_frame = ref None;
    undef_vals = ref WVarMap.empty;
    let_counter = ref 0;
    atomic_plan = ref Tid.Map.empty;
    ssavals = ref WVarMap.empty;
    bir_phis = ref Tid.Map.empty;
    ssa_versions = ref Tid.Map.empty;
    ptr_offsets = ref WVarMap.empty;
    storages = ref WVarMap.empty }

let typ_lltype ctx typ =
  match typ with
  | Imm n -> Llvm.integer_type ctx.llvm_ctx n
  | _ -> ctx.ptr_ty

(* A var's value is a pointer when its sort is [Mem] (the type pass's
   pointer versions and the model's storage) or it is the caller
   window. *)
let var_is_ptr var =
  Hike_stack_model.is_window_var var
  || match Var.typ var with Type.Mem _ -> true | _ -> false

let var_lltype ctx var =
  if var_is_ptr var then ctx.ptr_ty else typ_lltype ctx (Var.typ var)

(* An environment register's process-global cell: one internal module
   global per register, zero-initialized.  Reads load it, defs and phi
   incomings store it — the register never rides a call signature. *)
let env_global ctx (v : var) =
  let name = "hike_env_" ^ Hike_stack_model.sanitize_tid_name (Var.name v) in
  match Llvm.lookup_global name ctx.llvm_module with
  | Some g -> g
  | None ->
    let g =
      Llvm.define_global name
        (Llvm.const_int (var_lltype ctx v) 0)
        ctx.llvm_module
    in
    Llvm.set_linkage Llvm.Linkage.Internal g;
    g

let load_env_reg ctx llvm_builder (v : var) =
  Llvm.build_load (var_lltype ctx v) (env_global ctx v) "" llvm_builder

(* A var whose value is a stack/VLA address (a real pointer).  The
   model's memory-state vars are storage, not pointer values. *)
let is_ptr_var (v : Var.t) : bool =
  (match Hike_synth.classify Hike_synth.empty v with
   | Some (Hike_synth.Bytes _) -> false
   | _ -> true)
  && var_is_ptr v

(* Coerces an integer value of known width to a lane width. *)
let coerce_int_width llvm_ctx llvm_builder ~bits v w =
  if bits = w then v
  else if bits > w then
    Llvm.build_trunc v (Llvm.integer_type llvm_ctx w) "" llvm_builder
  else Llvm.build_zext v (Llvm.integer_type llvm_ctx w) "" llvm_builder

let is_fp_param (ctx : emit_ctx) (v : var) : bool =
  Abi.is_vector_param_reg ctx.abi v

let is_extern ctx (sub_tid : tid) : bool =
  not (Core.Set.mem ctx.synthetic sub_tid)
  &&
  match Core.Map.find ctx.sub_of sub_tid with
  | Some s ->
    (* A block-less sub and a trampoline (the PLT stub whose body never
       runs) are declarations: the loader binds the name. *)
    Hike_stack_model.is_declared s
  | None -> true

(* Strips tid prefixes for LLVM names; the model owns the character set,
   so the emitter's names and the resolver's name map agree. *)
let sanitize_name = Hike_stack_model.sanitize_tid_name

(* The frame's entry-line value. *)
let frame_stack0 (fr : sub_frame) : Llvm.llvalue = fr.entry_line


(* The synthetic indirect-call sub: every pointer call targets it, and
   its convention is [window_conv_args]. *)
let indirect_call_tid : tid = Tid.for_name "indirect_call"

(* The promoted slots in a signature: the thunk twin's arity, and the
   has-slots test's count. *)
let count_slot_args (args : Arg.t list) : int =
  Base.List.count args ~f:(fun a -> Hike_stack_model.is_arg_slot (Arg.lhs a))

let strip_at = Hike_abi.strip_at

let bb_find map tid =
  match Core.Map.find map tid with
  | Some v -> v
  | None -> failwith @@ "bb_find: " ^ Tid.name tid

let blk_llvals_find map tid =
  match Core.Map.find map tid with
  | Some v -> v
  | None -> failwith @@ "blk_llvals.find_exn: " ^ Tid.name tid

(* The convention's register lanes as args of one intent. *)
let reg_args ~intent (regs : var list) : Arg.t list =
  Base.List.map regs ~f:(fun reg -> Arg.create ~intent reg (Var reg))

(* The synthetic indirect-call convention: every register lane a call
   passes (the parameter registers and the variadic count) plus the
   caller-window base — exactly what a pointer call passes and a thunk
   accepts. *)
let window_conv_args ~(word : int) (conv : Abi.t) : Arg.t list =
  let window = Hike_stack_model.hike_window_var ~word in
  reg_args ~intent:In
    (Abi.param_regs conv @ Base.Option.to_list conv.Abi.variadic_count_reg)
  @ [ Arg.create ~intent:In window (Var window) ]

(* A lifted sub carries its own signature on its [arg] terms (the returns
   are the [Out] intents); the synthetic conventions (the indirect call
   and the twins) are DERIVED from the ABI — nothing is stored. *)
let synthetic_args ctx =
  window_conv_args ~word:ctx.abi.Hike_abi.word ctx.abi

let synthetic_rets ctx =
  reg_args ~intent:Out ctx.abi.Abi.return_regs

(* One signature lane's LLVM type: the pointer-tagged lanes pass
   pointers, a return lane wider than a word (the vector carrier) is a
   vector of words so the machine returns it in the vector register, the
   rest keep the BIR type. *)
let lane_is_ptr (a : Arg.t) : bool = var_is_ptr (Arg.lhs a)

(* The vector carrier: a return lane wider than a word. *)
let lane_vector ctx (a : Arg.t) : Llvm.lltype option =
  match Arg.intent a, Var.typ (Arg.lhs a) with
  | Some Out, Type.Imm w when w > ctx.addr_bits ->
    Some
      (Llvm.vector_type (Llvm.integer_type ctx.llvm_ctx ctx.addr_bits)
         (w / ctx.addr_bits))
  | _ -> None

let lane_type ctx (a : Arg.t) : Llvm.lltype =
  if lane_is_ptr a then ctx.ptr_ty
  else
    match lane_vector ctx a with
    | Some t -> t
    | None -> typ_lltype ctx (Var.typ (Arg.lhs a))

(* A lane's LLVM value at its typed home. *)
let lane_value_of (a : Arg.t) (v : Llvm.llvalue) : Bil2llvm_value.t =
  if lane_is_ptr a then Bil2llvm_value.Ptr v else Bil2llvm_value.Int v

let get_args ctx sub_tid =
  match Core.Map.find ctx.sub_of sub_tid with
  | Some sub
    when Base.Option.is_some (Term.first blk_t sub)
         && not (Hike_stack_model.is_plt_trampoline_sub sub) ->
    Hike_stack_model.sig_args sub
  | Some _ | None ->
    (* A declaration's interface is the machine's own convention: the
       bodyless sub (an external the loader binds) and the trampoline
       (the PLT stub — its absorbed body is the loader's protocol,
       never the module's code) carry no lanes of their own. *)
    if Core.Set.mem ctx.synthetic sub_tid then synthetic_args ctx
    else reg_args ~intent:In (Abi.param_regs ctx.abi)

let get_rets ctx sub_tid =
  match Core.Map.find ctx.sub_of sub_tid with
  | Some sub when Base.Option.is_some (Term.first blk_t sub) ->
    Hike_stack_model.sig_rets sub
  | Some _ | None ->
    if Core.Set.mem ctx.synthetic sub_tid then synthetic_rets ctx
    else reg_args ~intent:Out ctx.abi.Abi.return_regs

let goto_label_exn jmp =
  match jmp with Goto l -> l | _ -> failwith "goto_label_exn: ret jmp"

let label_tid label =
  match label with
  | Direct tid -> tid
  | Indirect _ -> failwith "label_tid: indirect label"

let label_exp label =
  match label with
  | Direct _ -> failwith "label_exp: direct label"
  | Indirect exp -> exp

type cf_type =
  | Br
  | Ret
  | CallFun
  | Int
  | CallIndirect
  | CallIndirectTail

let cf_type control_flow =
  let br = Seq.hd_exn control_flow in
  if Hike_return.is_jmp br then Ret
  else
    match Jmp.kind br with
    | Goto _ -> Br
    | Ret _ -> Ret
    | Call c -> (
        match Call.return c with
        | Some _ -> (
            match Call.target c with
            | Direct _ -> CallFun
            | Indirect _ -> CallIndirect)
        | None -> (
            match Call.target c with
            | Indirect _ -> CallIndirectTail
            | Direct _ -> CallFun))
    | Int _ -> Int

let insert_bb scope tid llvm_bb =
  scope.ll_bbs := Core.Map.add_exn !(scope.ll_bbs) ~key:tid ~data:llvm_bb

let get_bb scope tid = bb_find !(scope.ll_bbs) tid

(* The scope's block membership: [None] is a target this sub never
   registered. *)
let get_bb_opt scope tid = Core.Map.find !(scope.ll_bbs) tid

let init_blk_llvals scope blk_tid =
  scope.blk_llvals :=
    Core.Map.add_exn !(scope.blk_llvals) ~key:blk_tid
      ~data:{ locals = ref WVarMap.empty }

let insert_local scope blk_tid var value =
  let blk_llvals = blk_llvals_find !(scope.blk_llvals) blk_tid in
  blk_llvals.locals := WVarMap.add (wvar_of var) value !(blk_llvals.locals)

(* The entry-line offset of a ptr value, when it is structurally known
   (an arithmetic chain from the entry line / a slot). *)
let insert_ptr_offset scope var value =
  scope.ptr_offsets := WVarMap.add (wvar_of var) value !(scope.ptr_offsets)

let get_ptr_offset scope var =
  WVarMap.find_opt (wvar_of var) !(scope.ptr_offsets)

let get_local scope blk_tid var =
  let blk_vars = blk_llvals_find !(scope.blk_llvals) blk_tid in
  WVarMap.find_opt (wvar_of var) !(blk_vars.locals)

(* The sub-wide SSA binding: one var one value (a phi lhs, a
   versioned def, a stamped call ret, or a parameter). *)
let bind_ssaval scope var value =
  scope.ssavals := WVarMap.add (wvar_of var) value !(scope.ssavals)

let get_ssaval scope var =
  WVarMap.find_opt (wvar_of var) !(scope.ssavals)

(* The SSA stamps: one read per sub, before any body emits. *)
let load_ssa_versions scope blks =
  Seq.iter blks ~f:(fun blk ->
      match Term.get_attr blk Hike_stack_model.versions_tag with
      | Some vs ->
          scope.ssa_versions :=
            Core.Map.set !(scope.ssa_versions) ~key:(Term.tid blk) ~data:vs
      | None -> ())

(* A base lane's live version at a block, when it has one: the
   end-of-defs map (pre-mint). *)
let lane_version scope blk_tid v =
  Core.Map.find !(scope.ssa_versions) blk_tid
  |> Base.Option.bind ~f:(fun vs ->
         Base.List.Assoc.find vs.Hike_stack_model.Versions.args v
           ~equal:Var.same)

(* The block's entry versions: the tops before its defs. *)
let entry_version scope blk_tid v =
  Core.Map.find !(scope.ssa_versions) blk_tid
  |> Base.Option.bind ~f:(fun vs ->
         Base.List.Assoc.find vs.Hike_stack_model.Versions.entry v
           ~equal:Var.same)

(* The block's call-ret mints. *)
let mint_version scope blk_tid v =
  Core.Map.find !(scope.ssa_versions) blk_tid
  |> Base.Option.bind ~f:(fun vs ->
         Base.List.Assoc.find vs.Hike_stack_model.Versions.rets v
           ~equal:Var.same)



(* The BIR phi registry: one llvalue per (block, var). *)
let insert_bir_phi scope blk_tid var value =
  let for_blk =
    match Core.Map.find !(scope.bir_phis) blk_tid with
    | Some m -> m
    | None -> ref WVarMap.empty
  in
  for_blk := WVarMap.add (wvar_of var) value !for_blk;
  scope.bir_phis :=
    Core.Map.set !(scope.bir_phis) ~key:blk_tid ~data:for_blk

let get_bir_phi scope blk_tid var =
  match Core.Map.find !(scope.bir_phis) blk_tid with
  | Some m -> WVarMap.find_opt (wvar_of var) !m
  | None -> None

let frozen_undef ctx scope ?(builder : Llvm.llbuilder option) (var : var) :
    Bil2llvm_value.t =
  match WVarMap.find_opt (wvar_of var) !(scope.undef_vals) with
  | Some v -> v
  | None ->
      let typ = var_lltype ctx var in
      let b =
        match builder with
        | Some b -> b
        | None ->
            let entry = get_bb scope Graphs.Tid.start in
            (match Llvm.block_terminator entry with
             | Some t -> Llvm.builder_before ctx.llvm_ctx t
             | None -> Llvm.builder_at_end ctx.llvm_ctx entry)
      in
      let v = Llvm.build_freeze (Llvm.undef typ) "hike_undef" b in
      let v =
        if var_is_ptr var then Bil2llvm_value.Ptr v
        else Bil2llvm_value.Int v
      in
      scope.undef_vals := WVarMap.add (wvar_of var) v !(scope.undef_vals);
      v

let warn_undef_read ctx scope var blk_tid =
  let v = Var.base var in
  let abi = ctx.abi in
  let is_lane = Abi.is_vector_param_reg abi v || Abi.is_return_reg abi v in
  let warned_vars =
    match Core.Map.find !(scope.undef_warned) blk_tid with
    | Some r -> r
    | None ->
        let r = ref Var.Set.empty in
        scope.undef_warned :=
          Core.Map.set !(scope.undef_warned) ~key:blk_tid ~data:r;
        r
  in
  if not (Core.Set.mem !warned_vars v) then begin
    warned_vars := Core.Set.add !warned_vars v;
    if not is_lane then
      Hike_diag.warn "undef-read: blk %s: var %s never defined"
        (Tid.name blk_tid) (Var.name v)
  end

(* Rewrites a lane read to its live version at the block. *)
let lane_exp scope blk_tid (e : exp) : exp =
  (object
    inherit Exp.mapper

    method! map_sym v =
      match lane_version scope blk_tid v with
      | Some w -> w
      | None -> v
  end)#map_exp e


(* Binds one call-ret lane: the stamped version when the SSA pass
   minted one, else the base lane. *)
let bind_call_ret ctx scope blk_tid (ret : Arg.t) value =
  match mint_version scope blk_tid (Arg.lhs ret) with
  | Some v ->
      bind_ssaval scope v value;
      insert_local scope blk_tid v value
  | None -> insert_local scope blk_tid (Arg.lhs ret) value

(* A lane's value at a block: its end-of-defs version, then the
   sub-wide and per-block bindings of the base. *)
let lane_value ctx scope blk_tid v =
  match
    Base.Option.bind (lane_version scope blk_tid v) ~f:(get_ssaval scope)
  with
  | Some x -> x
  | None -> (
      match get_ssaval scope v with
      | Some x -> x
      | None -> (
          match get_local scope blk_tid v with
          | Some x -> x
          | None ->
              warn_undef_read ctx scope v blk_tid;
              frozen_undef ctx scope v))


let call_exn jmp =
  match Jmp.kind jmp with Call j -> j | _ -> failwith "call_exn:"

let finish_call scope llvm_builder fallthrough =
  match fallthrough with
  | Some ft ->
      let bb = get_bb scope ft in
      ignore (Llvm.build_br bb llvm_builder)
  | None -> ignore (Llvm.build_unreachable llvm_builder)

let trap_name = "llvm.trap"

let create_interrupt ctx llvm_builder =
  let trap_ty = Llvm.function_type (Llvm.void_type ctx.llvm_ctx) [||] in
  let trap =
    match !(ctx.trap_fn) with
    | Some f -> f
    | None ->
      let f = Llvm.declare_function trap_name trap_ty ctx.llvm_module in
      ctx.trap_fn := Some f;
      f
  in
  ignore
    (Llvm.build_call trap_ty trap [||] "" llvm_builder);
  ignore (Llvm.build_unreachable llvm_builder)

(* The sub's entry block: the first block in term order among the block
   graph's roots (the start node's successors).  A term can carry several
   roots — a re-lifted main holds each flattened callee's entry — and the
   entry is the block the sub's own execution starts at, which the lift
   put first in the term. *)
let entry_blk_tid sub =
  let cfg = Sub.to_graph sub in
  let roots =
    Graphs.Tid.Node.succs Graphs.Tid.start cfg
    |> Seq.filter ~f:(fun tid -> not (tid = Graphs.Tid.exit))
    |> Seq.to_list
    |> Core.Set.of_list (module Tid)
  in
  match
    Term.enum blk_t sub |> Seq.find ~f:(fun b -> Core.Set.mem roots (Term.tid b))
  with
  | Some b -> Term.tid b
  | None -> failwith "entry_blk_tid: no entry blk"

let is_empty sub =
  let cfg = Sub.to_graph sub in
  Seq.is_empty
    (Graphs.Tid.Node.succs Graphs.Tid.start cfg
    |> Seq.filter ~f:(fun tid -> not (tid = Graphs.Tid.exit)))
