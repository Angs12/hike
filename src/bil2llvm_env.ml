(* Emitter environment: the emission run's value ctx, the per-sub
   scope, LLtype helpers, the WVar/blk-llvals machinery, signature and
   label helpers, name minting. *)

open Bap.Std
open Bap.Std.Bil.Types
open Bap_core_theory
module Abi = Hike_abi

module EHashtbl = Core.Hashtbl

(* The pure integer constructors, shared by the expression lane and the
   pointer module (which must not depend on the expression lane). *)
let create_binop llvm_builder (op, llvm_val1, llvm_val2) =
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
  match op with
  | NEG -> Llvm.build_neg llvm_val "" llvm_builder
  | NOT -> Llvm.build_not llvm_val "" llvm_builder

(* Vars are keyed by name; the retype changes a var's sort but not its
   identity (`Var.compare` is the ident), so a binding written for one
   sort is readable through the other. *)
type wvar = Var.t

let wvar_of (v : Var.t) : wvar = v

module WVar = struct
  type t = wvar
  let compare = Var.compare
end

module WVarMap = Map.Make (WVar)

type llvalue_map = Llvm.llvalue WVarMap.t
type blk_llvals = {
  phis : llvalue_map ref;
  locals : llvalue_map ref;
}

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

(* The trap-id vocabulary's one test (the divide-by-zero interrupt sub). *)
let is_interrupt_name (n : string) : bool =
  Base.String.is_prefix n ~prefix:"@interrupt:"

(* LLVM's indirectbr count reserves destination slots; it is not the
   destination set. *)
let indirect_br_one_reserved = 1
let indirect_br_no_reserved = 0
let build_indirect_br llvm_builder target ~reserved_destinations =
  Llvm.build_indirect_br target reserved_destinations llvm_builder

(* One input section of the spec: the model's [sec_meta] row —
   [sm_image] is the section's byte image, None for the bss region. *)

(* The section spec: the components, the spans served whole
   (each (id, lo, hi)), the word grid, the input sections in the
   fixed section-list order ([None] = absent from the binary), and the
   absolute copy-relocation slot addresses used by access routing. *)
type section_spec = {
  spec_comps : Hike_stack_model.sec_comp list;
  spec_whole : (int * int64 * int64) list;
  spec_word : int;
  spec_sections : Hike_stack_model.sec_meta option list;
  (* Absolute addresses of copy-relocated slots, for access routing. *)
  spec_copy_relocs : int64 list;
}

type sub_frame = {
  (* The model entry line: the seeded SP's absolute address.  A constant,
      so every address is derived from the model offsets, and every
      storage GEP's index is [address − entry_line − rel]. *)
  entry_line : Llvm.llvalue;
  (* The entry line as a pointer into the residue (None = no storage). *)
  entry_ptr : Llvm.llvalue option;
  (* Region mem var -> (alloca, entry-relative base). *)
  regions : (Var.t * (Llvm.llvalue * int64)) list;
}

(* The emission run: static per-binary facts and the cross-phase
   state.  One value, created by [emit_program], threaded through the
   lanes; the caller owns the LLVM context and module. *)
type emit_ctx = {
  symtab : Symtab.t option;
  (* The section base map: every native address renders through its
     owning global. *)
  copy_relocs : int64 list;
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
  (* Bound once per emission. *)
  llvm_ctx : Llvm.llcontext;
  llvm_module : Llvm.llmodule;
  sections : section list;
  (* Cross-phase state: declarations fill [ll_funcs], the thunk phase
     fills [thunks], the preamble fills [sec_comps]; later phases
     read them. *)
  ll_funcs : (Llvm.llvalue * Llvm.lltype) Tid.Map.t ref;
  thunks : (string * Llvm.llvalue) list ref;
  (* [sec_comp_N_mem] var -> (global, native base). *)
  sec_comps : (Llvm.llvalue * int64) Var.Map.t ref;
  (* The TLS anchor global and the llvm.trap function, declared once. *)
  tls_anchor : Llvm.llvalue option ref;
  trap_fn : Llvm.llvalue option ref;
  (* The hot LLVM types, bound once per emission. *)
  i64_ty : Llvm.lltype;
  ptr_ty : Llvm.lltype;
  word_ty : Llvm.lltype;
  (* The symtab's function-start addresses: the initializer path's
     remap queries precheck this set before touching the symtab. *)
  native_starts : Core.Int64.Set.t;
}

(* The sub-emission scope: every per-sub emission state.  [emit_program]'s
   body loop opens one per sub and drops it at the boundary — nothing
   here survives the sub that created it, so no field needs a clear. *)
type sub_scope = {
  ll_bbs : Llvm.llbasicblock Tid.Map.t ref;
  blk_llvals : blk_llvals Tid.Map.t ref;
  (* One Dead-classification warn per sub. *)
  dead_warned : bool ref;
  (* Dedups [hike: undef-read:] warnings per (block, var). *)
  undef_warned : Var.Set.t ref Tid.Map.t ref;
  (* The body's frame: routes region/window mem vars; bound around
     body emission. *)
  cur_frame : sub_frame option ref;
  (* The vars whose value is an above-entry stack address (a window
     value): a store of one materializes the real address. *)
  window_vars : Var.Set.t ref;
  (* One frozen value per never-defined var, so two reads of the same
     undefined register observe identical bits (LLVM's per-use undef
     would fold a self-comparison). *)
  undef_vals : llvalue_map ref;
  (* The Let-temp counter: names need only sub-scoped uniqueness. *)
  let_counter : int ref;
  (* Sub-wide SSA bindings: a phi lhs, a versioned def, or a stamped
     call ret — one var, one value, valid wherever the def dominates. *)
  ssavals : llvalue_map ref;
  (* The BIR phi terms' own llvalues, per block. *)
  bir_phis : llvalue_map ref Tid.Map.t ref;
  (* The SSA version maps, read off the blocks' [hike-ssa-versions]
     stamps before any body emits. *)
  ssa_versions : Hike_stack_model.Versions.t Tid.Map.t ref;
  (* Each ptr value's entry-line offset (i64), where it is structurally
     known; a load / parameter / phi has none (the value is a real
     pointer and arithmetic GEPs it). *)
  ptr_offsets : llvalue_map ref;
  (* The section-component storage base vars -> their globals. *)
  sec_comp_ptrs : llvalue_map ref;
}

let fresh_scope () : sub_scope =
  { ll_bbs = ref Tid.Map.empty;
    blk_llvals = ref Tid.Map.empty;
    dead_warned = ref false;
    undef_warned = ref Tid.Map.empty;
    cur_frame = ref None;
    window_vars = ref Var.Set.empty;
    undef_vals = ref WVarMap.empty;
    let_counter = ref 0;
    ssavals = ref WVarMap.empty;
    bir_phis = ref Tid.Map.empty;
    ssa_versions = ref Tid.Map.empty;
    ptr_offsets = ref WVarMap.empty;
    sec_comp_ptrs = ref WVarMap.empty }

let typ_lltype ctx typ =
  match typ with
  | Imm n -> Llvm.integer_type ctx.llvm_ctx n
  | _ -> ctx.ptr_ty

(* The caller-window base is a real pointer; every other lane keeps its
   BIR type.  A [Mem]-typed var is a pointer (a stack/VLA address). *)
let var_lltype ctx var =
  if Hike_stack_model.is_window_var var then ctx.ptr_ty
  else typ_lltype ctx (Var.typ var)

(* A var whose value is a stack/VLA address (a real pointer).  The
   model's memory-state vars are storage, not pointer values. *)
let is_ptr_var (v : Var.t) : bool =
  (not
     (Hike_stack_model.is_region_mem v
     || Hike_stack_model.is_window_mem v
     || Hike_stack_model.is_sec_comp_mem v))
  && (Hike_stack_model.is_window_var v
     || match Var.typ v with Type.Mem _ -> true | _ -> false)

(* Coerces an integer value of known width to a lane width. *)
let coerce_int_width llvm_ctx llvm_builder ~bits v w =
  if bits = w then v
  else if bits > w then
    Llvm.build_trunc v (Llvm.integer_type llvm_ctx w) "" llvm_builder
  else Llvm.build_zext v (Llvm.integer_type llvm_ctx w) "" llvm_builder

let is_fp_param (ctx : emit_ctx) (v : var) : bool =
  Abi.is_vector_param_reg ctx.abi v

let is_extern ctx (sub_tid : tid) : bool =
  (not (Core.Map.mem ctx.sub_of sub_tid))
  && not (Core.Set.mem ctx.synthetic sub_tid)

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

(* The synthetic indirect-call convention: every register lane plus
   the caller-window base — exactly what a pointer call passes and a
   thunk accepts. *)
let window_conv_args ~(word : int) (conv : Abi.t) : Arg.t list =
  let window = Hike_stack_model.hike_window_var ~word in
  reg_args ~intent:In (Abi.param_regs conv)
  @ [ Arg.create ~intent:In window (Var window) ]

(* A lifted sub carries its own signature on its [arg] terms (the returns
   are the [Out] intents); the synthetic conventions (the indirect call
   and the twins) are DERIVED from the ABI — nothing is stored. *)
let synthetic_args ctx =
  window_conv_args ~word:ctx.abi.Hike_abi.word ctx.abi

let synthetic_rets ctx =
  reg_args ~intent:Out ctx.abi.Abi.return_regs

(* One signature lane's LLVM type: the pointer-tagged lanes pass
   pointers, the rest keep the BIR type. *)
let lane_type ctx (a : Arg.t) : Llvm.lltype =
  if Hike_stack_model.is_ptr_arg a || Hike_stack_model.is_arg_ptr_kind a then
    ctx.ptr_ty
  else var_lltype ctx (Arg.lhs a)

let get_args ctx sub_tid =
  match Core.Map.find ctx.sub_of sub_tid with
  | Some sub -> Hike_stack_model.sig_args sub
  | None ->
      if Core.Set.mem ctx.synthetic sub_tid then synthetic_args ctx
      else reg_args ~intent:In (Abi.param_regs ctx.abi)

let get_rets ctx sub_tid =
  match Core.Map.find ctx.sub_of sub_tid with
  | Some sub -> Hike_stack_model.sig_rets sub
  | None ->
      if Core.Set.mem ctx.synthetic sub_tid then synthetic_rets ctx
      else reg_args ~intent:Out ctx.abi.Abi.return_regs

let ret_set ctx = Var.Set.of_list ctx.abi.Abi.return_regs

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

let init_blk_llvals scope blk_tid =
  let phis = ref WVarMap.empty in
  let locals = ref WVarMap.empty in
  scope.blk_llvals :=
    Core.Map.add_exn !(scope.blk_llvals) ~key:blk_tid
      ~data:{ phis; locals }

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

let has_bir_phi scope blk_tid var =
  Base.Option.is_some (get_bir_phi scope blk_tid var)

(* One frozen value per never-defined var, memoized per sub and
   placed in the entry block so it dominates every reader. *)
let frozen_undef ctx scope ?(builder : Llvm.llbuilder option) (var : var) :
    Llvm.llvalue =
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

let entry_blk_tid sub =
  let cfg = Sub.to_graph sub in
  let entry_blks = Graphs.Tid.Node.succs Graphs.Tid.start cfg in
  let entry_blks =
    Seq.filter entry_blks ~f:(fun tid -> not (tid = Graphs.Tid.exit))
  in
  let entry_blk = Seq.min_elt entry_blks ~compare:Tid.compare in
  match entry_blk with
  | None -> failwith "entry_blk_tid: no entry blk"
  | Some tid -> tid

let is_empty sub =
  let cfg = Sub.to_graph sub in
  Seq.is_empty
    (Graphs.Tid.Node.succs Graphs.Tid.start cfg
    |> Seq.filter ~f:(fun tid -> not (tid = Graphs.Tid.exit)))
