(* Emitter environment: the emission run's value ctx, the per-sub
   scope, LLtype helpers, the WVar/blk-llvals machinery, signature and
   label helpers, name minting. *)

open Bap.Std
open Bap.Std.Bil.Types
open Bap_core_theory
module Abi = Hike_abi

module EHashtbl = Core.Hashtbl

(* One RENDERED edge: the block holding the winning terminator, the
   BIR block it belongs to, the edge's SP restore, the jump target.
   Rows are appended per rendered jmp — never merged, so two
   conditional gotos to one target are two rows with two distinct
   terminator blocks. *)
type phi_edge = {
  e_pred : Tid.t;                    (* the edge's BIR block *)
  e_term_bb : Llvm.llbasicblock;     (* the block holding the terminator *)
  e_sp_restore : Llvm.llvalue option;
  e_target : Tid.t;
}

(* Vars keyed by (name, width). *)
type wvar = WVar of Var.t * int

let wvar_of (v : Var.t) : wvar =
  let w = match Var.typ v with Imm w -> w | Mem _ -> 0 | Unk -> 0 in
  WVar (v, w)

module WVar = struct
  type t = wvar
  let compare (WVar (a, wa)) (WVar (b, wb)) =
    let c = Var.compare a b in
    if c <> 0 then c else Int.compare wa wb
end

module WVarMap = Map.Make (WVar)

type llvalue_map = Llvm.llvalue WVarMap.t
type blk_llvals = {
  phis : llvalue_map ref;
  locals : llvalue_map ref;
  (* The same bindings indexed by base var (width, value) lists —
     the width-miss probe reads this, not the whole locals map. *)
  family : (int * Llvm.llvalue) list WVarMap.t ref;
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

let section_type_to_string = function
  | Hike_stack_model.Stack -> "stack"
  | Hike_stack_model.Args -> "args"
  | Hike_stack_model.Data -> "data"
  | Hike_stack_model.Rodata -> "rodata"
  | Hike_stack_model.Bss -> "bss"
  | Hike_stack_model.Got -> "got"
  | Hike_stack_model.Gotplt -> "got.plt"
  | Hike_stack_model.Datarelro -> "data.rel.ro"
  | Hike_stack_model.Text -> "text"

(* One input section of the spec. *)
type sec_input =
  | Sec_bytes of {
      si_type : section_type;
      si_lo : int64;              (* native span [si_lo, si_hi] *)
      si_hi : int64;
      si_words : int;             (* the word count on the word grid *)
      si_const : bool;
      si_image : Bytes.t;       (* the section's byte image *)
    }
  | Sec_bss of {
      si_lo : int64;
      si_hi : int64;
      si_words : int;
      si_copy_relocs : (int * string) list;
    }

(* The section spec: the components, the spans served whole
   (each (id, lo, hi)), the word grid, and the input sections in the
   fixed section-list order ([None] = absent from the binary). *)
type section_spec = {
  spec_comps : Hike_stack_model.sec_comp list;
  spec_whole : (int * int64 * int64) list;
  spec_word : int;
  spec_sections : sec_input option list;
}

type sub_frame = {
  (* The anchor integer: the SP slot's stored value, or the constant
     0 for storage-free subs. *)
  anchor_i64 : Llvm.llvalue;
  (* The SP entry value; None = SP binds to [anchor_i64]. *)
  stack0 : Llvm.llvalue option;
  (* The anchor alloca pointer; None = storage-free. *)
  anchor_ptr : Llvm.llvalue option;
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
  (* PLT-trampoline verdicts, per sub: the O(sub) walk runs once. *)
  plt_trampolines : bool Tid.Map.t ref;
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
  dead_warned : Tid.Set.t ref;
  (* Dedups [hike: undef-read:] warnings per (block, var). *)
  undef_warned : Var.Set.t ref Tid.Map.t ref;
  (* The body's frame: routes region/window mem vars; bound around
     body emission. *)
  cur_frame : sub_frame option ref;
  (* The rendered edges: fresh per scope, owned by Bil2llvm_phi. *)
  edges : phi_edge list ref;
  (* One frozen value per never-defined var, so two reads of the same
     undefined register observe identical bits (LLVM's per-use undef
     would fold a self-comparison). *)
  undef_vals : llvalue_map ref;
}

let fresh_scope () : sub_scope =
  { ll_bbs = ref Tid.Map.empty;
    blk_llvals = ref Tid.Map.empty;
    dead_warned = ref Tid.Set.empty;
    undef_warned = ref Tid.Map.empty;
    cur_frame = ref None;
    edges = ref [];
    undef_vals = ref WVarMap.empty }

let typ_lltype ctx typ =
  match typ with
  | Imm n -> Llvm.integer_type ctx.llvm_ctx n
  | _ -> ctx.ptr_ty

(* The caller-window base is a real pointer; every other lane keeps its
   BIR type. *)
let var_lltype ctx var =
  if Hike_stack_model.is_window_var var then ctx.ptr_ty
  else typ_lltype ctx (Var.typ var)

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

(* The frame's entry-SP value: the SP slot's load, or the constant
   anchor for a storage-free sub. *)
let frame_stack0 (fr : sub_frame) : Llvm.llvalue =
  Base.Option.value fr.stack0 ~default:fr.anchor_i64


(* The synthetic indirect-call sub: every pointer call targets it, and
   its convention is [window_conv_args]. *)
let indirect_call_tid : tid = Tid.for_name "indirect_call"

(* The promoted slots in a signature: the thunk twin's arity, and the
   has-slots test's count. *)
let count_slot_args (args : Arg.t list) : int =
  Base.List.count args ~f:(fun a -> Hike_stack_model.is_arg_slot (Arg.lhs a))

let strip_at (name : string) : string =
  if String.length name > 0 && name.[0] = '@' then
    String.sub name 1 (String.length name - 1)
  else name

let bb_find map tid =
  match Core.Map.find map tid with
  | Some v -> v
  | None -> failwith @@ "bb_find_exn: " ^ Tid.name tid

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
  if Hike_stack_model.is_ptr_arg a then ctx.ptr_ty
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

let cf_type control_flow =
  let br = Seq.hd_exn control_flow in
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
          match Call.target c with Indirect _ -> Ret | Direct _ -> CallFun))
  | Int _ -> Int

let insert_bb scope tid llvm_bb =
  scope.ll_bbs := Core.Map.add_exn !(scope.ll_bbs) ~key:tid ~data:llvm_bb

let get_bb scope tid = bb_find !(scope.ll_bbs) tid

let init_blk_llvals scope blk_tid =
  let phis = ref WVarMap.empty in
  let locals = ref WVarMap.empty in
  let family = ref WVarMap.empty in
  scope.blk_llvals :=
    Core.Map.add_exn !(scope.blk_llvals) ~key:blk_tid
      ~data:{ phis; locals; family }

let insert_phi scope blk_tid var value =
  let blk_llvals = blk_llvals_find !(scope.blk_llvals) blk_tid in
  blk_llvals.phis := WVarMap.add (wvar_of var) value !(blk_llvals.phis)

let get_phi scope blk_tid var =
  let blk_llvals = blk_llvals_find !(scope.blk_llvals) blk_tid in
  match WVarMap.find_opt (wvar_of var) !(blk_llvals.phis) with
  | Some v -> v
  | None ->
      failwith @@ "Phi " ^ Var.name var ^ " not found at blk "
      ^ Tid.name blk_tid

let insert_local scope blk_tid var value =
  let blk_llvals = blk_llvals_find !(scope.blk_llvals) blk_tid in
  blk_llvals.locals := WVarMap.add (wvar_of var) value !(blk_llvals.locals);
  let wvar = wvar_of var in
  let WVar (base, _) = wvar in
  let prev = WVarMap.find_opt (WVar (base, -1)) !(blk_llvals.family) in
  let width =
    match Var.typ var with Type.Imm w -> w | _ -> 0
  in
  blk_llvals.family :=
    WVarMap.add (WVar (base, -1))
      ((width, value) :: Option.value prev ~default:[])
      !(blk_llvals.family)

let get_local scope blk_tid var =
  let blk_vars = blk_llvals_find !(scope.blk_llvals) blk_tid in
  WVarMap.find_opt (wvar_of var) !(blk_vars.locals)

(* Finds [v]'s binding at another width. *)
let probe_local_family scope blk_tid (v : Var.t) ~(want_w : int) :
    (Llvm.llvalue * int) option =
  let blk_vars = blk_llvals_find !(scope.blk_llvals) blk_tid in
  let base = Var.base v in
  let bindings =
    match WVarMap.find_opt (WVar (base, -1)) !(blk_vars.family) with
    | Some l -> l
    | None -> []
  in
  match
    List.sort (fun (w1, _) (w2, _) -> compare w2 w1) bindings
  with
  | [] -> None
  | (w, value) :: _ ->
      Some
        ( value,
          match List.assoc_opt want_w bindings with
          | Some _ -> want_w
          | None -> w )

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
