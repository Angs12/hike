(* Emitter environment: KB context vars, the env reader, LLtype helpers,
   the WVar/blk-llvals machinery, the signature/label helpers, and the
   LLVM-name minting.  The module every emitter lane opens. *)

open Bap.Std
open Bap.Std.Bil.Types
open Bap_core_theory
module Abi = Hike_abi
module KB = Bap_knowledge.Knowledge


module EHashtbl = Core.Hashtbl

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
type blk_llvals = { phis : llvalue_map ref; locals : llvalue_map ref }

(* Section types. *)
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
  (* The section's byte image (the initializers render inside
     [emit_program], where the one address map — thunks included —
     lives). *)
  bytes : int array option;
  (* The byte-exact tiling: every address in the section resolves
     through exactly one owner.  Empty = the identity (the one big
     array in [base]). *)
  owners : sec_owner list;
}
type section_type = DATA | RODATA | BSS | GOT | GOTPLT | RODATA_REL | TEXT

let section_type_to_string = function
  | DATA -> "data"
  | RODATA -> "rodata"
  | BSS -> "bss"
  | GOT -> "got"
  | GOTPLT -> "got.plt"
  | RODATA_REL -> "data.rel.ro"
  | TEXT -> "text"

(* One input section of the spec: a byte-image section (its span, word
   count on the word grid, const-ness, image) or the bss span (zeroed
   storage with its copy-relocated slots). *)
type sec_input =
  | Sec_bytes of {
      si_type : section_type;
      si_lo : int64;              (* native span [si_lo, si_hi] *)
      si_hi : int64;
      si_words : int;             (* the word count on the word grid *)
      si_const : bool;
      si_image : int array;       (* the section's byte image *)
    }
  | Sec_bss of {
      si_lo : int64;
      si_hi : int64;
      si_words : int;
      si_copy_relocs : (int * string) list;
    }

(* The section spec: everything the section construction consumes —
   the finalized data tree's Global components, the spans served whole
   (each (id, lo, hi): the section's own image global is the id's
   storage), the word grid, and the input sections in the fixed
   section-list order ([None] = absent from the binary). *)
type section_spec = {
  spec_comps : Hike_stack_model.sec_comp list;
  spec_whole : (int * int64 * int64) list;
  spec_word : int;
  spec_sections : sec_input option list;
}

type emit_ctx = {
  symtab : Symtab.t option;
  (* (lo, hi, base, owners) per reserved section: the section base map —
     every native address in a section renders through its owning
     global. *)
  section_remap : (int64 * int64 * Llvm.llvalue * sec_owner list) list;
  copy_relocs : int64 list;
  target : Theory.Target.t;
  (* ABI projection of [target] — static per binary. Leaf code reads these
     instead of reaching back into the target per def/exp. *)
  abi : Abi.t;
  sp : var;
  ptrsize : int;
  ll_funcs : (Llvm.llvalue * Llvm.lltype) Tid.Map.t ref;
  subs : (Arg.t list * Arg.t list) Tid.Map.t;
  blk_llvals : blk_llvals Tid.Map.t ref;
  ll_bbs : Llvm.llbasicblock Tid.Map.t ref;
  (* One Dead-classification warn per sub. *)
  dead_warned : Tid.Set.t ref;
  (* Dedups [hike: undef-read:] warnings per (sub, var). *)
  undef_warned : Var.Set.t ref Tid.Map.t ref;
  (* Edge-keyed SP restores: (pred, fallthrough) -> post-push+8 value. *)
  edge_sp_restores : (Tid.t, (Tid.t, Llvm.llvalue) EHashtbl.t) EHashtbl.t ref;
  (* The emitted Thunks (memory-convention twins), keyed by the
     sub's LLVM name — function-address rendering produces the twin so
     unresolvable pointer sites stay sound. *)
  thunks : (string * Llvm.llvalue) list ref;
  (* The named-component map: the BIL's [sec_comp_N_mem] var bound to
     its global and the component's native base — the typed channel. *)
  sec_comps : (Var.t * (Llvm.llvalue * int64)) list ref;
  (* Per-sub entry-block freeze of every never-defined var: one
     arbitrary-but-fixed value per register per invocation, so two
     reads of the same undefined register observe the SAME bits (a
     machine self-comparison of an undefined register stays
     deterministic instead of folding to LLVM's per-use undef). *)
  undef_vals : llvalue_map ref;
}

let empty_emit_ctx () : emit_ctx =
  {
    symtab = None;
    section_remap = [];
    copy_relocs = [];
    target = Theory.Target.unknown;
    abi = Abi.x86_64_sysv;
    sp = Abi.x86_64_sysv.sp;
    ptrsize = 0;
    ll_funcs = ref Tid.Map.empty;
    subs = Tid.Map.empty;
    blk_llvals = ref Tid.Map.empty;
    ll_bbs = ref Tid.Map.empty;
    dead_warned = ref Tid.Set.empty;
    undef_warned = ref Tid.Map.empty;
    edge_sp_restores = ref (EHashtbl.create (module Tid));
    thunks = ref [];
    sec_comps = ref [];
    undef_vals = ref WVarMap.empty;
  }

(* Per-sub frame state.  No analysis-record inputs — everything
   here is either LLVM emission state or structure transcribed from the
   sub term (the region geometry from the sub's LAYOUT tag). *)
type sub_frame = {
  (* The sub's anchor address integer: the SP Slot's stored value for
     storage-carrying subs; the constant 0 anchor for storage-free
     subs (the [stack0 = None] fallback readers). *)
  anchor_i64 : Llvm.llvalue;
  (* The per-invocation anchor: the SP entry value bound from the SP
     Slot.  None = the sub owns no SP storage (SP binds to the
     anchor constant, 0 for storage-free subs). *)
  stack0 : Llvm.llvalue option;
  (* The split regions: the BIL's region mem var bound to its alloca
     and the region's entry-relative base — the typed channel (the var
     is the identity; nothing parses names). *)
  regions : (Var.t * (Llvm.llvalue * int64)) list;
}

(* The sub whose body is being emitted: routes the region/window mem
   vars the generic exp lane's twin arms consult (defense in depth —
   the def-level dispatch owns the primary route).  Bound by the body
   emitter around its blocks. *)
let cur_frame : sub_frame option ref = ref None

(* Emission context threaded as a KB var. *)
let llvm_ctx_var : Llvm.llcontext KB.Context.var =
  KB.Context.declare ~package:"hike" "llvm-ctx" (KB.return (Obj.magic 0))

let llvm_module_var : Llvm.llmodule KB.Context.var =
  KB.Context.declare ~package:"hike" "llvm-module" (KB.return (Obj.magic 0))

let section_list_var : section list KB.Context.var =
  KB.Context.declare ~package:"hike" "section-list" (KB.return [])

(* Default emission context. *)
let emit_ctx_var : emit_ctx KB.Context.var =
  KB.Context.declare ~package:"hike" "emit-ctx"
    (KB.return (empty_emit_ctx ()))

(* One reader for the context-get pairs opening most emitters. *)
let emit_env () =
  let open KB in
  let* ctx = Context.get emit_ctx_var in
  let* llvm_ctx = Context.get llvm_ctx_var in
  return (ctx, llvm_ctx)

let typ_lltype_m typ =
  let open KB in
  let* llvm_ctx = Context.get llvm_ctx_var in
  match typ with
  | Imm n -> return @@ Llvm.integer_type llvm_ctx n
  | _ -> return @@ Llvm.pointer_type llvm_ctx

let var_lltype var = typ_lltype_m (Var.typ var)

(* Coerces an integer value of known width to a lane width. *)
let coerce_int_width llvm_ctx llvm_builder ~bits v w =
  if bits = w then v
  else if bits > w then
    Llvm.build_trunc v (Llvm.integer_type llvm_ctx w) "" llvm_builder
  else Llvm.build_zext v (Llvm.integer_type llvm_ctx w) "" llvm_builder

(* Tests for FP arg registers (the convention's vector param lanes). *)
let is_fp_param (ctx : emit_ctx) (v : var) : bool =
  Abi.is_vector_param_reg ctx.abi v

let is_extern ctx (sub_tid : tid) : bool =
  not (Core.Map.mem ctx.subs sub_tid)

(* Strips tid prefixes for LLVM names. *)
let sanitize_name =
  Base.String.filter ~f:(fun c ->
      if c = '#' then false
      else if c = '.' then false
      else if c = '%' then false
      else if c = '\\' then false
      else if c = '@' then false
      else true)

(* Tests for [intrinsic:*] names. *)
let is_intrinsic_name (s : string) : bool =
  Base.String.is_prefix s ~prefix:"intrinsic:"

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

let add_sub_sig subs tid ~rets ~args =
  Core.Map.add_exn subs ~key:tid ~data:(rets, args)

let get_calling_convention ctx =
  Abi.of_target ctx.target

(* The synthetic indirect-call convention: every register lane plus the
   caller-window base as In args — the exact argument list a pointer
   call passes and a thunk accepts. *)
let window_conv_args ~(word : int) (conv : Abi.t) : Arg.t list =
  let window = Hike_stack_model.hike_window_var ~word in
  Base.List.map
    ~f:(fun reg -> Arg.create ~intent:In reg (Var reg))
    (Abi.param_regs conv)
  @ [ Arg.create ~intent:In window (Var window) ]

let get_args ctx sub_tid =
  Base.Option.value_map (Core.Map.find ctx.subs sub_tid) ~f:snd
    ~default:(let callconv = get_calling_convention ctx in
              Base.List.map
                ~f:(fun reg -> Arg.create ~intent:In reg (Var reg))
                (Abi.param_regs callconv))

let get_rets ctx sub_tid =
  Base.Option.value_map (Core.Map.find ctx.subs sub_tid) ~f:fst
    ~default:(let callconv = get_calling_convention ctx in
              Base.List.map
                ~f:(fun reg -> Arg.create ~intent:Out reg (Var reg))
                callconv.return_regs)

let ret_set ctx =
  let callconv = get_calling_convention ctx in
  Var.Set.of_list callconv.return_regs

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

(* The BIR's shape decides the transfer's class: the completion's
   rewritten forms (real Ret jmps, guarded-goto series) read as the
   plain shapes they are. *)
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

let clear_blk_llvals ctx = ctx.blk_llvals := Tid.Map.empty
let clear_bbs ctx = ctx.ll_bbs := Tid.Map.empty
let clear_undef_vals ctx = ctx.undef_vals := WVarMap.empty

let insert_bb ctx tid llvm_bb =
  ctx.ll_bbs := Core.Map.add_exn !(ctx.ll_bbs) ~key:tid ~data:llvm_bb

let get_bb ctx tid = bb_find !(ctx.ll_bbs) tid

let init_blk_llvals ctx blk_tid =
  let phis = ref WVarMap.empty in
  let locals = ref WVarMap.empty in
  ctx.blk_llvals :=
    Core.Map.add_exn !(ctx.blk_llvals) ~key:blk_tid ~data:{ phis; locals }

let insert_phi ctx blk_tid var value =
  let blk_llvals = blk_llvals_find !(ctx.blk_llvals) blk_tid in
  blk_llvals.phis := WVarMap.add (wvar_of var) value !(blk_llvals.phis)

let get_phi ctx blk_tid var =
  let blk_llvals = blk_llvals_find !(ctx.blk_llvals) blk_tid in
  match WVarMap.find_opt (wvar_of var) !(blk_llvals.phis) with
  | Some v -> v
  | None ->
      failwith @@ "Phi " ^ Var.name var ^ " not found at blk "
      ^ Tid.name blk_tid

let insert_local ctx blk_tid var value =
  let blk_llvals = blk_llvals_find !(ctx.blk_llvals) blk_tid in
  blk_llvals.locals := WVarMap.add (wvar_of var) value !(blk_llvals.locals)

let get_local ctx blk_tid var =
  let blk_vars = blk_llvals_find !(ctx.blk_llvals) blk_tid in
  WVarMap.find_opt (wvar_of var) !(blk_vars.locals)

(* Finds [v]'s binding at another width. *)
let probe_local_family ctx blk_tid (v : Var.t) ~(want_w : int) :
    (Llvm.llvalue * int) option =
  let blk_vars = blk_llvals_find !(ctx.blk_llvals) blk_tid in
  let base = Var.base v in
  let bindings =
    WVarMap.bindings !(blk_vars.locals)
    |> List.filter (fun ((WVar (bv, _w)), _) -> Var.same bv base)
    |> List.map (fun ((WVar (_, w)), value) -> (w, value))
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

(* One arbitrary-but-fixed value for a never-defined var: memoized per
   sub, placed in the entry block so it dominates every reader.  While
   the entry block is being built the caller's builder inserts it in
   order; afterwards it inserts before the entry terminator. *)
let frozen_undef ctx ?(builder : Llvm.llbuilder option) (var : var) :
    Llvm.llvalue KB.t =
  let open KB in
  match WVarMap.find_opt (wvar_of var) !(ctx.undef_vals) with
  | Some v -> return v
  | None ->
      let* llvm_ctx = Context.get llvm_ctx_var in
      let* typ = var_lltype var in
      let b =
        match builder with
        | Some b -> b
        | None ->
            let entry = get_bb ctx Graphs.Tid.start in
            (match Llvm.block_terminator entry with
             | Some t -> Llvm.builder_before llvm_ctx t
             | None -> Llvm.builder_at_end llvm_ctx entry)
      in
      let v = Llvm.build_freeze (Llvm.undef typ) "hike_undef" b in
      ctx.undef_vals := WVarMap.add (wvar_of var) v !(ctx.undef_vals);
      return v

let call_exn jmp =
  match Jmp.kind jmp with Call j -> j | _ -> failwith "call_exn:"

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
