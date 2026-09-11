(* Emitter environment: KB context vars, the env reader, LLtype helpers.

   S10b: the emitter half of the convutils drawer dissolved here — the
   emit context (and its section types), the WVar/blk-llvals machinery,
   the signature/label helpers, and the LLVM-name minting.  This is the
   module every emitter lane already opened. *)

open Bap.Std
open Bap.Std.Bil.Types
open Bap_core_theory
module Abi = Hike_abi
module KB = Bap_knowledge.Knowledge


(* Core Hashtbl with the deprecated warning off. *)
module EHashtbl = Core_kernel.Hashtbl[@warning "-D"]

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
type section = {
  base : Llvm.llvalue;
  min_addr : word;
  max_addr : word;
  (* The section's byte image (T4: the initializers render inside
     [emit_program], where the one address map — thunks included —
     lives). *)
  bytes : int array option;
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

type emit_ctx = {
  symtab : Symtab.t option;
  text_section : (int array * int64 * int64) option;
  section_remap : (int64 * int64 * Llvm.llvalue) list;
  copy_relocs : int64 list;
  target : Theory.Target.t;
  (* ABI projection of [target] — static per binary. Leaf code reads these
     instead of reaching back into the target per def/exp (ticket 03). *)
  abi : Abi.t;
  sp : var;
  ptrsize : int;
  ll_funcs : (Llvm.llvalue * Llvm.lltype) Tid.Map.t ref;
  subs : (Arg.t list * Arg.t list) Tid.Map.t;
  blk_llvals : blk_llvals Tid.Map.t ref;
  ll_bbs : Llvm.llbasicblock Tid.Map.t ref;
  guarded_warned : Tid.Set.t ref;
  (* One Dead-classification warn per sub. *)
  dead_warned : Tid.Set.t ref;
  (* The sub's stack anchor: (storage llval, anchor address integer,
     anchor byte index) — ONE fact computed once per sub (create_sub)
     and consumed twice: create_addr_ptr routes LICENSED address
     integers through it as GEPs, and the SP Slot binds the anchor
     integer as stack_0.  A frame sub anchors to its %frame alloca; a
     precise (region-split) sub anchors to its first region alloca
     (index 0).  [None] = the sub owns no stack storage (tag-free,
     non-degraded); the absent anchor is then NEVER queried — a
     licensed address requires a Range/Infinite tag on some def, and a
     tagged sub always owns stack storage (frame or region split). *)
  stack_anchor : (Llvm.llvalue * Llvm.llvalue * int64) option ref;
  (* The address-materialization license (ticket T1): set per def from
     the def's VSA tag — a Range/Infinite whose lower bound is negative
     proves the access lives in THIS sub's frame, licensing the anchor
     GEP in create_addr_ptr.  Every other tag (Unbounded, VLA,
     none — foreign pointers: the sret pointer, reloaded pointers,
     dynamic-alloca addresses) leaves the license false and the address
     integer materializes via inttoptr (the exception lane): wrapping an
     unproven address claims the frame as its LLVM underlying object,
     and the consumer's optimizer then reasons such accesses die with
     this frame — the typed-model opt-safety regression. *)
  frame_wrap_license : bool ref;
  (* Dedups [hike: undef-read:] warnings per (sub, var). *)
  undef_warned : Var.Set.t ref Tid.Map.t ref;
  (* Edge-keyed SP restores: (pred, fallthrough) -> post-push+8 value. *)
  edge_sp_restores : (Tid.t, (Tid.t, Llvm.llvalue) EHashtbl.t) EHashtbl.t ref;
  (* T4: the emitted Thunks (memory-convention twins), keyed by the
     sub's LLVM name — function-address rendering produces the twin so
     unresolvable pointer sites stay sound. *)
  thunks : (string * Llvm.llvalue) list ref;
}

let empty_emit_ctx () : emit_ctx =
  {
    symtab = None;
    text_section = None;
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
    guarded_warned = ref Tid.Set.empty;
    dead_warned = ref Tid.Set.empty;
    (* The empty record before the first sub — not a mode: create_sub
       assigns every sub's computed anchor before any def emits. *)
    stack_anchor = ref None;
    frame_wrap_license = ref false;
    undef_warned = ref Tid.Map.empty;
    edge_sp_restores = ref (EHashtbl.create (module Tid));
    thunks = ref [];
  }

(* Per-sub frame state.  T10: no analysis-record inputs — everything
   here is either LLVM emission state or structure transcribed from the
   sub term (the region geometry from the sub's LAYOUT tag). *)
type sub_frame = {
  (* The sub's anchor address integer: the SP Slot's stored value for
     storage-carrying subs; the constant 0 anchor for storage-free
     subs (the [stack0 = None] fallback readers). *)
  anchor_i64 : Llvm.llvalue;
  (* The caller-window base local (the Caller-Window Parameter), when
     the sub carries one (variadic/mixed — the T4 residual). *)
  stack : Llvm.llvalue option;
  (* The per-invocation anchor: the SP entry value bound from the SP
     Slot (T4).  None = the sub owns no SP storage (SP binds to the
     anchor constant, 0 for storage-free subs). *)
  stack0 : Llvm.llvalue option;
  (* The split regions: ((id, span), base alloca) — geometry from the
     sub's LAYOUT tag. *)
  regions : ((int * (int64 * int64)) * Llvm.llvalue) list;
  (* The sub split into regions (the layout's regions are non-empty). *)
  is_precise : bool;
}
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

(* Tests for FP arg registers. *)
let is_fp_param (v : var) : bool =
  Base.String.is_prefix (Var.name (Var.base v)) ~prefix:Abi.vector_param_prefix

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

let get_args ctx sub_tid =
  match Core.Map.find ctx.subs sub_tid with
  | Some (_, args) -> args
  | None ->
      let callconv = get_calling_convention ctx in
      Base.List.map
        ~f:(fun reg -> Arg.create ~intent:In reg (Var reg))
        (callconv.int_param_regs @ callconv.vector_param_regs)

let get_rets ctx sub_tid =
  match Core.Map.find ctx.subs sub_tid with
  | Some (rets, _) -> rets
  | None ->
      let callconv = get_calling_convention ctx in
      Base.List.map
        ~f:(fun reg -> Arg.create ~intent:Out reg (Var reg))
        callconv.return_regs

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

type cf_type = Br | Ret | CallFun | Int | CallIndirect

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

let call_exn jmp =
  match Jmp.kind jmp with Call j -> j | _ -> failwith "call_exn:"

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
