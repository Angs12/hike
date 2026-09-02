open Bap.Std.Bil.Types
open Bap.Std
open Bap_core_theory
module Abi = Hike_abi

type llvalue_map = Llvm.llvalue Var.Map.t
type blk_llvals = { phis : llvalue_map ref; locals : llvalue_map ref }

(* [EHashtbl]: Core's Hashtbl under the deprecated-name alert the strict
   build treats as an error — the same disarm [module Vsa] uses. *)
module EHashtbl = Core_kernel.Hashtbl[@warning "-D"]

type emit_ctx = {
  symtab : Symtab.t option;
  text_section : (int array * int64 * int64) option;
  section_remap : (int64 * int64 * Llvm.llvalue) list;
  copy_relocs : int64 list;
  target : Theory.Target.t;
  ptrsize : int;
  addr_bits : int;
  ll_funcs : (Llvm.llvalue * Llvm.lltype) Tid.Map.t ref;
  subs : (Arg.t list * Arg.t list) Tid.Map.t;
  blk_llvals : blk_llvals Tid.Map.t ref;
  ll_bbs : Llvm.llbasicblock Tid.Map.t ref;
  guarded_warned : Tid.Set.t ref;
  (* L-E1e FIX (the tty/cat dominance bug): EDGE-KEYED SP-restore
     bindings — (pred_tid, fallthrough_tid) -> the post-push+8 value
     computed IN the pred (call) block. The fallthrough's per-BLOCK
     table can hold only ONE binding per var, so two call preds of the
     same join clobber each other (the last-emitted restore wins and
     its add does not dominate the join's phis — llc "Instruction does
     not dominate all uses"). The edge key makes each pred's restore
     independent; [Bil2llvm.update_phi] consults it before the pred's
     plain binding. *)
  edge_sp_restores : (Tid.t, (Tid.t, Llvm.llvalue) EHashtbl.t) EHashtbl.t ref;
}

let empty_emit_ctx () : emit_ctx =
  {
    symtab = None;
    text_section = None;
    section_remap = [];
    copy_relocs = [];
    target = Theory.Target.unknown;
    ptrsize = 0;
    addr_bits = 0;
    ll_funcs = ref Tid.Map.empty;
    subs = Tid.Map.empty;
    blk_llvals = ref Tid.Map.empty;
    ll_bbs = ref Tid.Map.empty;
    guarded_warned = ref Tid.Set.empty;
    edge_sp_restores = ref (EHashtbl.create (module Tid));
  }

module Vsa = struct
  open Core_kernel[@@warning "-D"]

  (* ARCH-1 — the enum's physical home is the extraction module (the
     cbat_vsa library, where the producer lives); this is the ALIAS
     the ~60 constructor references ([Convutils.Range] etc.) compile
     through unchanged.  [equal_kind] is derived at the definition
     site; the [equal] name below keeps the old references. *)
  type vsa_kind = Cbat_vsa.Cbat_extraction.kind =
    | Range of int64 * int64
    | Infinite of int64 * int64
    | Unbounded
    | Dead
    | VLA of Tid.t
  [@@deriving equal]

  type region = {
    id : int;
    span : int64 * int64;
    members : (Tid.t * (int64 * int64)) list;
    convertible : bool;
    max_width : int;
  }
  [@@deriving equal]

  (* THE STACK MODEL DECISION for a sub: [plan <> []] means the sub's
     stack is SPLIT into per-region [stack_rN] allocas (the optimized
     shape — every convertible access became a BIL local and every
     surviving memory access resolves inside a region); [plan = []]
     means ONE big [%frame] alloca covers all of it (the SOUND FALLBACK,
     always correct, unoptimized).

     Computed ONCE by [Hike_stack_model.split_plan] — Finding 1:
     the decision has ONE producer and three CONSUMERS ([Hike_stack_to_
     locals], [Hike_dce], [Bil2llvm]). It is a property of the
     PRE-rewrite sub (the converted slots vanish once stack-to-locals
     runs), so the vsa pass computes it and carries it here. *)
  type split_plan = region list [@@deriving equal]

  (* [vsa_info]: the VSA's per-def results for one sub.

     [offsets], [k_ranges] and [vla_bounds] are MAPS keyed by the def's
     tid — each is a per-DEF fact (one tag, one k-range, one VLA bound per
     def), so a map is what they are; the old association-list shape made
     every per-def lookup a linear scan and pushed a private refold into
     each consumer. [@@deriving equal] works on maps, so the KB join
     domain (and its [Vsa_info_conflict] detection) is unaffected. *)
  type vsa_info = {
    offsets : vsa_kind Tid.Map.t;
    k_ranges : (int64 * int64) Tid.Map.t;
    regions : region list;
    stack_plan : split_plan;
    degraded : bool;
    vla_bounds : (int64 * int64) Tid.Map.t;
  }
  [@@deriving equal]

  (* [empty_vsa_info]: the no-tags info (the [sub_info = None] default and
     the "nothing stack-relevant here" answer). *)
  let empty_vsa_info : vsa_info =
    { offsets = Tid.Map.empty; k_ranges = Tid.Map.empty; regions = [];
      stack_plan = []; degraded = false; vla_bounds = Tid.Map.empty }
end
include Vsa

(* Hidden stack-threading parameter: callee's entry RSP passed by caller. *)
let hike_stack_var : var =
  Var.create ~is_virtual:false ~fresh:false "hike_stack" (Type.Imm 64)

let kind_lo = function
  | Range (lo, _) | Infinite (lo, _) -> lo
  | Unbounded | Dead | VLA _ -> 0L

let is_positive_kind (kind : vsa_kind) : bool =
  Int64.compare (kind_lo kind) 0L > 0

let is_mem var = match Var.typ var with Mem _ -> true | _ -> false

type section = { base : Llvm.llvalue; min_addr : word; max_addr : word }
type section_type = DATA | RODATA | BSS | GOT | GOTPLT | RODATA_REL | TEXT

let section_type_to_string = function
  | DATA -> "data"
  | RODATA -> "rodata"
  | BSS -> "bss"
  | GOT -> "got"
  | GOTPLT -> "got.plt"
  | RODATA_REL -> "data.rel.ro"
  | TEXT -> "text"

let blk_llvals_find map tid =
  match Core.Map.find map tid with
  | Some v -> v
  | None -> failwith @@ "blk_llvals.find_exn: " ^ Tid.name tid

(* Strip BAP tid prefixes (@, #, ., etc.) for LLVM names. *)
let sanitize_name =
  Base.String.filter ~f:(fun c ->
      if c = '#' then false
      else if c = '.' then false
      else if c = '%' then false
      else if c = '\\' then false
      else if c = '@' then false
      else true)

let bb_find map tid =
  match Core.Map.find map tid with
  | Some v -> v
  | None -> failwith @@ "bb_find_exn: " ^ Tid.name tid

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

let is_void _ = false

let label_tid label =
  match label with
  | Direct tid -> tid
  | Indirect _ -> failwith "label_tid: indirect label"

let label_exp label =
  match label with
  | Direct _ -> failwith "label_exp: direct label"
  | Indirect exp -> exp

type cf_type = Br | Ret | CallFun | Int | CallFunVoid | CallIndirect

let clear_blk_llvals ctx = ctx.blk_llvals := Tid.Map.empty
let clear_bbs ctx = ctx.ll_bbs := Tid.Map.empty

let insert_bb ctx tid llvm_bb =
  ctx.ll_bbs := Core.Map.add_exn !(ctx.ll_bbs) ~key:tid ~data:llvm_bb

let get_bb ctx tid = bb_find !(ctx.ll_bbs) tid

let init_blk_llvals ctx blk_tid =
  let phis = ref Var.Map.empty in
  let locals = ref Var.Map.empty in
  ctx.blk_llvals :=
    Core.Map.add_exn !(ctx.blk_llvals) ~key:blk_tid ~data:{ phis; locals }

let insert_phi ctx blk_tid var value =
  let blk_llvals = blk_llvals_find !(ctx.blk_llvals) blk_tid in
  blk_llvals.phis := Core.Map.add_exn !(blk_llvals.phis) ~key:var ~data:value

let get_phi ctx blk_tid var =
  let blk_llvals = blk_llvals_find !(ctx.blk_llvals) blk_tid in
  match Core.Map.find !(blk_llvals.phis) var with
  | Some v -> v
  | None ->
      failwith @@ "Phi " ^ Var.name var ^ " not found at blk "
      ^ Tid.name blk_tid

let insert_local ctx blk_tid var value =
  let blk_llvals = blk_llvals_find !(ctx.blk_llvals) blk_tid in
  blk_llvals.locals := Core.Map.set !(blk_llvals.locals) ~key:var ~data:value

let get_local ctx blk_tid var =
  let blk_vars = blk_llvals_find !(ctx.blk_llvals) blk_tid in
  Core.Map.find !(blk_vars.locals) var

let is_goto jmp = match Jmp.kind jmp with Goto _ -> true | _ -> false

let cf_type control_flow =
  let br = Seq.hd_exn control_flow in
  match Jmp.kind br with
  | Goto _ -> Br
  | Ret _ -> Ret
  | Call c -> (
      match Call.return c with
      | Some _ -> (
          match Call.target c with
          | Direct tid -> if is_void tid then CallFunVoid else CallFun
          | Indirect _ -> CallIndirect)
      | None -> (
          match Call.target c with Indirect _ -> Ret | Direct _ -> CallFun))
  | Int _ -> Int

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
