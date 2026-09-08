open Bap.Std.Bil.Types
open Bap.Std
open Bap_core_theory
module Abi = Hike_abi

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

(* Core Hashtbl with the deprecated warning off. *)
module EHashtbl = Core_kernel.Hashtbl[@warning "-D"]

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
  fp : var;
  ptrsize : int;
  ll_funcs : (Llvm.llvalue * Llvm.lltype) Tid.Map.t ref;
  subs : (Arg.t list * Arg.t list) Tid.Map.t;
  blk_llvals : blk_llvals Tid.Map.t ref;
  ll_bbs : Llvm.llbasicblock Tid.Map.t ref;
  guarded_warned : Tid.Set.t ref;
  (* Dedups [hike: undef-read:] warnings per (sub, var). *)
  undef_warned : Var.Set.t ref Tid.Map.t ref;
  (* Edge-keyed SP restores: (pred, fallthrough) -> post-push+8 value. *)
  edge_sp_restores : (Tid.t, (Tid.t, Llvm.llvalue) EHashtbl.t) EHashtbl.t ref;
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
    fp = Abi.x86_64_sysv.fp;
    ptrsize = 0;
    ll_funcs = ref Tid.Map.empty;
    subs = Tid.Map.empty;
    blk_llvals = ref Tid.Map.empty;
    ll_bbs = ref Tid.Map.empty;
    guarded_warned = ref Tid.Set.empty;
    undef_warned = ref Tid.Map.empty;
    edge_sp_restores = ref (EHashtbl.create (module Tid));
  }

module Vsa = struct
  open Core_kernel[@@warning "-D"]

  (* Alias of the kind enum in [Cbat_extraction]. *)
  type vsa_kind = Cbat_vsa.Cbat_extraction.kind =
    | Range of int64 * int64
    | Infinite of int64 * int64
    | Unbounded
    | Dead
    | VLA of Tid.t
  (* Aliases [equal_kind] for [@@deriving equal]. *)
  let equal_vsa_kind = Cbat_vsa.Cbat_extraction.equal_kind

  type region = {
    id : int;
    span : int64 * int64;
    members : (Tid.t * (int64 * int64)) list;
    convertible : bool;
    max_width : int;
  }
  [@@deriving equal]

  (* [plan <> []] splits into [stack_rN] allocas; [[]] uses one [%frame]. *)
  type split_plan = region list [@@deriving equal]

  (* Per-def index maps: [offsets] and [k_ranges]. *)
  type vsa_info = {
    offsets : vsa_kind Tid.Map.t;
    k_ranges : (int64 * int64) Tid.Map.t;
    regions : region list;
    stack_plan : split_plan;
    degraded : bool;
    vla_bounds : (int64 * int64) Tid.Map.t;
    (* Dynamic-allocation defs (spec §2.3); the producer's one detection,
       read by the stack model and the emitter instead of re-detecting. *)
    vla_alloc_tids : Tid.Set.t;
  }

  (* Hand-written equality over maps. *)
  (* Pair equality, shared by both int64-pair maps. *)
  let equal_int64_pair ((a1, b1) : int64 * int64) ((a2, b2) : int64 * int64) : bool =
    Int64.equal a1 a2 && Int64.equal b1 b2

  let equal_krange = equal_int64_pair
  let equal_vla_bound = equal_int64_pair

  let equal_vsa_info (i1 : vsa_info) (i2 : vsa_info) : bool =
    Core.Map.equal equal_vsa_kind i1.offsets i2.offsets
    && Core.Map.equal equal_krange i1.k_ranges i2.k_ranges
    && Base.List.equal equal_region i1.regions i2.regions
    && Base.List.equal equal_region i1.stack_plan i2.stack_plan
    && Bool.equal i1.degraded i2.degraded
    && Core.Map.equal equal_vla_bound i1.vla_bounds i2.vla_bounds
    && Core.Set.equal i1.vla_alloc_tids i2.vla_alloc_tids

  (* Builds info from maps. *)
  let mk_vsa_info_maps ~offsets ~k_ranges ~regions ~stack_plan ~degraded
      ~vla_bounds ~vla_alloc_tids : vsa_info =
    { offsets; k_ranges; regions; stack_plan; degraded; vla_bounds;
      vla_alloc_tids }

  (* Builds info from lists. *)
  let mk_vsa_info ~offsets ~k_ranges ~regions ~stack_plan ~degraded
      ~vla_bounds ~vla_alloc_tids : vsa_info =
    mk_vsa_info_maps
      ~offsets:
        (Base.List.fold_left offsets ~init:Tid.Map.empty
           ~f:(fun m (tid, kind) -> Core.Map.set m ~key:tid ~data:kind))
      ~k_ranges:
        (Base.List.fold_left k_ranges ~init:Tid.Map.empty
           ~f:(fun m (tid, klo, khi) -> Core.Map.set m ~key:tid ~data:(klo, khi)))
      ~regions ~stack_plan ~degraded
      ~vla_bounds:
        (Base.List.fold_left vla_bounds ~init:Tid.Map.empty
           ~f:(fun m (tid, (a, b)) -> Core.Map.set m ~key:tid ~data:(a, b)))
      ~vla_alloc_tids

  (* Info with no tags. *)
  let empty_vsa_info : vsa_info =
    mk_vsa_info_maps ~offsets:Tid.Map.empty ~k_ranges:Tid.Map.empty
      ~regions:[] ~stack_plan:[] ~degraded:false ~vla_bounds:Tid.Map.empty
      ~vla_alloc_tids:Tid.Set.empty
end
include Vsa

(* Callee entry RSP passed by caller. *)
let hike_stack_var : var =
  Var.create ~is_virtual:false ~fresh:false "hike_stack" (Type.Imm 64)

let is_positive_kind = function
  | Range (lo, _) | Infinite (lo, _) -> Int64.compare lo 0L >= 0
  | Unbounded | Dead | VLA _ -> false

let is_mem var = match Var.typ var with Mem _ -> true | _ -> false

(* Tests for [intrinsic:*] names. *)
let is_intrinsic_name (s : string) : bool =
  Base.String.is_prefix s ~prefix:"intrinsic:"

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

(* Strips tid prefixes for LLVM names. *)
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

let label_tid label =
  match label with
  | Direct tid -> tid
  | Indirect _ -> failwith "label_tid: indirect label"

let label_exp label =
  match label with
  | Direct _ -> failwith "label_exp: direct label"
  | Indirect exp -> exp

type cf_type = Br | Ret | CallFun | Int | CallIndirect

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
          | Direct _ -> CallFun
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
