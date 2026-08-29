open Bap.Std.Bil.Types
open Bap.Std
open Bap_core_theory

type llvalue_map = Llvm.llvalue Var.Map.t
type blk_llvals = { phis : llvalue_map ref; locals : llvalue_map ref }

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
  }

module Vsa = struct
  open Core_kernel[@@warning "-D"]

  type vsa_kind =
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

  type vsa_info = {
    offsets : (Tid.t * vsa_kind) list;
    k_ranges : (Tid.t * int64 * int64) list;
    regions : region list;
    degraded : bool;
    call_stack_args : (Tid.t * (int * int64) list) list;
    vla_bounds : (Tid.t * (int64 * int64)) list;
  }
  [@@deriving equal]
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
  if Theory.Target.matches ctx.target "x86_64-gnu-elf" then
    Calling_conventions.x86_64_sysv
  else failwith "abi not supported"

let typ_lltype llvm_ctx typ =
  match typ with
  | Imm n -> Llvm.integer_type llvm_ctx n
  | _ -> Llvm.pointer_type llvm_ctx

let get_direct_call jmp =
  match Jmp.kind jmp with
  | Call c -> (
      match Call.target c with Direct target -> Some target | _ -> None)
  | _ -> None

let get_args ctx sub_tid =
  match Core.Map.find ctx.subs sub_tid with
  | Some (_, args) -> args
  | None ->
      let callconv = get_calling_convention ctx in
      Base.List.map
        ~f:(fun reg -> Arg.create ~intent:In reg (Var reg))
        callconv.param_regs

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

let var_size var =
  match Var.typ var with Imm n -> n | _ -> failwith "var size: non-imm var"

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

let get_local_exn ctx blk_tid var =
  let blk_vars = blk_llvals_find !(ctx.blk_llvals) blk_tid in
  let tmp = Core.Map.find !(blk_vars.locals) var in
  match tmp with
  | Some v -> v
  | None ->
      failwith @@ "Var with name " ^ Var.name var ^ " not found in block: "
      ^ Tid.name blk_tid

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

let base_exp_sub base_var sub =
  object
    inherit Exp.mapper
    method! map_var var = if Var.same var base_var then Var sub else Var var
  end

let get_bil_pass name =
  Base.List.find_exn ~f:(fun pass -> Bil.Pass.name pass = name) (Bil.passes ())

let get_pass name =
  Project.find_pass name
  |> Base.Option.value_exn ~message:("pass " ^ name ^ " not found")

let run_pass proj name =
  let pass = get_pass name in
  Project.Pass.run_exn pass proj

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
