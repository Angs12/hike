(* Emitter environment: the emission run's value ctx, the per-sub
   scope, LLtype helpers, the WVar/blk-llvals machinery, signature and
   label helpers, name minting. *)

open Bap.Std
open Bap.Std.Bil.Types
open Bap_core_theory
module Abi = Hike_abi

module EHashtbl = Core.Hashtbl

(* The edge bridge: per BIR edge (pred -> target), the basic block
   holding the edge's terminator and the edge's SP-restore value.
   One table per sub scope; phis read it after rendering completes. *)
module Edge_tbl = struct
  type row = { term_bb : Llvm.llbasicblock; sp_restore : Llvm.llvalue option }

  type t = (Tid.t, (Tid.t, row) EHashtbl.t) EHashtbl.t

  let empty () : t = EHashtbl.create (module Tid)

  (* Merges into any existing row: the render paths write different
     fields of one row. *)
  let set (t : t) ~(pred : Tid.t) ~(target : Tid.t)
      ?term_bb ?sp_restore () : unit =
    let inner =
      match EHashtbl.find t pred with
      | Some h -> h
      | None ->
        let h = EHashtbl.create (module Tid) in
        EHashtbl.set t ~key:pred ~data:h;
        h
    in
    let existing = EHashtbl.find inner target in
    let row =
      match existing with
      | Some r ->
        { term_bb = Option.value term_bb ~default:r.term_bb;
          sp_restore = Base.Option.first_some sp_restore r.sp_restore }
      | None ->
        { term_bb = (match term_bb with Some bb -> bb | None -> failwith "Edge_tbl.set: a new row needs a term_bb");
          sp_restore = sp_restore }
    in
    EHashtbl.set inner ~key:target ~data:row

  let find (t : t) ~(pred : Tid.t) ~(target : Tid.t) : row option =
    match EHashtbl.find t pred with
    | Some h -> EHashtbl.find h target
    | None -> None
end

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
type section_type = DATA | RODATA | BSS | GOT | GOTPLT | RODATA_REL | TEXT

let section_type_to_string = function
  | DATA -> "data"
  | RODATA -> "rodata"
  | BSS -> "bss"
  | GOT -> "got"
  | GOTPLT -> "got.plt"
  | RODATA_REL -> "data.rel.ro"
  | TEXT -> "text"

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
  section_remap : (int64 * int64 * Llvm.llvalue * sec_owner list) list;
  copy_relocs : int64 list;
  target : Theory.Target.t;
  (* ABI projection of [target], static per binary. *)
  abi : Abi.t;
  sp : var;
  ptrsize : int;
  subs : (Arg.t list * Arg.t list) Tid.Map.t;
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
  sec_comps : (Var.t * (Llvm.llvalue * int64)) list ref;
}

(* The sub-emission scope: every per-sub emission state.  [emit_program]'s
   body loop opens one per sub and drops it at the boundary — nothing
   here survives the sub that created it, so no field needs a clear. *)
type sub_scope = {
  ll_bbs : Llvm.llbasicblock Tid.Map.t ref;
  blk_llvals : blk_llvals Tid.Map.t ref;
  (* One Dead-classification warn per sub. *)
  dead_warned : Tid.Set.t ref;
  (* Dedups [hike: undef-read:] warnings per (sub, var). *)
  undef_warned : Var.Set.t ref Tid.Map.t ref;
  (* The body's frame: routes region/window mem vars; bound around
     body emission. *)
  cur_frame : sub_frame option ref;
  (* The edge bridge: fresh per scope. *)
  edge_tbl : Edge_tbl.t ref;
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
    edge_tbl = ref (Edge_tbl.empty ());
    undef_vals = ref WVarMap.empty }

let typ_lltype ctx typ =
  match typ with
  | Imm n -> Llvm.integer_type ctx.llvm_ctx n
  | _ -> Llvm.pointer_type ctx.llvm_ctx

let var_lltype ctx var = typ_lltype ctx (Var.typ var)

(* Coerces an integer value of known width to a lane width. *)
let coerce_int_width llvm_ctx llvm_builder ~bits v w =
  if bits = w then v
  else if bits > w then
    Llvm.build_trunc v (Llvm.integer_type llvm_ctx w) "" llvm_builder
  else Llvm.build_zext v (Llvm.integer_type llvm_ctx w) "" llvm_builder

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

(* The synthetic indirect-call convention: every register lane plus
   the caller-window base — exactly what a pointer call passes and a
   thunk accepts. *)
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
  scope.blk_llvals :=
    Core.Map.add_exn !(scope.blk_llvals) ~key:blk_tid ~data:{ phis; locals }

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
  blk_llvals.locals := WVarMap.add (wvar_of var) value !(blk_llvals.locals)

let get_local scope blk_tid var =
  let blk_vars = blk_llvals_find !(scope.blk_llvals) blk_tid in
  WVarMap.find_opt (wvar_of var) !(blk_vars.locals)

(* Finds [v]'s binding at another width. *)
let probe_local_family scope blk_tid (v : Var.t) ~(want_w : int) :
    (Llvm.llvalue * int) option =
  let blk_vars = blk_llvals_find !(scope.blk_llvals) blk_tid in
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
  let trap = Llvm.declare_function trap_name trap_ty ctx.llvm_module in
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
