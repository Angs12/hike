(* Dead-code elimination for the hike pipeline. Replaces the lifted return epilogue (indirect noreturn call) with a var-free form, then iteratively removes defs whose lhs is never used. Memory writes and ABI registers are always kept — EXCEPT the fissioned region mem vars ([stack_rN_mem], mem-fission 2026-09-02): those survive iff some Load reads them (the load-roots rule), so never-loaded store chains (the retaddr pushes) die together in one sweep round.
   RSP erasure on the precise path uses BAP-derived SP (Abi.sp), not hardcoded strings.
   RBP is not explicitly erased; it is deleted by the fixpoint if derived from RSP (RBP:=RSP) and RSP is erased. *)

open Bap.Std
open Bap.Std.Bil.Types
open Bap_core_theory
module Abi = Hike_abi

(* ABI registers that may be read implicitly by calls (Abi is the sole origin). *)
let is_ret_reg (target : Theory.Target.t) (v : var) : bool =
  Base.List.exists (Abi.return_regs target)
    ~f:(fun r -> Var.same r (Var.base v))

let is_call_reg (target : Theory.Target.t) (v : var) : bool =
  let regs =
    Abi.param_regs target
    @ Abi.return_regs target
  in
  Base.List.exists regs ~f:(fun r -> Var.same r (Var.base v))

(* Replace an indirect noreturn call (return idiom) with a var-free target. *)
let ret_replacement (j : jmp term) : jmp term =
  match Jmp.kind j with
  | Call c -> (
      match (Call.target c, Call.return c) with
      | Indirect (Bil.Var _), None ->
          Jmp.create ~tid:(Term.tid j) ~cond:(Jmp.cond j)
            (Call
               (Call.create
                  ~target:
                    (Indirect (Bil.Unknown ("hike-dce-ret", Type.Imm 64)))
                  ()))
      | _ -> j)
  | _ -> j

(* The fissioned region mem vars ([stack_rN_mem]): recognized through the
    producer module's predicate ([Hike_stack_to_locals.is_region_mem]: the
    naming convention is that module's fact, not a grammar every consumer
    re-types). *)
let is_region_mem (v : var) : bool =
  Hike_stack_to_locals.is_region_mem v

(* The LOAD-ROOTS set: vars read as a Load's mem OPERAND, plus jmp/phi
   reads.  A fissioned var's store-to-store chains do NOT self-keep
   through it (a Store's mem-operand use is write-position, invisible
   here) — [used_of] remains the ordinary global union for everything
   else. *)

let load_roots_of (sub : sub term) : Var.Set.t =
  let roots =
    object
      inherit [Var.Set.t] Term.visitor
      method! visit_load ~mem ~addr:_ _ _ acc =
        Core.Set.union acc (Exp.free_vars mem)
      (* jmps / phis read vars as a whole — count them (they cannot
         appear as a bare mem read per BNF1, but counting is sound). *)
      method! visit_jmp j acc = Core.Set.union acc (Jmp.free_vars j)
      method! visit_phi p acc = Core.Set.union acc (Phi.free_vars p)
    end
  in
  roots#visit_sub sub Var.Set.empty

(* Vars referenced by any def, jmp, or phi in the sub. *)
let used_of (sub : sub term) : Var.Set.t =
  let v =
    object
      inherit [Var.Set.t] Term.visitor
      method! visit_def d used = Core.Set.union used (Def.free_vars d)
      method! visit_jmp j used = Core.Set.union used (Jmp.free_vars j)
      method! visit_phi p used = Core.Set.union used (Phi.free_vars p)
    end
  in
  v#visit_sub sub Var.Set.empty

(* FP intrinsic interface vars ([intrinsic:xN] / [intrinsic:yN]). *)
let is_intrinsic_var (v : var) : bool =
  Base.String.is_prefix (Var.name (Var.base v)) ~prefix:"intrinsic:"

let is_hike_stack (v : var) : bool = Var.same v Convutils.hike_stack_var

let is_sp (target : Theory.Target.t) (v : var) : bool =
  Var.same v (Abi.sp target)

let rec sp_value_exp (target : Theory.Target.t) (e : exp) : bool =
  match e with
  | Bil.Var v -> is_sp target v
  | Bil.BinOp (_, a, b) -> sp_value_exp target a || sp_value_exp target b
  | Bil.UnOp (_, a) -> sp_value_exp target a
  | Bil.Cast (_, _, a) -> sp_value_exp target a
  | Bil.Extract (_, _, a) -> sp_value_exp target a
  | Bil.Concat (a, b) -> sp_value_exp target a || sp_value_exp target b
  | Bil.Let (_, a, b) -> sp_value_exp target a || sp_value_exp target b
  | Bil.Ite (c, a, b) -> sp_value_exp target c || sp_value_exp target a || sp_value_exp target b
  | _ -> false

let is_sp_value_def (target : Theory.Target.t) (d : def term) : bool =
  not (Convutils.is_mem (Def.lhs d))
  && not (is_sp target (Var.base (Def.lhs d)))
  && sp_value_exp target (Def.rhs d)

let is_sp_for_erasure (target : Theory.Target.t) (d : def term) : bool =
  is_sp target (Def.lhs d)

(* Precise predicate for RSP erasure (ADR 0001 Q1/A, Q2): the sub uses the
   SPLIT stack model (per-region [stack_rN] allocas) — its SP/hike_stack
   defs are dead.

   Finding 1: the decision is READ from [Convutils.stack_plan], the single
   result [Hike_stack_to_locals.split_plan] produced in the vsa pass. This
   pass is a CONSUMER — it no longer imports the emitter's
   [region_split_plan] to re-derive a BIL-level fact. *)
let is_precise_sub (_target : Theory.Target.t) (sub : sub term) : bool =
  match Core.Map.find (Hike_kb.vsa_info ()) (Term.tid sub) with
  | None -> false
  | Some info -> Hike_stack_to_locals.is_precise info

(* The TWO-TIER keep: a region mem var's def survives iff the var has
   a load-root; the lifter's [mem] keeps the unconditional is_mem keep
   (ABI/external/outgoing traffic — the sub-local used-set cannot see
   the callee's reads).  [load_roots] is threaded by [sweep_fixpoint],
   recomputed per round (a removed load can un-root a chain). *)
let keep ?(precise=false) ?(load_roots=Var.Set.empty)
    ~target (d : def term) (used : Var.Set.t) : bool =
  if precise && (is_sp_for_erasure target d || is_hike_stack (Def.lhs d) || is_sp_value_def target d) then false
  else
    let lhs = Def.lhs d in
    if is_region_mem lhs then
      Core.Set.mem load_roots lhs
      (* a fissioned store with no loads from its var: DEAD — the whole
         chain (store-to-store rewrites) dies together in one sweep
         round; the fixpoint loop re-runs to stability. *)
    else
      Core.Set.mem used lhs || is_ret_reg target lhs || Convutils.is_mem lhs
      || is_call_reg target lhs || is_intrinsic_var lhs

let def_count (sub : sub term) : int =
  Term.enum blk_t sub
  |> Seq.fold ~init:0 ~f:(fun n blk ->
      n + Seq.length (Term.enum def_t blk))

(* Iteratively remove unused defs until fixpoint. For precise subs, SP/hike_stack/sp_value are dead (Q2, Q5). *)
let rec sweep_fixpoint ~target (sub : sub term) : sub term =
  let precise = is_precise_sub target sub in
  let used = used_of sub in
  (* MEM-FISSION: the load-roots set (recomputed per round — a removed
     load can un-root a chain, and the fixpoint handles the cascade). *)
  let load_roots = load_roots_of sub in
  let sub' =
    Term.map blk_t sub ~f:(fun blk ->
        Term.filter def_t blk ~f:(fun d ->
            keep ~precise ~load_roots ~target d used))
  in
  if def_count sub' = def_count sub then sub' else sweep_fixpoint ~target sub'

(* Run DCE: rewrite return calls, then sweep unused defs. Intrinsics are left unchanged. *)
let dce ~target (sub : sub term) : sub term =
  if Term.has_attr sub Sub.intrinsic then sub
  else
    let mapper =
      object
        inherit Term.mapper
        method! map_jmp j = ret_replacement j
      end
    in
    mapper#map_sub sub |> sweep_fixpoint ~target
