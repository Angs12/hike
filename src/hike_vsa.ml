(* Src/hike_vsa.ml — the VSA tag-EXTRACTION module of the hike library. *)

open Bap.Std
open Bap_core_theory
module KB = Bap_knowledge.Knowledge

module AI = Cbat_vsa.AI
module Mem = Cbat_vsa.Mem
module Vsa = Cbat_vsa
module Ws = Cbat_clp_set_composite

(* [set_addr_bits n]: Forward the program architecture's address size in bits (the Target-derived [Abi.addr_size_bits]) into the VSA — the memmap's native key width (O1). *)
let set_addr_bits (n : int) : unit = Vsa.set_addr_bits n

(* the RSP identity var for the k-range computation is the TARGET's stack pointer ([Abi.sp]) — threaded in as the [sp] argument of [offsets_of_sub] (R2: no [target_ref] global; the caller derives it from [Project.target] once and passes it down). *)
(* sibling inside the hike library — reference DIRECTLY by plain name (the
   [Hike.Relevance] alias in hike.ml/hike.mli is the library's public seam for
   OUTSIDE consumers; inside, plain names are the one form that resolves
   under both dune (wrapped) and bapbuild (flat). *)
module Relevance = Hike_vsa_relevance

(* ARCH-1 — [classify]/[bounds_of]/[k_range_of] are DELETED here:
   the ONE home is [Cbat_vsa.Cbat_extraction] (the extraction
   submodule; the pass layer reaches it through [Vsa.Cbat_extraction]
   — the probe's copy routes through the same [extract] call). *)

(* [has_relevant_tags sub]: Does ANY def of [sub] carry the [relevant] or [stack_access] tag? *)
let has_relevant_tags (sub : sub term) : bool =
  Term.enum blk_t sub
  |> Seq.exists ~f:(fun b ->
      Term.enum def_t b
      |> Seq.exists ~f:(fun d ->
          Term.has_attr d Cbat_vsa_utils.relevant
          || Term.has_attr d Relevance.stack_access))

(* [has_stack_access_tags sub]: Does ANY def of [sub] carry the [stack_access] tag (an actual direct SP-relative stack access)? *)
let has_stack_access_tags (sub : sub term) : bool =
  Term.enum blk_t sub
  |> Seq.exists ~f:(fun b ->
      Term.enum def_t b
      |> Seq.exists ~f:(fun d -> Term.has_attr d Relevance.stack_access))


(* [offsets_of_sub target sp sub]: The per-def offset interval tags of [sub]'s Load/Store defs, in block-then-def order (see the header contract), PLUS the sub's STACK MODEL DECISION ([Convutils.stack_plan] — the per-region split or the single-frame fallback).

   [target] is threaded in so the stack model's SP/FP derivation comes from [Abi] (AGENTS.md Principle 8 — never hardcode a register name); [sp] is [Abi.sp target]. *)
let offsets_of_sub (target : Theory.Target.t) (sp : var) (sub : sub term) :
    Convutils.vsa_info =
  let sub' = if has_relevant_tags sub then sub else Relevance.analyze sp sub in
  (* A sub with NO direct-SP stack accesses produces an empty offset set regardless of the fixpoint result (only [stack_access]-tagged Load/Store defs yield offset tags). *)
  if not (has_stack_access_tags sub') then
    Convutils.empty_vsa_info
  else
  let prog' = Program.create ~subs:[ sub' ] () in
  (* The single-pass trace-partitioning (docs/trace-partitioning-plan.md §2/§7 — ticket 01): the
     forward fixpoint is branch-sensitive END-TO-END (the deep walk runs INLINE at every
     out-edge, driven by the ACCUMULATED [Graphs.Ir.Edge.cond]), so the per-block TAG state IS
     the block's IN-state in the converged solution — the Phase B post-pass is deleted
     (ticket 02: the view machinery is gone from the library; the solution-only
     [static_graph_vsa] is THE entry point).  The per-def walk (finish): the sequential
     state (the
     block input [st], advanced def-by-def exactly like the fixpoint's [denote_defs]) and the
     two tag accumulators thread through ONE nested fold — no refs. *)
  let finish (sol : Vsa.vsa_sol) : Convutils.vsa_info =
  (* A sub with an INDIRECT JUMP ([Goto/Ret (Indirect _)]) has an INCOMPLETE CFG — the lifter could not resolve the jump-table targets — so a bottom block state does NOT prove unreachability (the target blocks are stranded, their accesses would be mislabeled dead-path). *)
  let has_indirect_jumps =
    Term.enum blk_t sub'
    |> Seq.exists ~f:(fun blk ->
        Term.enum jmp_t blk
        |> Seq.exists ~f:(fun j ->
            match Jmp.kind j with
            | Goto (Indirect _) | Ret (Indirect _) -> true
            | _ -> false))
  in
  let degraded = has_indirect_jumps in
  (* ARCH-1 — THE EXTRACTION IS THE CBAT_VSA MODULE'S ([Cbat_extraction]):
     the M6 classification walk, the kind/k-range arithmetic, the
     set-overlap merge, and the VLA idiom matcher — ONE home, the probe's
     copy routed through the same [extract].  This [finish] is the
     COMPOSITION only: the fixpoint's solution in, the record out, plus
     the stack-model calls below. *)
  let offsets, k_ranges, vla_bounds =
    Vsa.Cbat_extraction.extract
      ~sp ~sol
      ~stack_access:(fun d -> Term.has_attr d Relevance.stack_access)
      ~dynamic_alloc:(fun d -> Term.has_attr d Relevance.dynamic_alloc)
      sub'
  in
  let mk = Convutils.mk_vsa_info_maps ~offsets ~k_ranges ~degraded in
  let base_info = mk ~regions:[] ~vla_bounds ~stack_plan:[] in
  (* The ESCAPE verdict — computed ONCE per sub and shared by the
     region convertibility rule and (through it) the plan. *)
  let frame_escaped = Hike_stack_model.frame_escapes sp target sub' in
  let regions =
    Hike_stack_model.regions_of_sub sp target sub' base_info ~frame_escaped
  in
  let base = mk ~regions ~vla_bounds ~stack_plan:[] in
  (* THE STACK MODEL DECISION — computed ONCE, here, on the PRE-rewrite
     sub (Finding 1): [Hike_stack_model.split_plan] is its single
     producer; the stack-to-locals rewrite, dce and the emitter are its
     consumers (they read [info.stack_plan]). *)
  { base with Convutils.stack_plan = Hike_stack_model.split_plan sp target sub' base }
  in
  let probe_res =
  (* the solve driver: run the fixpoint; a non-convergent fixpoint (D.1) degrades the sub soundly — no tags, every stack access stays real memory (the emitter's dynamic path). *)
  match
    try
      Some (Vsa.static_graph_vsa [] prog' sub' (Vsa.init_sol sub'))
    with Vsa.Fixpoint_not_converged (n, _, _) ->
      (* The fixpoint did not converge — the partial solution is an UNDER-APPROXIMATION; narrow offset tags computed from it would exclude reachable values (unsound). *)
      Hike_diag.warn
        "vsa: sub %s: fixpoint not converged in %d iterations — degraded (no tags, dynamic stack)"
        (Sub.name sub') n;
      None
  with
  | None ->
      let offsets =
        Term.enum blk_t sub'
        |> Seq.concat_map ~f:(Term.enum def_t)
        |> Seq.filter ~f:(fun d -> Term.has_attr d Relevance.stack_access)
        |> Seq.fold ~init:Tid.Map.empty ~f:(fun m d ->
               Core.Map.set m ~key:(Term.tid d) ~data:Convutils.Unbounded) in
      Convutils.{ empty_vsa_info with offsets; degraded = true }
  | Some sol -> finish sol
  in
  (* 100% VSA Tagging Assertion: Every stack_access def MUST be present in info.offsets *)
  let tagged_tids = probe_res.Convutils.offsets |> Core.Map.keys |> Tid.Set.of_list in
  (* The 100% VSA TAGGING INVARIANT CHECK (PARKED 2026-09-01 by the user:
     "That is a later fix, not now" — the assert crashed the big-binary
     conversions; see the ticket
     .scratch/100-invariant-gaps/01-diagnose-and-fix.md): neutralized to a
     WARNED gap that enumerates the violating sub+def so the conversions
     complete soundly (non-seeding is the raw-memory fallback; no unsound
     conversion happens). Restoring the hard invariant is the ticket's
     first step. *)
  Term.enum blk_t sub'
  |> Seq.iter ~f:(fun blk ->
      Term.enum def_t blk
      |> Seq.iter ~f:(fun d ->
          if Term.has_attr d Relevance.stack_access
             && not (Core.Set.mem tagged_tids (Term.tid d)) then
            Hike_diag.warn "100%%-invariant gap (PARKED): sub %s def %s untagged"
              (Sub.name sub') (Tid.to_string (Term.tid d))));
  probe_res

(* M2: arity_of_sub and arity_map_of_prog removed — no stack-arg arity, M2 hike_stack ptr only. *)
