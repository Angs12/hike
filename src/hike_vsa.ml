(* Computes per-sub VSA tags. *)

open Bap.Std
open Bap_core_theory
module KB = Bap_knowledge.Knowledge

module AI = Cbat_vsa.AI
module Mem = Cbat_vsa.Mem
module Vsa = Cbat_vsa
module Ws = Cbat_clp_set_composite

(* Forwards the address width into the VSA. *)
let set_addr_bits (n : int) : unit = Vsa.set_addr_bits n



module Relevance = Hike_vsa_relevance



(* Tests for any relevance tag. *)
let has_relevant_tags (sub : sub term) : bool =
  Term.enum blk_t sub
  |> Seq.exists ~f:(fun b ->
      Term.enum def_t b
      |> Seq.exists ~f:(fun d ->
          Term.has_attr d Cbat_vsa_utils.relevant
          || Term.has_attr d Relevance.stack_access))

(* Tests for any stack access tag. *)
let has_stack_access_tags (sub : sub term) : bool =
  Term.enum blk_t sub
  |> Seq.exists ~f:(fun b ->
      Term.enum def_t b
      |> Seq.exists ~f:(fun d -> Term.has_attr d Relevance.stack_access))


(* Computes [sub]'s offset tags and stack plan. *)
let offsets_of_sub (target : Theory.Target.t) (sp : var) (sub : sub term) :
    Convutils.vsa_info =
  let sub' = if has_relevant_tags sub then sub else Relevance.analyze sp sub in
  (* Subs without stack accesses yield no tags. *)
  if not (has_stack_access_tags sub') then
    Convutils.empty_vsa_info
  else
  let prog' = Program.create ~subs:[ sub' ] () in
  (* Runs the fixpoint, then extracts tags def by def. *)
  let finish (sol : Vsa.vsa_sol) : Convutils.vsa_info =
  (* Indirect jumps leave the CFG incomplete. *)
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
  (* Extracts tags via [Cbat_extraction]. *)
  let offsets, k_ranges, vla_bounds =
    Vsa.Cbat_extraction.extract
      ~sp ~sol
      ~stack_access:(fun d -> Term.has_attr d Relevance.stack_access)
      ~dynamic_alloc:(fun d -> Term.has_attr d Relevance.dynamic_alloc)
      sub'
  in
  let mk = Convutils.mk_vsa_info_maps ~offsets ~k_ranges ~degraded in
  let base_info = mk ~regions:[] ~vla_bounds ~stack_plan:[] in
  (* Escape verdict shared by regions and plan. *)
  let frame_escaped = Hike_stack_model.frame_escapes sp target sub' in
  let regions =
    Hike_stack_model.regions_of_sub sp target sub' base_info ~frame_escaped
  in
  let base = mk ~regions ~vla_bounds ~stack_plan:[] in
  (* Computes the stack plan on the pre-rewrite sub. *)
  { base with Convutils.stack_plan = Hike_stack_model.split_plan sp target sub' base }
  in
  let probe_res =
  (* Runs the fixpoint; non-convergence degrades to no tags. *)
  match
    try
      Some (Vsa.static_graph_vsa [] prog' sub' (Vsa.init_sol sub'))
    with Vsa.Fixpoint_not_converged (n, _, _) ->
      (* Partial solutions under-approximate; tags from them are unsound. *)
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
  (* Every stack access must appear in [offsets]. *)
  let tagged_tids = probe_res.Convutils.offsets |> Core.Map.keys |> Tid.Set.of_list in
  (* Warns on untagged stack accesses. *)
  Term.enum blk_t sub'
  |> Seq.iter ~f:(fun blk ->
      Term.enum def_t blk
      |> Seq.iter ~f:(fun d ->
          if Term.has_attr d Relevance.stack_access
             && not (Core.Set.mem tagged_tids (Term.tid d)) then
            Hike_diag.warn "100%%-invariant gap (PARKED): sub %s def %s untagged"
              (Sub.name sub') (Tid.to_string (Term.tid d))));
  probe_res


