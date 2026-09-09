(* Computes per-sub VSA tags via the two-channel frame-residency proof
   (spec §2.2); [vsa_info] is the only carrier of stack-access-ness. *)

open Bap.Std
open Bap_core_theory
module Vsa = Cbat_vsa

(* Forwards the address width into the VSA. *)
let set_addr_bits (n : int) : unit = Vsa.set_addr_bits n

(* Computes [sub]'s offset tags and stack plan. *)
let offsets_of_sub (target : Theory.Target.t) (sp : var) (sub : sub term) :
    Convutils.vsa_info =
  let prog' = Program.create ~subs:[ sub ] () in
  (* VLA detection runs once per sub (spec §2.3), ahead of every arm below:
     even a memory-free sub can carry a dynamic SP decrement the emitter
     must see, and the set travels in [vsa_info.vla_alloc_tids]. *)
  let alloc_tids = Vsa.Cbat_extraction.detect_dynamic_alloc sp sub in
  (* Runs the fixpoint, then extracts tags def by def. *)
    let finish (sol : Vsa.vsa_sol) : Convutils.vsa_info =
      (* Indirect jumps leave the CFG incomplete. *)
      let has_indirect_jumps =
        Term.enum blk_t sub
        |> Seq.exists ~f:(fun blk ->
            Term.enum jmp_t blk
            |> Seq.exists ~f:(fun j ->
                match Jmp.kind j with
                | Goto (Indirect _) | Ret (Indirect _) -> true
                | _ -> false))
      in
      let degraded = has_indirect_jumps in
      (* Extracts tags via [Cbat_extraction]: the per-def offset ranges. *)
      let offsets =
        Vsa.Cbat_extraction.extract
          ~sol ~alloc_tids
          ~dynamic_alloc:(fun d -> Core.Set.mem alloc_tids (Term.tid d))
          sub
      in
      (* Escape analysis: one computation per sub (ADR 0008, producer-fix).
         The result flows as [vsa_info.frame_escaped]; [regions_of_sub]
         reads it to veto conversion on escaped frames. *)
      let arg_stores =
        Vsa.Cbat_extraction.outgoing_arg_stores ~sp ~sol sub
      in
      let frame_escaped =
        Hike_stack_model.frame_escapes sp target sub ~offsets ~arg_stores
      in
      let mk = Convutils.mk_vsa_info_maps ~offsets ~degraded
          ~vla_alloc_tids:alloc_tids ~frame_escaped in
      let base_info = mk ~regions:[] ~stack_plan:[] in
      let regions = Hike_stack_model.regions_of_sub sub base_info in
      let base = mk ~regions ~stack_plan:[] in
      (* The plan IS the convertible regions — no refusals, no recomputation. *)
      { base with
    Convutils.stack_plan = Hike_stack_model.split_plan sub base }
    in
    let probe_res =
      (* Runs the fixpoint; non-convergence degrades to no tags. *)
      match
        try
          Some (Vsa.static_graph_vsa [] prog' sub (Vsa.init_sol sub))
        with Vsa.Fixpoint_not_converged (n, _, _) ->
          (* Partial solutions under-approximate; tags from them are unsound. *)
          Hike_diag.warn
            "vsa: sub %s: fixpoint not converged in %d iterations — degraded (no tags, dynamic stack)"
            (Sub.name sub) n;
          None
      with
      | None ->
        (* Degraded: every memory op is Unbounded (the sound fallback). *)
        let offsets =
          Term.enum blk_t sub
          |> Seq.concat_map ~f:(Term.enum def_t)
          |> Seq.filter ~f:(fun d ->
              Option.is_some
                (Vsa.Cbat_extraction.stack_address_of_rhs (Def.rhs d)))
          |> Seq.fold ~init:Tid.Map.empty ~f:(fun m d ->
              Core.Map.set m ~key:(Term.tid d) ~data:Convutils.Unbounded)
        in
        Convutils.{ empty_vsa_info with offsets; degraded = true;
                    vla_alloc_tids = alloc_tids }
      | Some sol -> finish sol
    in
    probe_res
