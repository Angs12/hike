(* The VSA: the solver and its CFG-completion loop.  The products are
   the block-boundary environments and the rewritten sub; consumers
   read them through the Hike_kb facts record. *)

open Bap.Std
open Bap_core_theory
module Vsa = Cbat_vsa
module Def_origin = Cbat_vsa.Def_origin
module Model = Hike_stack_model

let set_addr_bits (n : int) : unit = Vsa.set_addr_bits n

(* Every analysis entry self-arms the address width from the target it
   carries — no cross-pass init order exists. *)
let self_arm (target : Theory.Target.t) : unit =
  set_addr_bits (Hike_abi.addr_size_bits target)

type section_image = Vsa.section_image = {
  img_lo : int64;
  img_hi : int64;
  img_bytes : Bytes.t;
  img_slots : Core.Int64.Set.t;
}

(* The per-sub written-register summary: every def whose lhs base is a
   persistent register; [Var.base] normalizes partial defs. *)
let written_regs_of_sub (sub : sub term) : Var.Set.t =
  Term.enum blk_t sub
  |> Seq.concat_map ~f:(Term.enum def_t)
  |> Seq.fold ~init:Var.Set.empty ~f:(fun acc d ->
      let lhs = Def.lhs d in
      match Var.typ (Var.base lhs) with
      | Type.Imm _ when not (Hike_synth.is_temporary lhs) ->
        Core.Set.add acc (Var.base lhs)
      | _ -> acc)

type lookup_fn = int64 -> Tid.t option

type paused = {
  p_sub : sub term;
  p_resolved : Tid.Set.t Tid.Map.t;
  p_block_addrs : Tid.t Addr.Map.t;
  p_seed : Vsa.vsa_sol;
  p_blocked : Tid.Set.t;
  p_wake : Tid.Set.t;
}

type outcome =
  | Done of (Vsa.AI.t * Vsa.AI.t) Tid.Map.t * sub term * Tid.t Addr.Map.t
  | Paused of paused

(* The callees the solution's reachable calls wait on, and the blocks
   of those calls.  Only a call with a continuation waits: nothing flows
   past a tail call (or the canonical return, which BAP exposes as
   one). *)
let blocked_callees ~(lookup : lookup_fn)
    ~(callee : Tid.t -> Vsa.Call_effects.callee) (sol : Vsa.vsa_sol)
    (sub : sub term) : Tid.Set.t * Tid.Set.t =
  let blocked t =
    match callee t with Vsa.Call_effects.Blocked -> true | Summary _ -> false
  in
  Term.enum blk_t sub
  |> Seq.fold ~init:(Tid.Set.empty, Tid.Set.empty) ~f:(fun acc blk ->
      let calls =
        Term.enum jmp_t blk
        |> Seq.filter_map ~f:(fun j ->
            match Jmp.kind j with
            | Call c when Base.Option.is_some (Call.return c) -> Some c
            | _ -> None)
        |> Seq.to_list
      in
      if Base.List.is_empty calls
      || Vsa.AI.equal (Graphlib.Std.Solution.get sol (Term.tid blk)) Vsa.AI.bottom
      then acc
      else
        (* Only an indirect target reads the post-state; a direct
           call's block is not replayed. *)
        let post =
          lazy (snd (Vsa.fold_block_states ~sol blk ~init:()
                       ~f:(fun _ _ _ () -> ()))) in
        Base.List.fold calls ~init:acc ~f:(fun acc c ->
            let target =
              match Call.target c with
              | Direct t -> Some t
              | Indirect e -> (
                match Vsa.denote_imm_exp e (Lazy.force post) with
                | Ok ws -> Hike_resolve.resolve_target ~lookup ws
                | Error _ -> None)
            in
            match target with
            | Some t when blocked t ->
              let callees, blocks = acc in
              (Core.Set.add callees t, Core.Set.add blocks (Term.tid blk))
            | _ -> acc))

(* The fused solve: each phase runs the engine over the resolved
   extra-edge set, then the resolver grows the edges and splits
   mid-block case entries — a resolution event — and the next phase
   solves warm.  A phase whose reachable calls wait on a callee with no
   summary yet pauses instead: the phase's solution is the seed the
   resume warms from (a blocked call's continuation is bottom, so the
   seed stays below the final state).  The BIR's claims are immutable
   during the solve; at drain the materialization lands once.
   Non-convergence is not a top identity: the phases fail the lift
   with a [hike-vsa] error. *)
let solve_phases (target : Theory.Target.t) ~(lookup : lookup_fn)
    ~(images : Vsa.section_image list)
    ~(callee : Tid.t -> Vsa.Call_effects.callee)
    ~(foreign_slots : Core.Int64.Set.t) ~(sub : sub term)
    ~(resolved : Tid.Set.t Tid.Map.t) ~(block_addrs : Tid.t Addr.Map.t)
    ~(seed : Vsa.vsa_sol option) ~(wake : Tid.Set.t) : outcome =
  self_arm target;
  let abi = Hike_abi.of_target target in
  (* The images arm the whole fused solve: every denotation the
     phases, the completion's rewrites, and the replay compute reads
     them through one bracket. *)
  Vsa.with_images images (fun () ->
      let rec phases (resolved : Tid.Set.t Tid.Map.t)
          (block_addrs : Tid.t Addr.Map.t)
          (init : Vsa.vsa_sol option) (wake : Tid.Set.t) =
        let seed = match init with Some s -> s | None -> Vsa.init_sol ~abi sub in
        let sol =
          Vsa.static_graph_vsa ~abi
            ~def_reads:(fun d -> Model.reads (`Def d))
            ~def_writes:(fun d -> Model.writes (`Def d))
            ~phi_reads:(fun p -> Model.reads (`Phi p))
            ~phi_writes:(fun p -> Model.writes (`Phi p))
            ~jmp_reads:(fun j ->
                Core.Set.union (Model.reads (`Jmp j)) (Model.writes (`Jmp j)))
            ~callee ~resolved ~sub_lookup:lookup ~wake
            sub seed
        in
        let blocked, blocks = blocked_callees ~lookup ~callee sol sub in
        if not (Core.Set.is_empty blocked) then
          `Paused { p_sub = sub; p_resolved = resolved;
                    p_block_addrs = block_addrs; p_seed = sol;
                    p_blocked = blocked; p_wake = blocks }
        else
          let resolved', events =
            Hike_cfg_complete.resolve_phase ~abi ~sol ~block_addrs
              ~foreign_slots sub resolved
          in
          if events then phases resolved' block_addrs (Some sol) Tid.Set.empty
          else `Drained (sol, block_addrs)
      in
      (* A sub without a converged solution has no sound summary or
         body; the lift stops. *)
      match phases resolved block_addrs seed wake with
      | exception Vsa.Fixpoint_not_converged (n, _) ->
        failwith
          (Printf.sprintf "hike-vsa: sub %s: fixpoint not converged in %d iterations"
             (Sub.name sub) n)
      | `Paused p -> Paused p
      | `Drained (sol, block_addrs') ->
        let sub' =
          Hike_cfg_complete.materialize ~abi ~sol ~block_addrs:block_addrs'
            ~foreign_slots sub
        in
        (* The round-down normalization rides the returned sub: the
           attribution re-denotes from these rhs's, and the solve's
           materialization may reintroduce the shift pair. *)
        let sub' = Vsa.normalize_round sub' in
        let envs, stamped = Vsa.stamp_envs_of_sol ~sol sub' in
        Done (envs, stamped, block_addrs'))

let start (target : Theory.Target.t) ~(lookup : lookup_fn)
    ~(images : Vsa.section_image list)
    ~(callee : Tid.t -> Vsa.Call_effects.callee)
    ~(block_addrs : Tid.t Addr.Map.t) ~(foreign_slots : Core.Int64.Set.t)
    (sub : sub term) : outcome =
  solve_phases target ~lookup ~images ~callee ~foreign_slots ~sub
    ~resolved:Tid.Map.empty ~block_addrs ~seed:None ~wake:Tid.Set.empty

let resume (target : Theory.Target.t) ~(lookup : lookup_fn)
    ~(images : Vsa.section_image list)
    ~(callee : Tid.t -> Vsa.Call_effects.callee)
    ~(foreign_slots : Core.Int64.Set.t) (p : paused) : outcome =
  solve_phases target ~lookup ~images ~callee ~foreign_slots ~sub:p.p_sub
    ~resolved:p.p_resolved ~block_addrs:p.p_block_addrs ~seed:(Some p.p_seed)
    ~wake:p.p_wake
