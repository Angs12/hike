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
  set_addr_bits (Bap_core_theory.Theory.Target.data_addr_size target)

type section_image = Vsa.section_image = {
  img_lo : int64;
  img_hi : int64;
  img_bytes : Bytes.t;
  img_slots : Core.Int64.Set.t;
}

(* The per-sub written-register summary: every def whose lhs base is a
   persistent register; [Var.base] normalizes partial defs. *)
let written_regs_of_sub ~(synth : Hike_synth.table) (sub : sub term) : Var.Set.t =
  Term.enum blk_t sub
  |> Seq.concat_map ~f:(Term.enum def_t)
  |> Seq.fold ~init:Var.Set.empty ~f:(fun acc d ->
      let lhs = Def.lhs d in
      match Var.typ (Var.base lhs) with
      | Type.Imm _ when not (Hike_synth.is_temporary ~table:synth lhs) ->
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
  p_synth : Hike_synth.table;
}

type continuation = { canonical : sub term; seed : Vsa.vsa_sol }

type outcome =
  | Done of (Vsa.AI.t * Vsa.AI.t) Tid.Map.t * sub term * Tid.t Addr.Map.t * Hike_synth.table * continuation
  | Paused of paused

(* The callees the solution's reachable calls wait on, and the blocks
   of those calls.  Only a call with a continuation waits: nothing flows
   past a tail call (or the canonical return, which BAP exposes as
   one). *)
let blocked_callees ~(synth : Hike_synth.table) ~(lookup : lookup_fn)
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
          lazy (snd (Vsa.fold_block_states ~synth ~sol blk ~init:()
                       ~f:(fun _ _ _ () -> ()))) in
        Base.List.fold calls ~init:acc ~f:(fun acc c ->
            let target =
              match Call.target c with
              | Direct t -> Some t
              | Indirect e -> (
                match Vsa.denote_imm_exp ~synth e (Lazy.force post) with
                | Ok ws -> Hike_resolve.resolve_target ~lookup ws
                | Error _ -> None)
            in
            match target with
            | Some t when blocked t ->
              let callees, blocks = acc in
              (Core.Set.add callees t, Core.Set.add blocks (Term.tid blk))
            | _ -> acc))

(* Edge-dirty blocks keep their incoming state; the solve starts from
   their successors, which replay the changed terms.  The entry keeps the
   ABI seed. *)
let warm_seed ~abi ~sub ~woken sol =
  let entry = Base.Option.map (Vsa.entry_block_of sub) ~f:Term.tid in
  let initial = Vsa.init_sol ~abi sub in
  let seed = Graphlib.Std.Solution.enum sol
    |> Seq.filter ~f:(fun (b, _) ->
        Option.is_some (Term.find blk_t sub b))
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun m (b, v) -> Core.Map.set m ~key:b ~data:v) in
  let seed = match entry with
    | Some b when Core.Set.mem woken b ->
      Core.Map.set seed ~key:b ~data:(Graphlib.Std.Solution.get initial b)
    | _ -> seed in
  let seed = Graphlib.Std.Solution.create seed (Graphlib.Std.Solution.default sol) in
  (seed, woken)

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
    ~(synth : Hike_synth.table)
    ~(seed : Vsa.vsa_sol option) ~(wake : Tid.Set.t) : outcome =
  self_arm target;
  Vsa.reset_memos ();
  let abi = Hike_abi.of_target target in
  (* The images arm the whole fused solve: every denotation the
     phases, the completion's rewrites, and the replay compute reads
     them through one bracket. *)
  let synth = ref synth in
  let solve_once sub ~resolved ~init ~wake =
    Vsa.static_graph_vsa ~abi ~synth
      ~def_reads:(fun d -> Model.reads (`Def d))
      ~def_writes:(fun d -> Model.writes (`Def d))
      ~phi_reads:(fun p -> Model.reads (`Phi p))
      ~phi_writes:(fun p -> Model.writes (`Phi p))
      ~jmp_reads:(fun j ->
          Core.Set.union (Model.reads (`Jmp j)) (Model.writes (`Jmp j)))
      ~callee ~resolved ~sub_lookup:lookup ~wake
      sub init
  in
  Vsa.with_images images (fun () ->
      let rec phases (resolved : Tid.Set.t Tid.Map.t)
          (block_addrs : Tid.t Addr.Map.t)
          (init : Vsa.vsa_sol option) (wake : Tid.Set.t) =
        let seed = match init with Some s -> s | None -> Vsa.init_sol ~abi sub in
        let sol = solve_once sub ~resolved ~init:seed ~wake in
        let blocked, blocks = blocked_callees ~synth:!synth ~lookup ~callee sol sub in
        if not (Core.Set.is_empty blocked) then
          `Paused { p_sub = sub; p_resolved = resolved;
                    p_block_addrs = block_addrs; p_seed = sol;
                    p_blocked = blocked; p_wake = blocks; p_synth = !synth }
        else
          (* The return-address set is one replay of the phase's
             solution; the resolution and, on drain, the
             materialization both read it.  A phase that grows the
             edges discards it: the next phase's solution differs. *)
          let retaddr =
            Hike_cfg_complete.retaddr_defs ~abi ~synth:!synth ~sol sub
          in
          let resolved', events =
            Hike_cfg_complete.resolve_phase ~sol ~synth:!synth ~block_addrs
              ~foreign_slots ~retaddr sub resolved
          in
          if events then phases resolved' block_addrs (Some sol) Tid.Set.empty
          else `Drained (sol, block_addrs, resolved, retaddr)
      in
      (* A sub without a converged solution has no sound summary or
         body; the lift stops. *)
      try
      match phases resolved block_addrs seed wake with
      | `Paused p -> Paused p
      | `Drained (sol, block_addrs', resolved, retaddr) ->
        let continuation = { canonical = sub; seed = sol } in
        let materialized =
          Hike_cfg_complete.materialize ~sol ~synth:!synth ~retaddr
            ~block_addrs:block_addrs' ~foreign_slots sub
        in
        (* The materialization changes the edge set; the SSA follows, and
           the blocks it renamed are solved again from the warm solution
           (the others keep their variables, so their states stand). *)
        let sub', woken =
          Hike_ssa.update_sub_woken ~synth:!synth ~target ~old:sub materialized
        in
        let sol =
          if Core.Set.is_empty woken then sol
          else begin
            (* An edge-dirty block with no real successor changes no
               other block's incoming state: the terms are committed and
               the warm solution already holds every reachable state. *)
            let g = Sub.to_graph sub' in
            let reaches_successor =
              Core.Set.exists woken ~f:(fun b ->
                  Graphs.Tid.Node.succs b g |> Seq.exists ~f:(fun s ->
                      (not (Tid.equal s Graphs.Tid.start))
                      && not (Tid.equal s Graphs.Tid.exit)))
            in
            if not reaches_successor then sol
            else begin
              let seed, wake = warm_seed ~abi ~sub:sub' ~woken sol in
              let own =
                Core.Set.of_list (module Tid)
                  (Seq.to_list (Seq.map (Term.enum blk_t sub') ~f:Term.tid))
              in
              let resolved =
                Core.Map.map resolved ~f:(fun ts -> Core.Set.inter ts own)
              in
              solve_once sub' ~resolved ~init:seed ~wake
            end
          end
        in
        (* The round-down normalization rides the returned sub: the
           attribution re-denotes from these rhs's, and the solve's
           materialization may reintroduce the shift pair. *)
        let sub' = Vsa.normalize_round_with_synth ~synth sub' in
        let envs, stamped = Vsa.stamp_envs_of_sol ~synth:!synth ~sol sub' in
        let continuation = { continuation with canonical =
            Hike_ssa.retain_history ~from:stamped continuation.canonical } in
        Done (envs, stamped, block_addrs', !synth, continuation)
      with Vsa.Fixpoint_not_converged (n, _) ->
        failwith
          (Printf.sprintf "hike-vsa: sub %s: fixpoint not converged in %d iterations"
             (Sub.name sub) n))

let start (target : Theory.Target.t) ~(lookup : lookup_fn)
    ~(images : Vsa.section_image list)
    ~(callee : Tid.t -> Vsa.Call_effects.callee)
    ~(block_addrs : Tid.t Addr.Map.t) ~(synth : Hike_synth.table)
    ~(foreign_slots : Core.Int64.Set.t)
    (sub : sub term) : outcome =
  solve_phases target ~lookup ~images ~callee ~foreign_slots ~sub
    ~resolved:Tid.Map.empty ~block_addrs ~synth ~seed:None ~wake:Tid.Set.empty

let restart target ~lookup ~images ~callee ~block_addrs ~synth ~foreign_slots
    ~previous ~woken sub =
  let sol = previous.seed in
  let abi = Hike_abi.of_target target in
  let seed, wake = warm_seed ~abi ~sub ~woken sol in
  solve_phases target ~lookup ~images ~callee ~foreign_slots ~sub
    ~resolved:Tid.Map.empty ~block_addrs ~synth ~seed:(Some seed) ~wake

let resume (target : Theory.Target.t) ~(lookup : lookup_fn)
    ~(images : Vsa.section_image list)
    ~(callee : Tid.t -> Vsa.Call_effects.callee)
    ~(foreign_slots : Core.Int64.Set.t) (p : paused) : outcome =
  solve_phases target ~lookup ~images ~callee ~foreign_slots ~sub:p.p_sub
    ~resolved:p.p_resolved ~block_addrs:p.p_block_addrs ~synth:p.p_synth
    ~seed:(Some p.p_seed)
    ~wake:p.p_wake
