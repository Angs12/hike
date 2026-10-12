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

let kill_summaries ~(abi : Hike_abi.t) (prog : program term) :
    Core.Int.Set.t option Tid.Map.t =
  let subs = Hike_stack_model.sub_map prog in
  let reads_retaddr (rhs : exp) : bool =
    Base.Option.value_map (Model.addr_of_rhs rhs) ~default:false
      ~f:(fun (addr, _) -> Model.is_return_address_shape ~abi addr)
  in
  (* The sub's call sites: a lifted direct callee, a kill-all site (an
     indirect target, trap, or extern), or no site (the return epilogue
     is no mark at all). *)
  let sites (s : sub term) : Tid.t list * bool =
    Term.enum blk_t s
    |> Seq.concat_map ~f:(fun blk ->
        let last =
          Core.Map.fold (Vsa.last_defs blk) ~init:Var.Map.empty
            ~f:(fun ~key ~data acc ->
                Core.Map.set acc ~key:(Var.base key)
                  ~data:(Def.rhs data))
        in
        Term.enum jmp_t blk
        |> Seq.filter_map ~f:(fun j ->
            match Jmp.kind j with
            | Int _ -> Some `Kill
            | Call c when not (Hike_return.is_jmp j) -> (
                match Call.target c with
                | Indirect (Bil.Var v)
                | Indirect (Bil.Cast (_, _, Bil.Var v))
                  when Base.Option.is_none (Call.return c) -> (
                    match Core.Map.find last (Var.base v) with
                    | Some rhs when reads_retaddr rhs -> None
                    | _ -> Some `Kill)
                | Indirect _ -> Some `Kill
                | Direct t ->
                  if Core.Map.mem subs t then Some (`Call t) else Some `Kill)
            | _ -> None))
    |> Seq.fold ~init:([], false) ~f:(fun (edges, kill) site ->
        match site with
        | `Kill -> (edges, true)
        | `Call c -> (c :: edges, kill))
  in
  (* The may-write summary is the least fixpoint of
     [direct(s) ∪ ⋃ callees' summaries] over the direct-call graph; a
     cycle unions its members instead of killing the whole component.
     A kill-all site or a kill-all callee makes its callers kill-all. *)
  let written = ref Tid.Map.empty in
  let kill = ref Tid.Set.empty in
  let callers = ref Tid.Map.empty in
  Term.enum sub_t prog
  |> Seq.iter ~f:(fun s ->
      let stid = Term.tid s in
      let edges, own_kill = sites s in
      written := Core.Map.set !written ~key:stid ~data:(written_regs_of_sub s);
      if own_kill then kill := Core.Set.add !kill stid;
      Base.List.iter edges ~f:(fun c ->
          callers := Core.Map.add_multi !callers ~key:c ~data:stid));
  let work = ref (Core.Set.of_list (module Tid) (Core.Map.keys !written)) in
  while not (Core.Set.is_empty !work) do
    let t = Core.Set.choose_exn !work in
    work := Core.Set.remove !work t;
    Base.List.iter
      (Base.Option.value (Core.Map.find !callers t) ~default:[])
      ~f:(fun p ->
        if not (Core.Set.mem !kill p) then begin
          let changed =
            if Core.Set.mem !kill t then begin
              kill := Core.Set.add !kill p;
              true
            end
            else
              match Core.Map.find !written t with
              | None -> false
              | Some ws ->
                let before =
                  Base.Option.value (Core.Map.find !written p)
                    ~default:Var.Set.empty in
                let after = Core.Set.union before ws in
                if Core.Set.equal before after then false
                else begin
                  written := Core.Map.set !written ~key:p ~data:after;
                  true
                end
          in
          if changed then work := Core.Set.add !work p
        end)
  done;
  Term.enum sub_t prog
  |> Seq.fold ~init:Tid.Map.empty ~f:(fun m s ->
      let stid = Term.tid s in
      let v =
        if Core.Set.mem !kill stid then None
        else
          Some
            (Cbat_var_id.intern_set
               (Base.Option.value (Core.Map.find !written stid)
                  ~default:Var.Set.empty))
      in
      Core.Map.set m ~key:stid ~data:v)

(* One computation per program, at the pass_vsa boundary; the fixpoint
   consumes the summaries per phase. *)

(* The fused solve: each phase runs the engine over the resolved
   extra-edge set, then the resolver grows the edges and splits
   mid-block case entries — a resolution event — and the next phase
   solves warm.  A phase whose reachable calls wait on a callee with no
   summary yet pauses instead: the phase's solution is the seed the
   resume warms from (a blocked call's continuation is bottom, so the
   seed stays below the final state).  The BIR's claims are immutable
   during the solve; at drain the materialization lands once.
   Non-convergence is the top identity: empty environments, the
   shape-canonicalized sub, the input block-address map. *)
type lookup_fn = int64 -> Tid.t option

type paused = {
  p_sub : sub term;
  p_resolved : Tid.Set.t Tid.Map.t;
  p_block_addrs : Tid.t Addr.Map.t;
  p_seed : Vsa.vsa_sol;
  p_blocked : Tid.Set.t;
}

type outcome =
  | Done of (Vsa.AI.t * Vsa.AI.t) Tid.Map.t * sub term * Tid.t Addr.Map.t
  | Paused of paused

(* The callees the solution's reachable calls wait on.  Only a call
   with a continuation waits: nothing flows past a tail call (or the
   canonical return, which BAP exposes as one). *)
let blocked_callees ~(lookup : lookup_fn)
    ~(callee : Tid.t -> Vsa.Call_effects.callee) (sol : Vsa.vsa_sol)
    (sub : sub term) : Tid.Set.t =
  let blocked t =
    match callee t with Vsa.Call_effects.Blocked -> true | Summary _ -> false
  in
  Term.enum blk_t sub
  |> Seq.fold ~init:Tid.Set.empty ~f:(fun acc blk ->
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
        let _, post = Vsa.fold_block_states ~sol blk ~init:() ~f:(fun _ _ _ () -> ()) in
        Base.List.fold calls ~init:acc ~f:(fun acc c ->
            let target =
              match Call.target c with
              | Direct t -> Some t
              | Indirect e -> (
                match Vsa.denote_imm_exp e post with
                | Ok ws -> Hike_resolve.resolve_target ~lookup ws
                | Error _ -> None)
            in
            match target with
            | Some t when blocked t -> Core.Set.add acc t
            | _ -> acc))

let solve_phases (target : Theory.Target.t) ~(lookup : lookup_fn)
    ~(images : Vsa.section_image list)
    ~(callee : Tid.t -> Vsa.Call_effects.callee)
    ~(foreign_slots : Core.Int64.Set.t) ~(sub : sub term)
    ~(resolved : Tid.Set.t Tid.Map.t) ~(block_addrs : Tid.t Addr.Map.t)
    ~(seed : Vsa.vsa_sol option) : outcome =
  self_arm target;
  let abi = Hike_abi.of_target target in
  (* The images arm the whole fused solve: every denotation the
     phases, the completion's rewrites, and the replay compute reads
     them through one bracket. *)
  Vsa.with_images images (fun () ->
      let rec phases (resolved : Tid.Set.t Tid.Map.t)
          (block_addrs : Tid.t Addr.Map.t)
          (init : Vsa.vsa_sol option) =
        let seed = match init with Some s -> s | None -> Vsa.init_sol ~abi sub in
        let sol =
          Vsa.static_graph_vsa ~abi
            ~def_reads:Model.def_reads ~def_writes:Model.def_writes
            ~phi_reads:Model.phi_reads ~phi_writes:Model.phi_writes
            ~jmp_reads:(Model.jmp_reads ~abi)
            ~callee ~resolved ~sub_lookup:lookup
            sub seed
        in
        let blocked = blocked_callees ~lookup ~callee sol sub in
        if not (Core.Set.is_empty blocked) then
          `Paused { p_sub = sub; p_resolved = resolved;
                    p_block_addrs = block_addrs; p_seed = sol;
                    p_blocked = blocked }
        else
          let resolved', events =
            Hike_cfg_complete.resolve_phase ~abi ~sol ~block_addrs
              ~foreign_slots sub resolved
          in
          if events then phases resolved' block_addrs (Some sol)
          else `Drained (sol, block_addrs)
      in
      match
        try Some (phases resolved block_addrs seed)
        with Vsa.Fixpoint_not_converged (n, _) ->
#ifdef VSA_DEBUG
          Vsa.Cbat_attr_census.bump "backstop.sub";
#endif
          Hike_diag.warn
            "vsa: sub %s: fixpoint not converged in %d iterations — shape return canonicalization only (every other reader takes the top identity)"
            (Sub.name sub) n;
          None
      with
      | Some (`Paused p) -> Paused p
      | Some (`Drained (sol, block_addrs')) ->
        let sub' =
          Hike_cfg_complete.materialize ~abi ~sol ~block_addrs:block_addrs'
            ~foreign_slots sub
        in
        (* The round-down normalization rides the returned sub: the
           attribution re-denotes from these rhs's, and the solve's
           materialization may reintroduce the shift pair. *)
        let sub' = Vsa.normalize_round sub' in
        let envs, stamped = Vsa.stamp_envs_of_sol ~sol sub' in
        Done (envs, stamped, block_addrs')
      | None ->
        Done
          ( Tid.Map.empty,
            Hike_cfg_complete.canonicalize_shape_returns ~abi sub,
            block_addrs ))

let start (target : Theory.Target.t) ~(lookup : lookup_fn)
    ~(images : Vsa.section_image list)
    ~(callee : Tid.t -> Vsa.Call_effects.callee)
    ~(block_addrs : Tid.t Addr.Map.t) ~(foreign_slots : Core.Int64.Set.t)
    ?(noreturn : Tid.Set.t = Tid.Set.empty) (sub : sub term) : outcome =
  let sub = Hike_cfg_complete.clear_noreturn_returns ~noreturn sub in
  solve_phases target ~lookup ~images ~callee ~foreign_slots ~sub
    ~resolved:Tid.Map.empty ~block_addrs ~seed:None

let resume (target : Theory.Target.t) ~(lookup : lookup_fn)
    ~(images : Vsa.section_image list)
    ~(callee : Tid.t -> Vsa.Call_effects.callee)
    ~(foreign_slots : Core.Int64.Set.t) (p : paused) : outcome =
  solve_phases target ~lookup ~images ~callee ~foreign_slots ~sub:p.p_sub
    ~resolved:p.p_resolved ~block_addrs:p.p_block_addrs ~seed:(Some p.p_seed)

(* The kill-summary map never blocks, so the solve runs to the end. *)
let fixpoint (target : Theory.Target.t)
    ~(lookup : lookup_fn)
    ~(sub_addrs : Tid.t Addr.Map.t)
    ~(images : Vsa.section_image list)
    ~(written : Core.Int.Set.t option Tid.Map.t)
    ~(block_addrs : Tid.t Addr.Map.t)
    ~(foreign_slots : Core.Int64.Set.t)
    ?(noreturn : Tid.Set.t = Tid.Set.empty)
    (sub : sub term) :
    (Vsa.AI.t * Vsa.AI.t) Tid.Map.t * sub term * Tid.t Addr.Map.t =
  match
    start target ~lookup ~images
      ~callee:(Vsa.Call_effects.callee_of_written written)
      ~block_addrs ~foreign_slots ~noreturn sub
  with
  | Done (envs, sub, block_addrs) -> (envs, sub, block_addrs)
  | Paused _ -> assert false
