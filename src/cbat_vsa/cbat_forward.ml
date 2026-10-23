(* Forward jump/block denotation: the per-jmp transfer toward a target
   (the direct/resolved identity, the call abstraction), joined over the
   reachable jumps; each conditional edge drives the backward
   refinement inline. *)

include Core
open Bap.Std
open Graphlib.Std
module AI = Cbat_ai_representation
module WordSet = Cbat_clp_set_composite
open Cbat_transfer

(* The edge classification: whether a jump's transfer reaches the
   denotation target.  [Exact ts] — iff the transfer's target is in
   [ts]; [Any] — may continue anywhere.  The plan types live in
   [Cbat_runctx] so the canonical context owns its plan cache. *)
type edge_rel = Cbat_runctx.edge_rel = Exact of Tid.Set.t | Any

let edge_rel_of ~(resolved : Tid.Set.t Tid.Map.t) (jmp : jmp term) : edge_rel =
  match Jmp.kind jmp with
  | Goto (Direct tid) | Ret (Direct tid) -> Exact (Tid.Set.singleton tid)
  | Call c ->
    (match Core.Map.find resolved (Term.tid jmp) with
     | Some tids ->
       Exact
         (match Call.return c with
          | Some (Direct t) -> Core.Set.add tids t
          | Some (Indirect _) | None -> tids)
     | None ->
       (match Call.return c with
        | Some (Direct t) -> Exact (Tid.Set.singleton t)
        | Some (Indirect _) | None -> Any))
  | Goto (Indirect _) | Ret (Indirect _) | Int _ -> Any

(* The env projection: the edge delivers its state to the target. *)
let env_leads ~(target : tid) (rel : edge_rel) : bool =
  match rel with
  | Exact ts -> Core.Set.mem ts target
  | Any -> true

(* The walk projection: whether the edge's own refinement is discarded.
   NOT the env projection — on a noreturn call the walk RUNS (its
   empty-meet landmark observations persist) while the env result is
   bottom. *)
let walk_discards ~(target : tid) (rel : edge_rel) : bool =
  match rel with
  | Exact ts -> not (Core.Set.mem ts target)
  | Any -> false

(* A block's static jump facts, built once per solve at first visit:
   each jump with its edge cond, disabled continuation and classification,
   plus the block's call facts.  The callee summary is read per visit —
   it grows while a recursion is tentative. *)
type jump_plan = Cbat_runctx.jump_plan = {
  jp_jmp : jmp term;
  jp_cond : exp option;
  jp_disabled : exp option;
  jp_rel : edge_rel;
  jp_resolved : bool;
  jp_call_facts : Cbat_runctx.call_facts;
  (* The summary's effective preserved set, keyed physically by the
     summary it was derived from. *)
  mutable jp_preserved : (Int.Set.t * Int.Set.t) option;
}

type block_plan = Cbat_runctx.block_plan = {
  bp_term : blk term;
  bp_has_conds : bool;
  bp_jumps : jump_plan list;
}

let plan_block
    ~(resolved : Tid.Set.t Tid.Map.t)
    ~(jmp_conds : exp Tid.Map.t Tid.Map.t)
    ~(disabled : exp Tid.Map.t)
    ~(rctx : Cbat_runctx.refine_ctx)
    (source : tid) : block_plan =
  match Core.Map.find rctx.Cbat_runctx.rc_blocks source with
  | None -> invalid_arg "hike: source tid does not represent block"
  | Some bf ->
    let b = bf.Cbat_runctx.bf_term in
    let conds = Core.Map.find jmp_conds source in
    let bp_jumps =
      Term.enum jmp_t b |> Seq.to_list
      |> List.map ~f:(fun jmp ->
          { jp_jmp = jmp;
            jp_cond = Option.bind conds ~f:(fun m ->
                Core.Map.find m (Term.tid jmp));
            jp_disabled = Core.Map.find disabled (Term.tid jmp);
            jp_rel = edge_rel_of ~resolved jmp;
            jp_resolved = Core.Map.mem resolved (Term.tid jmp);
            jp_call_facts =
              Cbat_runctx.call_facts_of_jmp ~abi:rctx.Cbat_runctx.rc_abi
                ~blk:b jmp;
            jp_preserved = None }) in
    { bp_term = b; bp_has_conds = Option.is_some conds; bp_jumps }

(* The plan of [source], memoized for the solve. *)
let plans_of ~resolved ~jmp_conds ~disabled ~rctx : tid -> block_plan =
  let memo : block_plan Tid.Table.t = Tid.Table.create () in
  fun source ->
    match Hashtbl.find memo source with
    | Some p -> p
    | None ->
      let p = plan_block ~resolved ~jmp_conds ~disabled ~rctx source in
      Hashtbl.set memo ~key:source ~data:p;
      p

(* The destination's state, as one edge delivers it: the values it
   receives and the memory it carries.  The source's own values do not
   come along — the destination's state is built, not filtered.

   The live-in set is the destination's free reads and its phis.  On an
   SSA sub every non-entry word input is a phi, so the set is the phis;
   on an unversioned sub it is the registers the block reads.  One rule
   either way. *)
let contribution (rctx : Cbat_runctx.refine_ctx) ~(source : tid)
    ~(target : tid) (edge : AI.t) : AI.t =
  if AI.equal edge AI.bottom then AI.bottom
  else
    match Core.Map.find rctx.Cbat_runctx.rc_blocks target with
    | None -> edge
    | Some bf ->
      let edge =
        denote_phis ~synth:!(rctx.Cbat_runctx.rc_synth) ~source bf.Cbat_runctx.bf_term edge in
      let keep =
        Core.Set.to_list bf.Cbat_runctx.bf_live_ids
        |> List.map ~f:Cbat_var_id.var_of in
      AI.deliver ~keep edge

(* The source block's post-state: its IN state with its definitions
   replayed.  It is edge-independent, so the solver computes it once per
   source IN state and fans the same [forward] into every target. *)
let denote_block
    ~(rctx : Cbat_runctx.refine_ctx)
    (plan : block_plan) ~(entry : AI.t) : AI.t =
  (* A woken edge can visit an unreached predecessor.  Its calls and
     stores must not turn bottom into a partially populated state. *)
  if AI.equal entry AI.bottom then AI.bottom
  else denote_block_values ~synth:!(rctx.rc_synth) plan.bp_term entry

(* Denotation of one edge: [forward] is the source block's post-state. *)
let denote_jump
    ~(preserved : Int.Set.t)
    ~(callee : Tid.t -> Cbat_call_effects.callee)
    ~(rctx : Cbat_runctx.refine_ctx)
    (plan : block_plan) ~(source : tid) ~(entry : AI.t)
    ~(forward : AI.t) ~(target : tid) : AI.t =
  (* The backward refinement's entry state IS the source block's IN
     state — the env this jump transfers. *)
  let b = plan.bp_term in
  let env = forward in
  let per_jump acc (jp : jump_plan) =
    let jmp = jp.jp_jmp in
    let rel = jp.jp_rel in
    (* Observes the disabled continuation (the widening landmarks); the
       observation needs the walk, so it rides the same sol-carrying
       arm. *)
    Option.iter jp.jp_disabled
      ~f:(fun dc ->
        Cbat_backward.acquire_unsat ~synth:!(rctx.rc_synth) ~rctx ~entry
          ~landmarks:rctx.rc_landmarks
          ~witness:rctx.rc_nonneg
          env b dc);
    let env =
      match jp.jp_cond with
      | Some acc_cond ->
        Cbat_backward.refine_edge_inline
          ~entry ~rctx ~discarded:(walk_discards ~target rel) b env acc_cond
      | None -> env in

    let call_site_transfer ?signature ~(summary : Int.Set.t option) () =
      let facts = jp.jp_call_facts in
      (* The call reads the SP version the block ends with. *)
      let abi = { rctx.Cbat_runctx.rc_abi with sp = facts.cf_sp } in
      let stack_args =
        Cbat_call_effects.stack_arg_ranges ~synth:!(rctx.rc_synth)
          ~abi ~block:b ~entry env
      in
      let kept =
        Option.map summary ~f:(fun ws ->
            match jp.jp_preserved with
            | Some (ws0, p) when phys_equal ws0 ws -> p
            | _ ->
              let p = Cbat_call_effects.preserved_with_summary
                  ~abi:rctx.Cbat_runctx.rc_abi ~preserved ws in
              jp.jp_preserved <- Some (ws, p);
              p) in
      let result =
        Option.bind (List.hd rctx.Cbat_runctx.rc_abi.Hike_abi.return_regs)
          ~f:(fun ret ->
              List.find (Hike_stack_model.effects jmp).Hike_stack_model.Term_effects.writes
                ~f:(Var.same ret)) in
      Cbat_call_effects.transfer ?kept ?signature ?result ~abi ~preserved
        ~stack_args
        ~site:{ Cbat_call_effects.summary; read_lanes = facts.cf_lanes }
        env
    in
    let inspect_call c =
      (* An unsat edge is unreachable: it must not pause the solve on a
         callee it can never call. *)
      if AI.equal env AI.bottom then AI.bottom
      else
        match Call.return c with
        | None -> AI.bottom
        | Some (Direct tid) when compare_tid target tid <> 0 -> AI.bottom
        | Some _ ->
          (* The callee callback solves a Fresh callee at this call site
             and returns its published summary; an already-final sub is
             read without re-solving. *)
          let site_callee =
            match Call.target c with
            | Direct ct -> callee ct
            | Indirect texp ->
              Cbat_call_effects.indirect_callee
                ~synth:!(rctx.rc_synth)
                ~lookup:rctx.Cbat_runctx.rc_sub_lookup
                ~callee ~env texp
          in
          (match site_callee with
           | Cbat_call_effects.Summary summary -> call_site_transfer ~summary ()
           | Declared (summary, signature) ->
             call_site_transfer ~signature ~summary ())
    in
    let leads () = if env_leads ~target rel then env else AI.bottom in
    let env_res =
      match Jmp.kind jmp with
      | Int _ ->
        (* Traps ride the same frame-keep rule as ABI calls; a trap
           pushes no retaddr. *)
        call_site_transfer ~summary:None ()
      | Call c ->
        if jp.jp_resolved then
          (* A resolved transfer is the intra-sub jump the concrete
             machine performs: FULL IDENTITY — no callee effects; any
             other target is unreachable. *)
          leads ()
        else inspect_call c
      | Goto (Direct _) | Ret (Direct _) -> leads ()
      | Goto (Indirect _)
      | Ret (Indirect _) -> env in
    AI.join acc env_res in
  let refined = Seq.fold
    (reachable_jumps_by ~synth:!(rctx.rc_synth)
       ~jmp:(fun jp -> jp.jp_jmp) env (Seq.of_list plan.bp_jumps))
    ~init:AI.bottom
    ~f:per_jump in
  (* The edge delivers the destination's state: the values it receives and
     the memory it carries. *)
  let delivered = contribution rctx ~source ~target refined in
  delivered
