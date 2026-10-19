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
   [ts]; [Any] — may continue anywhere. *)
type edge_rel = Exact of Tid.Set.t | Any

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
type jump_plan = {
  jp_jmp : jmp term;
  jp_cond : exp option;
  jp_disabled : exp option;
  jp_rel : edge_rel;
  jp_resolved : bool;
  (* The summary's effective preserved set, keyed physically by the
     summary it was derived from. *)
  mutable jp_preserved : (Int.Set.t * Int.Set.t) option;
}

type block_plan = {
  bp_term : blk term;
  bp_call_facts : Cbat_runctx.call_facts;
  bp_has_conds : bool;
  bp_jumps : jump_plan list;
}

let plan_block
    ~(resolved : Tid.Set.t Tid.Map.t)
    ~(edge_conds : exp Tid.Map.t Tid.Map.t)
    ~(disabled : exp Tid.Map.t)
    ~(rctx : Cbat_runctx.refine_ctx)
    (source : tid) : block_plan =
  match Core.Map.find rctx.Cbat_runctx.rc_blocks source with
  | None -> invalid_arg "hike: source tid does not represent block"
  | Some bf ->
    let b = bf.Cbat_runctx.bf_term in
    let conds = Core.Map.find edge_conds source in
    let bp_jumps =
      Term.enum jmp_t b |> Seq.to_list
      |> List.map ~f:(fun jmp ->
          { jp_jmp = jmp;
            jp_cond = Option.bind conds ~f:(fun m ->
                Core.Map.find m (Term.tid jmp));
            jp_disabled = Core.Map.find disabled (Term.tid jmp);
            jp_rel = edge_rel_of ~resolved jmp;
            jp_resolved = Core.Map.mem resolved (Term.tid jmp);
            jp_preserved = None }) in
    { bp_term = b; bp_call_facts = bf.Cbat_runctx.bf_call_facts;
      bp_has_conds = Option.is_some conds; bp_jumps }

(* The plan of [source], memoized for the solve. *)
let plans_of ~resolved ~edge_conds ~disabled ~rctx : tid -> block_plan =
  let memo : block_plan Tid.Table.t = Tid.Table.create () in
  fun source ->
    match Hashtbl.find memo source with
    | Some p -> p
    | None ->
      let p = plan_block ~resolved ~edge_conds ~disabled ~rctx source in
      Hashtbl.set memo ~key:source ~data:p;
      p

(* Denotation of a block's jumps. *)
let denote_jump
    ~(preserved : Int.Set.t)
    ~(callee : Tid.t -> Cbat_call_effects.callee)
    ~(rctx : Cbat_runctx.refine_ctx)
    (plan : block_plan) ~(entry : AI.t) ~(target : tid)
    : AI.t =
  (* The backward refinement's entry state IS the source block's IN
     state — the env this jump transfers. *)
  let b = plan.bp_term in
  let source = Term.tid b in
  let edges = match Map.find !(rctx.rc_edges) source with
    | Some (saved, edges) when phys_equal saved entry -> edges
    | _ -> Tid.Map.empty in
  match Map.find edges target with
  | Some refined -> refined
  | None ->
  let env = denote_block_values ~synth:!(rctx.rc_synth) b entry in
  let per_jump acc (jp : jump_plan) =
    let jmp = jp.jp_jmp in
    let rel = jp.jp_rel in
    (* Observes the disabled continuation (the widening landmarks); the
       observation needs the walk, so it rides the same sol-carrying
       arm. *)
    Option.iter jp.jp_disabled
      ~f:(fun dc ->
        Cbat_backward.acquire_unsat ~synth:!(rctx.rc_synth) ~entry
          ~landmarks:rctx.rc_landmarks
          ~witness:rctx.rc_nonneg
          env b dc);
    let env =
      match jp.jp_cond with
      | Some acc_cond ->
        Cbat_backward.refine_edge_inline
          ~entry ~rctx ~discarded:(walk_discards ~target rel) b env acc_cond
      | None -> env in

    let call_site_transfer ~(summary : Int.Set.t option) =
      let facts = plan.bp_call_facts in
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
      Cbat_call_effects.transfer ?kept ~abi ~preserved ~stack_args
        ~site:{ Cbat_call_effects.summary; read_lanes = facts.cf_lanes }
        env
    in
    let inspect_call c =
      match Call.return c with
      | None -> AI.bottom
      | Some (Direct tid) when compare_tid target tid <> 0 -> AI.bottom
      | Some _ ->
        (* Calls abstract; every caller's def is denoted.  A blocked
           callee has no summary yet: nothing flows past it. *)
        let site_callee =
          match Call.target c with
          | Direct ct -> callee ct
          | Indirect texp ->
            Cbat_call_effects.indirect_callee
              ~synth:!(rctx.rc_synth) ~lookup:rctx.Cbat_runctx.rc_sub_lookup
              ~callee ~env texp
        in
        match site_callee with
        | Cbat_call_effects.Blocked -> AI.bottom
        | Cbat_call_effects.Summary summary ->
          call_site_transfer ~summary
    in
    let leads () = if env_leads ~target rel then env else AI.bottom in
    let env_res =
      match Jmp.kind jmp with
      | Int _ ->
        (* Traps ride the same frame-keep rule as ABI calls; a trap
           pushes no retaddr. *)
        call_site_transfer ~summary:None
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
  (* Later replays mutate the general cells; keep this edge's facts private. *)
  let refined = AI.copy_scalars refined in
  rctx.rc_edges := Map.set !(rctx.rc_edges) ~key:source
      ~data:(entry, Map.set edges ~key:target ~data:refined);
  refined

(* Block denotation toward a target. *)
let denote_block
    ~(preserved : Int.Set.t)
    ~(callee : Tid.t -> Cbat_call_effects.callee)
    ~(plan_of : tid -> block_plan)
    ~(rctx : Cbat_runctx.refine_ctx)
    ~(source : tid) (env : AI.t)
    : target:tid -> AI.t =
  (* A woken edge can visit an unreached predecessor. Its calls and
     stores must not turn bottom into a partially populated state. *)
  if AI.equal env AI.bottom then fun ~target:_ -> AI.bottom
  else
  let plan = plan_of source in
  fun ~target ->
    denote_jump ~preserved ~callee ~rctx plan ~entry:env ~target
