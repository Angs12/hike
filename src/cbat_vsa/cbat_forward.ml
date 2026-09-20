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
   [ts]; [Any] — may continue anywhere; [Never] — never reaches it. *)
type edge_rel = Exact of Tid.Set.t | Any | Never

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
  | Never -> false

(* The walk projection: whether the edge's own refinement is discarded.
   NOT the env projection — on a noreturn call the walk RUNS (its
   empty-meet landmark observations persist) while the env result is
   bottom. *)
let walk_discards ~(target : tid) (rel : edge_rel) : bool =
  match rel with
  | Exact ts -> not (Core.Set.mem ts target)
  | Any -> false
  | Never -> true

(* Denotation of a block's jumps. *)
let denote_jump
    ~(preserved : Var.Set.t)
    ~(written : Var.Set.t option Tid.Map.t)
    ~(resolved : Tid.Set.t Tid.Map.t)
    ~(sub : sub term)
    ~(edge_conds : exp Tid.Map.t Tid.Map.t)
    ~(disabled : exp Tid.Map.t)
    ~(sol : (tid, AI.t) Solution.t)
    ~(rctx : Cbat_runctx.refine_ctx)
    (b : blk term)  (env : AI.t) ~(target : tid)
    : AI.t * Cbat_runctx.refine_ctx =
  let rc0 = rctx in
  (* Per jmp: the edge's own cond and the disabled continuation (the
     next edge's cond), both from the run's tables. *)
  let lookup_cond jmp =
    Core.Map.find edge_conds (Term.tid b)
    |> Option.bind ~f:(fun by_jmp ->
        Core.Map.find by_jmp (Term.tid jmp)) in
  let per_jump (acc, rctx) jmp =
    let edge_cond = lookup_cond jmp in
    let rel = edge_rel_of ~resolved jmp in
    (* Observes the disabled continuation (the widening landmarks); the
       observation needs the walk, so it rides the same sol-carrying
       arm. *)
    Option.iter (Core.Map.find disabled (Term.tid jmp))
      ~f:(fun dc ->
        Cbat_backward.acquire_unsat ~sol
          ~landmarks:(rctx : Cbat_runctx.refine_ctx).rc_landmarks
          ~witness:(rctx : Cbat_runctx.refine_ctx).rc_nonneg
          env b dc);
    let env, rctx =
      match edge_cond with
      | Some acc_cond ->
        Cbat_backward.refine_edge_inline ~sol
          ~rctx ~discarded:(walk_discards ~target rel) b env acc_cond
      | None -> (env, rctx) in

    let inspect_call c =
      match Call.return c with
        | None -> AI.bottom
        | Some (Direct tid) when compare_tid target tid <> 0 -> AI.bottom
        | Some (Indirect _)
        | Some (Direct _) ->
          (* Calls abstract; every caller's def is denoted. *)
          begin
            let abi = rc0.Cbat_runctx.rc_abi in
            let written_lanes, pushed =
              match Core.Map.find rc0.rc_blocks (Term.tid b) with
              | Some bf -> bf.bf_call_facts
              | None -> failwith "hike: no call facts for block (rctx)" in
            let target =
              match Call.target c with
              | Direct ct ->
                Cbat_call_effects.Callee
                  (match Core.Map.find written ct with
                   | Some (Some ws) -> Some ws
                   | _ -> None)
              | Indirect _ -> Cbat_call_effects.Callee None
            in
            Cbat_call_effects.transfer ~abi ~preserved
              ~site:{ Cbat_call_effects.target; written_lanes; pushed }
              env
          end in
    let env_res, rctx =
      match Jmp.kind jmp with
      | Int _ ->
        (* Traps are external callees. *)
        (Cbat_call_effects.transfer
           ~abi:(rc0.Cbat_runctx.rc_abi) ~preserved
           ~site:{ Cbat_call_effects.target = Trap;
                   written_lanes = []; pushed = false }
           env,
         rctx)
      | Call c -> (
        match Core.Map.find resolved (Term.tid jmp) with
        | Some _ ->
          (* A resolved transfer is the intra-sub jump the concrete
             machine performs: FULL IDENTITY — no callee effects; any
             other target is unreachable. *)
          ((if env_leads ~target rel then env else AI.bottom), rctx)
        | None -> (inspect_call c, rctx))
      | Goto (Direct _) | Ret (Direct _) ->
        ((if env_leads ~target rel then env else AI.bottom), rctx)
      | Goto (Indirect _)
      | Ret (Indirect _) -> (env, rctx) in
    (AI.join acc env_res, rctx) in
  Seq.fold (reachable_jumps env (Term.enum jmp_t b))
    ~init:(AI.bottom, rctx)
    ~f:per_jump

(* Block denotation toward a target. *)
let denote_block
    ~(preserved : Var.Set.t)
    ~(written : Var.Set.t option Tid.Map.t)
    ~(resolved : Tid.Set.t Tid.Map.t)
    ~(sub : sub term)
    ~(edge_conds : exp Tid.Map.t Tid.Map.t)
    ~(disabled : exp Tid.Map.t)
    ~(sol : (tid, AI.t) Solution.t)
    ~(rctx : Cbat_runctx.refine_ctx)
    (ctx : program term) ~(source : tid) (env : AI.t)
    : target:tid -> AI.t * Cbat_runctx.refine_ctx =
 match (Program.lookup blk_t ctx source) with
   | Some b ->
     let postcond = denote_defs b env in
     fun ~target ->
       denote_jump ~preserved ~written ~resolved ~sub ~edge_conds ~disabled
         ~sol
         ~rctx
         b postcond ~target
   | None -> fun ~target ->
       ignore (invalid_arg "source tid does not represent block");
       (AI.bottom, rctx)
