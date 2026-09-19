(* Forward jump/block denotation: the per-jmp transfer toward a target
   (the direct/resolved identity, the call abstraction), joined over the
   reachable jumps; each conditional edge drives the backward
   refinement inline (cbat_backward, one-directional).  Consumes the
   transfer (open). *)

include Core
open Bap.Std
open Graphlib.Std
module AI = Cbat_ai_representation
module WordSet = Cbat_clp_set_composite
open Cbat_transfer

(* The ONE edge classification: whether a jump's transfer reaches the
   denotation target.  [Exact ts] — iff the transfer's target is in
   [ts]; [Any] — may continue anywhere (the target among them);
   [Never] — never reaches it. *)
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
let denote_jump ?preserved
    ?(written : Var.Set.t option Tid.Map.t = Tid.Map.empty)
    ?(resolved : Tid.Set.t Tid.Map.t = Tid.Map.empty)
    ?(sub : sub term option = None)
    ?edge_conds ?disabled ?sol
    ~(rctx : Cbat_runctx.refine_ctx)
    (b : blk term)  (env : AI.t) ~(target : tid)
    : AI.t * Cbat_runctx.refine_ctx =
  (* Fold joins per-jump results. *)
  let rc0 = rctx in
  (* Per jmp: the edge's own cond and the disabled continuation (the
     next edge's cond — the fallthrough's completed form), both from
     the run's tables.  Without them there is no cond to constrain and
     no continuation to observe. *)
  let lookup_cond jmp =
    match edge_conds with
    | Some tbl ->
      Core.Map.find tbl (Term.tid b)
      |> Option.bind ~f:(fun by_jmp ->
          Core.Map.find by_jmp (Term.tid jmp))
    | None -> None in
  let per_jump (acc, rctx) jmp =
    let edge_cond = lookup_cond jmp in
    let rel = edge_rel_of ~resolved jmp in
    (* Observe the disabled continuation (the widening landmarks); the
       edge's cond constrains the state inside refine_edge_inline.
       The observation needs the walk (the producer push), so it rides
       the same sol-carrying arm. *)
    (match sol, disabled with
     | Some snap, Some tbl ->
       Option.iter (Core.Map.find tbl (Term.tid jmp))
         ~f:(fun dc ->
           Cbat_backward.acquire_unsat ~sol:snap
             ~witness:(rctx : Cbat_runctx.refine_ctx).rc_nonneg
             env b dc)
     | _ -> ());
    (* Deep walk uses the same edge cond. *)
    let env, rctx =
      match edge_conds, sol, sub with
      | Some _, Some snap, Some _ ->
        (match edge_cond with
         | Some acc_cond ->
           Cbat_backward.refine_edge_inline ~sol:snap
             ~rctx:rctx ~jt:(Term.tid jmp)
             ~discarded:(walk_discards ~target rel) b env acc_cond
         | None -> (env, rctx))
      | _ -> (env, rctx) in

    let inspect_call c =
      match Call.return c with
        | None -> AI.bottom
        | Some (Direct tid) when compare_tid target tid <> 0 -> AI.bottom
        | Some (Indirect _)
        | Some (Direct _) ->
          (* Calls abstract; every caller's def is denoted. *)
          begin
            (* The run's convention facts (the rctx carries them). *)
            let abi = rc0.Cbat_runctx.rc_abi in
            let word_bits = 8 * abi.Hike_abi.word in
            let rsp = abi.Hike_abi.sp in
            (* A direct callee's kill summary keeps the caller-saved GPRs
               it provably never writes; the return regs are the call's
               own lanes.  No summary (missing or kill-all) keeps only
               the base preserved set. *)
            let preserved_site =
              let base = Option.value ~default:Var.Set.empty preserved in
              match Call.target c with
              | Direct ct -> (
                  match Core.Map.find written ct with
                  | Some (Some ws) ->
                    Base.List.fold abi.Hike_abi.caller_saved_gprs
                      ~init:base ~f:(fun acc v ->
                          if Core.Set.mem ws v then acc
                          else if
                            Base.List.exists
                              abi.Hike_abi.return_regs ~f:(Var.same v)
                          then acc
                          else Core.Set.add acc v)
                  | _ -> base)
              | Indirect _ -> base
            in
            (* The run's convention facts (the rctx carries them);
               [mk_rctx] builds the facts for every block of the sub. *)
            let written_lanes, pushed =
              match Core.Map.find rc0.rc_blocks (Term.tid b) with
              | Some bf -> bf.bf_call_facts
              | None -> failwith "hike: no call facts for block (rctx)" in
            (* Written registers are static. *)
            let escape =
              List.map written_lanes ~f:(fun v -> AI.find_word word_bits env v) in
            let abs =
              AI.call_abstraction_frame
                ~preserved:preserved_site
                ~rsp:(AI.find_word word_bits env rsp)
                ~escape env in
            (* The SP restores by one word on returns: the matched-pair
               restore — the callee's ret pops exactly the retaddr the
               caller pushed.  On a stack word the +word lands in the
               offsets exactly (StackOff + const). *)
            if pushed then begin
              AI.add_word abs ~key:rsp
                ~data:(WordSet.add (AI.find_word word_bits abs rsp)
                         (WordSet.singleton
                            (Cbat_word.of_int ~width:word_bits
                               abi.Hike_abi.word)))
            end else abs
          end in
    (* Per-jump transfer results. *)
    let env_res, rctx =
      match Jmp.kind jmp with
      | Int _ ->
        (* Traps are external callees. *)
        (AI.call_abstraction
           ~preserved:(Option.value ~default:Var.Set.empty preserved) env,
         rctx)
      | Call c -> (
        match Core.Map.find resolved (Term.tid jmp) with
        | Some _ ->
          (* A resolved transfer is the intra-sub jump the concrete
             machine performs: FULL IDENTITY — no callee effects on
             registers, memory, or frame; control continues at cont.
             Any other target is unreachable. *)
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
let denote_block ?preserved
    ?(written : Var.Set.t option Tid.Map.t = Tid.Map.empty)
    ?(resolved : Tid.Set.t Tid.Map.t = Tid.Map.empty)
    ?(sub : sub term option = None)
    ?(edge_conds : exp Tid.Map.t Tid.Map.t option = None)
    ?(disabled : exp Tid.Map.t option = None)
    ?(sol : (tid, AI.t) Solution.t option = None)
    ~(rctx : Cbat_runctx.refine_ctx)
    (ctx : program term) ~(source : tid) (env : AI.t)
    : target:tid -> AI.t * Cbat_runctx.refine_ctx =
 match (Program.lookup blk_t ctx source) with
   | Some b ->
     let postcond = denote_defs b env in
     fun ~target ->
       denote_jump ?preserved ~written ~resolved ~sub ?edge_conds ?disabled
         ?sol
         ~rctx
         b postcond ~target
   | None -> fun ~target ->
       ignore (invalid_arg "source tid does not represent block");
       (AI.bottom, rctx)
