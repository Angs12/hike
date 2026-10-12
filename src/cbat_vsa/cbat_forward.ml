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

(* Denotation of a block's jumps. *)
let denote_jump
    ~(preserved : Int.Set.t)
    ~(callee : Tid.t -> Cbat_call_effects.callee)
    ~(resolved : Tid.Set.t Tid.Map.t)
    ~(edge_conds : exp Tid.Map.t Tid.Map.t)
    ~(disabled : exp Tid.Map.t)
    ~(rctx : Cbat_runctx.refine_ctx)
    (b : blk term)  (env : AI.t) ~(entry : AI.t) ~(target : tid)
    : AI.t =
  (* The backward refinement's entry state IS the source block's IN
     state — the env this jump transfers. *)
  (* Per jmp: the edge's own cond and the disabled continuation (the
     next edge's cond), both from the run's tables. *)
  let lookup_cond jmp =
    Core.Map.find edge_conds (Term.tid b)
    |> Option.bind ~f:(fun by_jmp ->
        Core.Map.find by_jmp (Term.tid jmp)) in
  let per_jump acc jmp =
    let edge_cond = lookup_cond jmp in
    let rel = edge_rel_of ~resolved jmp in
    (* Observes the disabled continuation (the widening landmarks); the
       observation needs the walk, so it rides the same sol-carrying
       arm. *)
    Option.iter (Core.Map.find disabled (Term.tid jmp))
      ~f:(fun dc ->
        Cbat_backward.acquire_unsat ~entry:env
          ~landmarks:(rctx : Cbat_runctx.refine_ctx).rc_landmarks
          ~witness:(rctx : Cbat_runctx.refine_ctx).rc_nonneg
          env b dc);
    let env =
      match edge_cond with
      | Some acc_cond ->
        Cbat_backward.refine_edge_inline
          ~entry ~rctx ~discarded:(walk_discards ~target rel) b env acc_cond
      | None -> env in

    let call_site_transfer ~(summary : Int.Set.t option) ~(pushed : bool) =
      let written_lanes, _ =
        match Core.Map.find rctx.rc_blocks (Term.tid b) with
        | Some bf -> bf.bf_call_facts
        | None -> failwith "hike: no call facts for block (rctx)"
      in
      Cbat_call_effects.transfer ~abi:rctx.Cbat_runctx.rc_abi ~preserved
        ~site:{ Cbat_call_effects.summary; written_lanes; pushed }
        env
    in
    let inspect_call c =
      match Call.return c with
      | None -> AI.bottom
      | Some (Direct tid) when compare_tid target tid <> 0 -> AI.bottom
      | Some (Indirect _)
      | Some (Direct _) ->
        (* Calls abstract; every caller's def is denoted.  A blocked
           callee has no summary yet: nothing flows past it. *)
        let site_callee =
          match Call.target c with
          | Direct ct -> callee ct
          | Indirect texp ->
            Cbat_call_effects.indirect_callee
              ~lookup:rctx.Cbat_runctx.rc_sub_lookup ~callee ~env texp
        in
        match site_callee with
        | Cbat_call_effects.Blocked -> AI.bottom
        | Cbat_call_effects.Summary summary ->
          let _written_lanes, pushed =
            match Core.Map.find rctx.rc_blocks (Term.tid b) with
            | Some bf -> bf.bf_call_facts
            | None -> failwith "hike: no call facts for block (rctx)"
          in
          call_site_transfer ~summary ~pushed
    in
    let env_res =
      match Jmp.kind jmp with
      | Int _ ->
        (* Traps ride the same frame-keep rule as ABI calls; a trap
           pushes no retaddr. *)
        call_site_transfer ~summary:None ~pushed:false
      | Call c -> (
        match Core.Map.find resolved (Term.tid jmp) with
        | Some _ ->
          (* A resolved transfer is the intra-sub jump the concrete
             machine performs: FULL IDENTITY — no callee effects; any
             other target is unreachable. *)
          (if env_leads ~target rel then env else AI.bottom)
        | None -> inspect_call c)
      | Goto (Direct _) | Ret (Direct _) ->
        (if env_leads ~target rel then env else AI.bottom)
      | Goto (Indirect _)
      | Ret (Indirect _) -> env in
    AI.join acc env_res in
  Seq.fold (reachable_jumps env (Term.enum jmp_t b))
    ~init:AI.bottom
    ~f:per_jump

(* Block denotation toward a target. *)
let denote_block
    ~(preserved : Int.Set.t)
    ~(callee : Tid.t -> Cbat_call_effects.callee)
    ~(resolved : Tid.Set.t Tid.Map.t)
    ~(edge_conds : exp Tid.Map.t Tid.Map.t)
    ~(disabled : exp Tid.Map.t)
    ~(rctx : Cbat_runctx.refine_ctx)
    ~(source : tid) (env : AI.t)
    : target:tid -> AI.t =
 match (Core.Map.find rctx.Cbat_runctx.rc_blocks source) with
   | Some bf ->
     let b = bf.Cbat_runctx.bf_term in
     (* The block's postcondition depends only on the source block's
        IN state: one denotation per (block, state), shared by every
        successor edge. *)
     let postcond =
       match Core.Map.find !(rctx.Cbat_runctx.rc_post) source with
       | Some (e0, p0) when phys_equal e0 env -> p0
       | _ ->
         let p = denote_defs b env in
         rctx.Cbat_runctx.rc_post :=
           Core.Map.set !(rctx.Cbat_runctx.rc_post) ~key:source ~data:(env, p);
         p
     in
     fun ~target ->
       denote_jump ~preserved ~callee ~resolved ~edge_conds ~disabled
         ~rctx
         b postcond ~entry:env ~target
   | None -> fun ~target ->
       invalid_arg "hike: source tid does not represent block"
