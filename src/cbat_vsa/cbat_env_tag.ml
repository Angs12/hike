(* The Env Tag seam: the before-state environment the solve held at a
   def, riding the def's value; absence denotes TOP.  Owns the KB
   domain/slot, the stamp, the raw replay, the VSA_DEBUG differential,
   the consumers' denotation seam, and the solution's env stamp. *)

include Core
open Bap.Std
open Bap_core_theory
open Graphlib.Std

module AI = Cbat_ai_representation
module WordSet = Cbat_clp_set_composite

(* The transfer machinery the replay and the seam read. *)
let denote_def = Cbat_transfer.denote_def
let denote_defs = Cbat_transfer.denote_defs
let denote_imm_exp = Cbat_transfer.denote_imm_exp

(* The Env Tag: the before-state environment the solve held at a def,
   riding the def's value.  Absence means the def is outside the
   analysis boundary — minted after it, or its sub did not converge —
   and denotes TOP. *)

module KB = Bap_knowledge.Knowledge

type KB.conflict += Env_tag_conflict

let () =
  KB.Conflict.register_printer (function
    | Env_tag_conflict ->
        Some
          "hike: env-tag conflict: two different before-state environments were stamped for one def"
    | _ -> None)

let env_tag_d : AI.t option Hike_def_slot.t =
  Hike_def_slot.optional ~name:"hike-env-tag"
    ~inspect:(fun _ -> Sexp.Atom "hike:env-tag")
    ~join:(fun a b ->
#ifdef VSA_DEBUG
      let () = Cbat_kb_census.bump "domain.env.join" in
#endif
      if AI.equal a b then Ok a else Error Env_tag_conflict)
    ~equal:(fun a b ->
#ifdef VSA_DEBUG
      let () = Cbat_kb_census.bump "domain.env.equal" in
#endif
      AI.equal a b)
    ~get_bump:"env_tag.get" ~put_bump:"env_tag.put"
    ~bump:
#ifdef VSA_DEBUG
      Cbat_kb_census.bump
#else
      (fun _ -> ())
#endif

let env_tag_slot = Hike_def_slot.slot env_tag_d

let env_tag (d : def term) : AI.t option = Hike_def_slot.get env_tag_d d

let set_env_tag (env : AI.t) (d : def term) : def term =
  Hike_def_slot.put env_tag_d (Some env) d

(* The SOLVE's own replay — for Hike_cfg_complete, the producer's
   completion loop, ONLY.  Consumers use the seam [denote_exp_at];
   this is a raw replay from the given state. *)
let solve_denote :
    pre:AI.t -> blk:blk term -> ?def:def term -> exp ->
    (WordSet.t, Type.error) Result.t =
  fun ~pre ~blk ?def e ->
    let env =
      match def with
      | None -> denote_defs blk pre
      | Some d ->
        let hit = ref false in
        let env =
          Term.enum def_t blk
          |> Seq.fold ~init:pre ~f:(fun env x ->
              if !hit then env
              else if Tid.equal (Term.tid x) (Term.tid d) then (
                hit := true;
                env)
              else denote_def x env)
        in
        if !hit then env else AI.top
    in
    denote_imm_exp e env

#ifdef VSA_DEBUG
(* The Env Tag differential: every def-level query replays from [pre]
   through the raw path and compares the tag's answer; a def whose tid
   was stamped and now carries no tag is a LOST tag, counted as a
   mismatch like a value divergence.  Mismatches print as they happen;
   the per-sub census (stamped / queried / mismatch) prints at exit. *)
let env_tag_sub_of_blk : (Tid.t, string) Hashtbl.t = Hashtbl.create (module Tid)
let env_tag_stamped : (Tid.t, unit) Hashtbl.t = Hashtbl.create (module Tid)
let env_tag_census : (string, int * int * int) Hashtbl.t =
  Hashtbl.create (module String)

let env_tag_bump ~(sub : string) ~(stamped : int) ~(queried : int)
    ~(mismatch : int) : unit =
  let s, q, m =
    Hashtbl.find env_tag_census sub |> Base.Option.value ~default:(0, 0, 0)
  in
  Hashtbl.set env_tag_census ~key:sub
    ~data:(s + stamped, q + queried, m + mismatch)

let env_tag_dump () =
  Hashtbl.iteri env_tag_census
    ~f:(fun ~key:sub ~data:(stamped, queried, mismatch) ->
      Printf.eprintf
        "hike-env-tag: sub %s: stamped=%d queried=%d mismatch=%d\n%!" sub
        stamped queried mismatch)

let () = at_exit env_tag_dump

let env_tag_result_str (r : (WordSet.t, Type.error) Result.t) : string =
  match r with
  | Ok ws ->
    if WordSet.is_top ws then "TOP"
    else if WordSet.is_bottom ws then "BOTTOM"
    else (
      match WordSet.min_elem ws, WordSet.max_elem ws with
      | Some lo, Some hi ->
        Printf.sprintf "[%s..%s]" (Cbat_word.to_string lo)
          (Cbat_word.to_string hi)
      | _ -> "?")
  | Error e -> "error: " ^ Type.Error.to_string e

let env_tag_check ~pre ~blk ~(tagged : bool) (d : def term) (e : exp)
    (answer : (WordSet.t, Type.error) Result.t) : unit =
  let sub =
    Hashtbl.find env_tag_sub_of_blk (Term.tid blk)
    |> Base.Option.value ~default:"?"
  in
  let lost = (not tagged) && Hashtbl.mem env_tag_stamped (Term.tid d) in
  let replay = solve_denote ~pre ~blk ~def:d e in
  let mismatch =
    lost
    || (tagged
        && (match answer, replay with
            | Ok a, Ok r -> not (WordSet.equal a r)
            | Error a, Error r -> not (Type.Error.equal a r)
            | _ -> true))
  in
  env_tag_bump ~sub ~stamped:0 ~queried:1
    ~mismatch:(if mismatch then 1 else 0);
  if lost then
    Printf.eprintf
      "hike-env-tag: LOST sub %s blk %s def %s: tag=absent (stamped before) replay=%s\n%!"
      sub (Tid.to_string (Term.tid blk)) (Tid.to_string (Term.tid d))
      (env_tag_result_str replay)
  else if mismatch then
    Printf.eprintf
      "hike-env-tag: MISMATCH sub %s blk %s def %s: tag=%s replay=%s\n%!" sub
      (Tid.to_string (Term.tid blk)) (Tid.to_string (Term.tid d))
      (env_tag_result_str answer) (env_tag_result_str replay)
#endif

(* [e] denotes in the before-env of [def] — the Env Tag the solve
   stamped on the def, or [AI.top] when the def carries no tag (minted
   after the analysis boundary) — or, with no [def], in the block's
   postcondition.  [pre] feeds the VSA_DEBUG differential's replay
   only. *)
let denote_exp_at :
    ?post:AI.t -> pre:AI.t -> blk:blk term -> ?def:def term -> exp ->
    (WordSet.t, Type.error) Result.t =
  fun ?(post = AI.top) ~pre ~blk ?def e ->
    match def with
    | None ->
#ifdef VSA_DEBUG
      let () = Cbat_kb_census.bump "seam.query.nodef" in
#endif
      denote_imm_exp e post
    | Some d ->
#ifdef VSA_DEBUG
      let () = Cbat_kb_census.bump "seam.query.def" in
#endif
      let tag = env_tag d in
      let env = match tag with Some env -> env | None -> AI.top in
      let answer = denote_imm_exp e env in
#ifdef VSA_DEBUG
      env_tag_check ~pre ~blk ~tagged:(Base.Option.is_some tag) d e answer;
#endif
      answer

(* The solve's boundary sweep: one (pre, post) env pair per block (pre
   the solution's entry state, post the block's def replay from it) and
   the sub with every def stamped with the env its own transfer reads. *)
let stamp_envs_of_sol ~(sol : (tid, AI.t) Solution.t) (sub : sub term) :
    (AI.t * AI.t) Tid.Map.t * sub term =
  (* The final replay is the seed's authoritative pass for this sub:
     clear its fixpoint-transient events so the table holds only the
     events the converged denotations still satisfy.  Other subs'
     entries stay: the table accumulates the program's allocations. *)
  let own =
    Term.enum blk_t sub |> Seq.concat_map ~f:(Term.enum def_t)
    |> Seq.map ~f:Term.tid |> Seq.to_list |> Tid.Set.of_list
  in
  WordSet.Origin.Vla_seed.filter (fun t -> not (Core.Set.mem own t));
  let envs = ref Tid.Map.empty in
  let sub' =
    Term.map blk_t sub ~f:(fun blk ->
        let pre = Solution.get sol (Term.tid blk) in
        let env = ref pre in
        let blk' =
          Term.map def_t blk ~f:(fun d ->
              let before = !env in
              let after = denote_def d before in
              env := after;
              let d = Cbat_def_origin.stamp_origin ~before d after in
#ifdef VSA_DEBUG
              Hashtbl.set env_tag_stamped ~key:(Term.tid d) ~data:();
              env_tag_bump ~sub:(Sub.name sub) ~stamped:1 ~queried:0
                ~mismatch:0;
#endif
              set_env_tag before d)
        in
        envs := Core.Map.set !envs ~key:(Term.tid blk) ~data:(pre, !env);
        blk')
  in
#ifdef VSA_DEBUG
  Term.enum blk_t sub'
  |> Seq.iter ~f:(fun b ->
      Hashtbl.set env_tag_sub_of_blk ~key:(Term.tid b) ~data:(Sub.name sub));
#endif
  (!envs, sub')

