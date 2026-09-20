(* What survives a call: the one policy over the caller's words and
   frames at a call site. *)

open Core
open Bap.Std

module AI = Cbat_ai_representation
module WordSet = Cbat_clp_set_composite

type target =
  | Callee of Var.Set.t option
  | Trap

type site = {
  target : target;
  written_lanes : var list;
  pushed : bool;
}

let transfer ~(abi : Hike_abi.t) ~(preserved : Var.Set.t) ~(site : site)
    (env : AI.t) : AI.t =
  let word_bits = 8 * abi.Hike_abi.word in
  let rsp = abi.Hike_abi.sp in
  (* A callee's kill summary keeps the caller-saved GPRs it provably
     never writes; the return regs are the call's own lanes.  No
     summary (unknown target or kill-all) keeps only the base set. *)
  let preserved =
    match site.target with
    | Callee (Some ws) ->
      Base.List.fold abi.Hike_abi.caller_saved_gprs
        ~init:preserved ~f:(fun acc v ->
            if Core.Set.mem ws v then acc
            else if
              Base.List.exists abi.Hike_abi.return_regs ~f:(Var.same v)
            then acc
            else Core.Set.add acc v)
    | Callee None | Trap -> preserved
  in
  (* The escape: the registers the call block wrote. *)
  let escape =
    List.map site.written_lanes ~f:(fun v -> AI.find_word word_bits env v) in
  let abs =
    match site.target with
    | Callee _ -> AI.call_abstraction_frame ~preserved
                    ~rsp:(AI.find_word word_bits env rsp) ~escape env
    | Trap -> AI.call_abstraction ~preserved env
  in
  (* The SP restores by one word on returns: the callee's ret pops
     exactly the retaddr the caller pushed.  On a stack word the +word
     lands in the offsets exactly. *)
  if site.pushed then
    AI.add_word abs ~key:rsp
      ~data:(WordSet.add (AI.find_word word_bits abs rsp)
               (WordSet.singleton
                  (Cbat_word.of_int ~width:word_bits abi.Hike_abi.word)))
  else abs
