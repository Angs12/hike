(* What survives a call: the one policy over the caller's words and
   frames at a call site. *)

open Core
open Bap.Std

module AI = Cbat_ai_representation
module Mem = Cbat_ai_memmap
module WordSet = Cbat_clp_set_composite

type site = {
  summary : Int.Set.t option;
  written_lanes : var list;
  pushed : bool;
}

type callee = Summary of Int.Set.t option | Blocked

let indirect_callee ~(lookup : int64 -> Tid.t option)
    ~(callee : Tid.t -> callee) ~(env : AI.t) (texp : exp) : callee =
  match Cbat_transfer.denote_imm_exp texp env with
  | Error _ -> Summary None
  | Ok ws ->
    (match WordSet.enumerate ~cap:1 ws with
     | Some [ target ] ->
       (match Cbat_word.to_int64_opt target with
        | Some v -> Option.value_map (lookup v) ~default:(Summary None) ~f:callee
        | None -> Summary None)
     | _ -> Summary None)

(* Segment-relative bounds of a stack value; None when no bound exists.
   [key_extent] is the shared key-space clamp — the same rule the
   sections' attribution uses. *)
let range_of (ws : WordSet.t) : (Cbat_word.t * Cbat_word.t) option =
  Hike_stack_bounds.key_extent ws

(* The frame-keep boundary and the escape ranges are KEY-space:
   stack-derived cells key by segment offsets, foreign cells by their
   concrete addresses.  The callee writes below its own RSP, so the
   keep boundary is the HIGHEST possible call-time SP's position — an
   unbounded-below SP still has a highest position, and the callee
   reaches below its entry only.  An unbounded-above SP keeps nothing
   — the whole-memory top stays the sound fallback on any doubt.

   Only the Stack origin certifies a frame-keep boundary or a stack
   escape. An SP without that proof forces whole-memory top. *)
let frame_keep ~(preserved : Int.Set.t) ~(rsp : WordSet.t)
    ~(escape : WordSet.t list) (env : AI.t) : AI.t =
#ifdef VSA_DEBUG
  Cbat_attr_census.bump "call.frame";
#endif
  let env = AI.top_words_except ~preserved env in
  let keep_lo =
    (* An ascending, circular, or wrapped SP hull names no highest
       position — nothing provably survives; the top fallback below is
       the sound answer. *)
    if WordSet.is_ascending rsp || WordSet.is_circular rsp then None
    else
      match WordSet.stack_offsets rsp with
      | Some offs -> WordSet.Clp.Pieces.max_elem offs
      | None -> None
  in
  (* The escape list: each escape's stack-line leaves (a mixed value's
     stack addresses escape too).  A plain or module-relative escape
     cannot collide with a Stack-line cell (the key namespaces by
     origin); a bottom escape writes nothing.  Such an escape keeps its
     bounded extent; a top one spans the whole line (the sound claim). *)
  let escape_ranges =
    List.concat_map escape ~f:(fun ws -> List.filter_map (WordSet.stack_leaves ws) ~f:range_of)
  in
  match keep_lo with
  | Some lo ->
#ifdef VSA_DEBUG
    Cbat_attr_census.bump "call.frame.kept";
#endif
    AI.map_memories env ~f:(fun ~key:_ ~data ->
        Mem.call_keep data ~keep_lo:lo ~escape:escape_ranges)
  | None ->
#ifdef VSA_DEBUG
    Cbat_attr_census.bump "call.frame.top.rsp";
#endif
    AI.top_memories env

let preserved_with_summary ~(abi : Hike_abi.t) ~(preserved : Int.Set.t)
    (ws : Int.Set.t) : Int.Set.t =
  Base.List.fold abi.Hike_abi.caller_saved_gprs
    ~init:preserved ~f:(fun acc v ->
        let id = Cbat_var_id.intern v in
        if Core.Set.mem ws id then acc
        else if
          Base.List.exists abi.Hike_abi.return_regs ~f:(Var.same v)
        then acc
        else Core.Set.add acc id)

let transfer ?kept ~(abi : Hike_abi.t) ~(preserved : Int.Set.t)
    ~(site : site) (env : AI.t) : AI.t =
  let word_bits = Hike_abi.word_bits abi in
  let rsp = abi.Hike_abi.sp in
  (* A callee's kill summary keeps the caller-saved GPRs it provably
     never writes; the return regs are the call's own lanes.  No
     summary keeps only the base set. *)
  let preserved =
    match kept, site.summary with
    | Some k, _ -> k
    | None, Some ws -> preserved_with_summary ~abi ~preserved ws
    | None, None -> preserved
  in
  (* The escape: the registers the call block wrote. *)
  let escape =
    List.map site.written_lanes ~f:(fun v -> AI.find_word word_bits env v) in
  (* Every call keeps the caller frame at/above the highest possible
     call-time RSP outside the escapes — a trap like an ABI call; the
     whole-memory top stays the fallback on any doubt. *)
  let abs =
    frame_keep ~preserved
      ~rsp:(AI.find_word word_bits env rsp) ~escape env in
  (* The SP restores by one word on returns: the callee's ret pops
     exactly the retaddr the caller pushed.  On a stack word the +word
     lands in the offsets exactly. *)
  if site.pushed then
    AI.add_word abs ~key:rsp
      ~data:(WordSet.add (AI.find_word word_bits abs rsp)
               (WordSet.singleton
                  (Cbat_word.of_int ~width:word_bits abi.Hike_abi.word)))
  else abs
