(* What survives a call: the one policy over the caller's words and
   frames at a call site. *)

open Core
open Bap.Std

module AI = Cbat_ai_representation
module Mem = Cbat_ai_memmap
module WordSet = Cbat_clp_set_composite

type site = {
  summary : Var.Set.t option;
  written_lanes : var list;
  pushed : bool;
}

let indirect_summary ~(lookup : int64 -> Tid.t option)
    ~(summary_of : Tid.t -> Var.Set.t option) ~(env : AI.t)
    (texp : exp) : Var.Set.t option =
  match Cbat_transfer.denote_imm_exp texp env with
  | Error _ -> None
  | Ok ws ->
    if WordSet.is_top ws then None
    else
      match WordSet.min_elem ws, WordSet.max_elem ws with
      | Some lo, Some hi when Cbat_word.equal lo hi ->
        (match Cbat_word.to_int64 lo with
         | Ok v -> Option.bind (lookup v) ~f:summary_of
         | Error _ -> None)
      | _ -> None

(* Segment-relative bounds of a stack value; None when no bound exists.
   [key_extent] is the shared key-space clamp — the same rule the
   sections' attribution uses. *)
let range_of (ws : WordSet.t) : (word * word) option =
  Option.map (Hike_stack_bounds.key_extent ws) ~f:(fun (lo, hi) ->
      (Cbat_word.to_word lo, Cbat_word.to_word hi))

(* The frame-keep boundary and the escape ranges are KEY-space:
   stack-derived cells key by segment offsets, foreign cells by their
   concrete addresses.  The callee writes below its own RSP, so cells
   at keys at/above the HIGHEST possible call-time RSP survive every
   call site; the whole-memory top stays the sound fallback on any
   doubt. *)
let frame_keep ~(preserved : Var.Set.t) ~(rsp : WordSet.t)
    ~(escape : WordSet.t list) (env : AI.t) : AI.t =
#ifdef VSA_DEBUG
  Cbat_attr_census.bump "call.frame";
#endif
  let env = AI.top_words_except ~preserved env in
  let keep_lo = Option.map ~f:snd (range_of rsp) in
  let escape_ranges =
    match List.filter_map escape ~f:range_of with
    | ranges when List.length ranges = List.length escape -> Some ranges
    | _ -> None in
  match keep_lo, escape_ranges with
  | Some lo, Some ranges ->
#ifdef VSA_DEBUG
    Cbat_attr_census.bump "call.frame.kept";
#endif
    AI.map_memories env ~f:(fun ~key:_ ~data ->
        Mem.call_keep data ~keep_lo:lo ~escape:ranges)
  | _ ->
#ifdef VSA_DEBUG
    (match keep_lo, escape_ranges with
     | None, None -> Cbat_attr_census.bump "call.frame.top.rsp_and_escape"
     | None, Some _ -> Cbat_attr_census.bump "call.frame.top.rsp"
     | Some _, None -> Cbat_attr_census.bump "call.frame.top.escape"
     | Some _, Some _ -> ());
#endif
    AI.top_memories env

let transfer ~(abi : Hike_abi.t) ~(preserved : Var.Set.t) ~(site : site)
    (env : AI.t) : AI.t =
  let word_bits = Hike_abi.word_bits abi in
  let rsp = abi.Hike_abi.sp in
  (* A callee's kill summary keeps the caller-saved GPRs it provably
     never writes; the return regs are the call's own lanes.  No
     summary keeps only the base set. *)
  let preserved =
    match site.summary with
    | Some ws ->
      Base.List.fold abi.Hike_abi.caller_saved_gprs
        ~init:preserved ~f:(fun acc v ->
            if Core.Set.mem ws v then acc
            else if
              Base.List.exists abi.Hike_abi.return_regs ~f:(Var.same v)
            then acc
            else Core.Set.add acc v)
    | None -> preserved
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
