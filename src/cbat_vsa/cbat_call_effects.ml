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
       (match Cbat_word.to_int64 target with
        | Ok v -> Option.value_map (lookup v) ~default:(Summary None) ~f:callee
        | Error _ -> Summary None)
     | _ -> Summary None)

(* Segment-relative bounds of a stack value; None when no bound exists.
   [key_extent] is the shared key-space clamp — the same rule the
   sections' attribution uses. *)
let range_of (ws : WordSet.t) : (word * word) option =
  Option.map (Hike_stack_bounds.key_extent ws) ~f:(fun (lo, hi) ->
      (Cbat_word.to_word lo, Cbat_word.to_word hi))

(* The frame-keep boundary and the escape ranges are KEY-space:
   stack-derived cells key by segment offsets, foreign cells by their
   concrete addresses.  The callee writes below its own RSP, so the
   keep boundary is the HIGHEST possible call-time SP's position — an
   unbounded-below SP still has a highest position; a VLA-frame SP
   keeps from its extent's LOW end instead — every run's live bytes
   (the allocation's own, the frame above) sit at/above that run's SP,
   and the callee reaches below its entry only.  An unbounded-above SP
   keeps nothing — the whole-memory top stays the sound fallback on
   any doubt. *)
(* Only Stack/Window/Vla origins certify a frame-keep boundary or a
   stack escape. An SP without that proof forces whole-memory top. *)
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
      | Some offs -> (
          let int64_of w =
            match Cbat_word.to_int64 w with Ok v -> Some v | Error _ -> None
          in
          let bound w =
            Option.bind w ~f:(fun x ->
                Option.map (int64_of x) ~f:(fun off ->
                    Word.of_int64 ~width:64 off))
          in
          match WordSet.origin rsp with
          | Some (WordSet.Origin.Vla tid) -> (
            (* Keep from the allocation's base; an unknown base cannot
               place the frame — the top fallback. *)
            match WordSet.Origin.Vla_seed.extent tid with
            | Some { WordSet.Origin.base_lo = Some blo; _ } ->
              bound (Some (Cbat_word.of_int64 ~width:64 blo))
            | _ -> None)
          | _ -> bound (WordSet.Clp.max_elem offs))
      | None -> None
  in
  (* The escape list: the escapes whose origin names the stack line.  A
     plain or module-relative escape cannot collide with a Stack-line
     cell (the key namespaces by origin); a bottom escape writes
     nothing.  Such an escape keeps its bounded extent; a top one spans
     the whole line (the sound claim). *)
  let escape_ranges =
    List.filter_map escape ~f:(fun ws ->
        if WordSet.in_stack_segment ws
        then range_of ws
        else None)
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

let transfer ~(abi : Hike_abi.t) ~(preserved : Int.Set.t) ~(site : site)
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
            let id = Cbat_var_id.intern v in
            if Core.Set.mem ws id then acc
            else if
              Base.List.exists abi.Hike_abi.return_regs ~f:(Var.same v)
            then acc
            else Core.Set.add acc id)
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
