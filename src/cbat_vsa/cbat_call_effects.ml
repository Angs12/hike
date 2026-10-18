(* What survives a call: the one policy over the caller's words and
   frames at a call site. *)

open Core
open Bap.Std

module AI = Cbat_ai_representation
module Mem = Cbat_ai_memmap
module WordSet = Cbat_clp_set_composite

type site = {
  summary : Int.Set.t option;
  read_lanes : var list;
  pushed : bool;
}

type callee = Summary of Int.Set.t option | Blocked

let indirect_callee ~(synth : Hike_synth.table) ~(lookup : int64 -> Tid.t option)
    ~(callee : Tid.t -> callee) ~(env : AI.t) (texp : exp) : callee =
  match Cbat_transfer.denote_imm_exp ~synth texp env with
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

(* The call block's bounded outgoing stack-argument hull.  The slot test
   is shared with promotion: only a singleton stack store beginning at a
   word-aligned slot above the call-time SP contributes. Store addresses
   use their before-states, before a later call push changes SP. *)
let stack_arg_ranges ~(synth : Hike_synth.table) ~(abi : Hike_abi.t) ~(block : blk term)
    ~(entry : AI.t) (env : AI.t) :
    (Cbat_word.t * Cbat_word.t) list =
  if not (Term.enum jmp_t block |> Seq.exists ~f:Hike_stack_model.machine_call)
  then []
  else
  let word_bits = Hike_abi.word_bits abi in
  let rsp = AI.find_word word_bits env abi.Hike_abi.sp in
  match Hike_stack_model.singleton_stack_position rsp with
  | None -> []
  | Some call_sp ->
    let ranges =
      Term.enum def_t block
      |> Seq.fold ~init:([], entry) ~f:(fun (acc, before) d ->
          let acc = match Hike_stack_model.addr_of_rhs (Def.rhs d),
                Hike_stack_model.store_data_of_rhs (Def.rhs d) with
          | Some (addr, size), Some _ ->
            (match Cbat_transfer.denote_imm_exp ~synth addr before with
             | Error _ -> acc
             | Ok address ->
               (match Hike_stack_model.singleton_stack_position address with
                | Some start
                  when Option.is_some
                         (Hike_stack_model.call_arg_slot ~word:abi.Hike_abi.word
                            ~call_sp ~start) ->
                  (match range_of address with
                   | None -> acc
                   | Some (lo, hi) ->
                     let extra =
                       Cbat_word.of_int ~width:word_bits
                         (Size.in_bytes size - 1)
                     in
                     let hi' = Cbat_word.add hi extra in
                     let hi' =
                       if Cbat_word.(hi' < hi) then Cbat_word.ones word_bits
                       else hi'
                     in
                     (lo, hi') :: acc)
                | _ -> acc))
          | _ -> acc in
          (acc, Cbat_transfer.denote_def ~synth d before))
      |> fst
    in
    (match ranges with
     | [] -> []
     | (lo, hi) :: rest ->
       let lo, hi =
         List.fold rest ~init:(lo, hi) ~f:(fun (lo, hi) (lo', hi') ->
             ((if Cbat_word.(lo' < lo) then lo' else lo),
              (if Cbat_word.(hi' > hi) then hi' else hi)))
       in
       [ lo, hi ])

(* The frame-keep boundary and outgoing stack-argument ranges are
   KEY-space: stack-derived cells key by segment offsets, foreign cells
   by their concrete addresses. The callee writes below its own RSP, so
   the keep boundary is the HIGHEST possible call-time SP's position —
   an unbounded-below SP still has a highest position, and the callee
   reaches below its entry only. An unbounded-above SP keeps nothing —
   the whole-memory top stays the sound fallback on any doubt.

   Only the Stack origin certifies a frame-keep boundary. An SP without
   that proof forces whole-memory top. *)
let frame_keep ~(preserved : Int.Set.t) ~(rsp : WordSet.t)
    ~(frame_escaped : bool)
    ~(stack_args : (Cbat_word.t * Cbat_word.t) list) (env : AI.t) : AI.t =
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
  match keep_lo with
  | Some lo ->
#ifdef VSA_DEBUG
    Cbat_attr_census.bump "call.frame.kept";
#endif
    AI.map_memories env ~f:(fun ~key:_ ~data ->
        Mem.call_keep data ~keep_lo:lo ~stack_args
          ~clear_frame:frame_escaped)
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

let transfer ?kept ?(stack_args = []) ~(abi : Hike_abi.t) ~(preserved : Int.Set.t)
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
  (* Any stack pointer in a lane the call reads may escape through the
     callee.  Once raised, the bit survives every later call in the sub. *)
  let lane_escapes =
    List.exists site.read_lanes ~f:(fun v ->
        not (Base.List.is_empty
               (WordSet.stack_leaves (AI.find_word word_bits env v))))
  in
  let frame_escaped = AI.frame_escaped env || lane_escapes in
  let env = if lane_escapes then AI.escape_frame env else env in
  (* Every call clears the outgoing stack-argument hull.  Once any frame
     address escaped, the simple rule clears the whole retained frame. *)
  let abs =
    frame_keep ~preserved
      ~rsp:(AI.find_word word_bits env rsp)
      ~frame_escaped ~stack_args env in
  (* The SP restores by one word on returns: the callee's ret pops
     exactly the retaddr the caller pushed.  On a stack word the +word
     lands in the offsets exactly. *)
  if site.pushed then
    AI.add_word abs ~key:rsp
      ~data:(WordSet.add (AI.find_word word_bits abs rsp)
               (WordSet.singleton
                  (Cbat_word.of_int ~width:word_bits abi.Hike_abi.word)))
  else abs
