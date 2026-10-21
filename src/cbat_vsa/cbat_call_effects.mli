(* What survives a call: the one policy over the caller's words and
   frames at a call site — the preserved-set derivation from the
   callee's kill summary, the frame-keep decision, and the SP restore. *)

open Bap.Std

module AI = Cbat_ai_representation

(* The call-site facts the transfer consumes. *)
type site = {
  (* The callee's written-register (kill) summary over caller-saved
     GPRs; preserved = not in it and not a return lane.  [None] = an
     unknown or kill-all callee, or a non-ABI trap. *)
  summary : Core.Int.Set.t option;
  (* The lanes read by the call, regardless of which block last set
     them.  A Stack value in any lane raises the sub's sticky escape bit. *)
  read_lanes : var list;
}

(* What a call site reads about its callee: its published kill summary
   ([None] = any caller-saved GPR).  The caller obtains it by solving the
   callee recursively; an already-final summary is read directly. *)
type callee = Summary of Core.Int.Set.t option

val stack_arg_ranges :
  synth:Hike_synth.table ->
  abi:Hike_abi.t -> block:Bap.Std.blk Bap.Std.term -> entry:AI.t -> AI.t ->
  (Cbat_word.t * Cbat_word.t) list

(* An indirect target's callee: every code word in the target exp's
   pre-call denotation reads its lifted sub through [callee]; the call
   keeps the intersection of the solved targets' preserved sets.  Any
   unresolved target makes the whole call [Summary None]. *)
val indirect_callee :
  synth:Hike_synth.table ->
  lookup:(int64 -> Tid.t option) ->
  callee:(Tid.t -> callee) ->
  env:AI.t -> exp -> callee

(* The preserved set a callee summary derives from the base set.  A
   caller that reuses it passes it as [transfer]'s [~kept], which then
   skips its own derivation. *)
val preserved_with_summary :
  abi:Hike_abi.t -> preserved:Core.Int.Set.t -> Core.Int.Set.t -> Core.Int.Set.t

(* The caller's post-call state: the preserved caller-saved GPRs kept,
   the rest topped; the frame kept at/above the highest possible
   call-time RSP outside outgoing stack arguments, unless the sub's
   sticky escape bit requires clearing the whole retained frame.  The
   whole-memory top remains the fallback on an unbounded SP. *)
val transfer :
  ?kept:Core.Int.Set.t ->
  ?stack_args:(Cbat_word.t * Cbat_word.t) list ->
  abi:Hike_abi.t -> preserved:Core.Int.Set.t -> site:site -> AI.t -> AI.t
