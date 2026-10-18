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
  (* The call block writes SP: the retaddr push the callee's ret pops.
     A trap pushes no retaddr and restores none. *)
  pushed : bool;
}

(* What a call site reads about its callee: its published kill summary
   ([None] = any caller-saved GPR), or [Blocked] while the callee has no
   summary yet — nothing flows past the call until it has one, so a
   paused solve resumes from a state below its final one. *)
type callee = Summary of Core.Int.Set.t option | Blocked

val stack_arg_ranges :
  abi:Hike_abi.t -> block:Bap.Std.blk Bap.Std.term -> entry:AI.t -> AI.t ->
  (Cbat_word.t * Cbat_word.t) list

(* An indirect target's callee: the target exp's denotation in the
   pre-call env — a singleton word naming a lifted sub through [lookup]
   reads that sub through [callee]; anything unresolved is
   [Summary None]. *)
val indirect_callee :
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
