(* What survives a call: the one policy over the caller's words and
   frames at a call site — the preserved-set derivation from the
   callee's kill summary, the frame-keep decision, and the SP restore. *)

open Bap.Std

module AI = Cbat_ai_representation

(* The call-site facts the transfer consumes. *)
type site = {
  (* The callee's never-written caller-saved set; [None] = an unknown
     or kill-all callee, or a non-ABI trap. *)
  summary : Var.Set.t option;
  (* The convention's integer/pointer arg lanes the call block writes —
     the escape bounding which caller-frame cells the callee may
     clobber. *)
  written_lanes : var list;
  (* The call block writes SP: the retaddr push the callee's ret pops.
     A trap pushes no retaddr and restores none. *)
  pushed : bool;
}

(* The caller's post-call state: the preserved caller-saved GPRs kept,
   the rest topped; the frame kept at/above the highest possible
   call-time RSP outside the escapes — every call alike, trap or ABI —
   with the whole-memory top as the fallback on any doubt.  A pushed
   site's SP gains one word — the popped retaddr. *)
val transfer :
  abi:Hike_abi.t -> preserved:Var.Set.t -> site:site -> AI.t -> AI.t
