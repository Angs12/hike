(* A function's summary: the only fact a caller reads about a callee,
   published once the callee's own fixpoint is final (ADR 0027). *)
open Bap.Std

(** [written] is the may-write set over the caller-saved registers'
    interned ids ([None]: any of them); [returns] is whether control may
    come back to the caller. *)
type t = { written : Core.Int.Set.t option; returns : bool }

(** Nothing proven: anything written, control may come back. *)
val unknown : t

(** The summary of a solved sub, over its reachable blocks.  Each exit
    contributes: a return comes back; a direct or resolved transfer
    joins the callee's summary ([callee] for a sub, [slot] for the
    external a linker slot names, [lookup] for an entry address), a tail
    transfer coming back iff the callee does; a trap writes anything and
    does not exit; an unresolved transfer is unknown.  A return whose RSP
    is not entry + word draws a fixed diagnostic; the ABI restore is
    assumed. *)
val of_solved :
  abi:Hike_abi.t ->
  callee:(Tid.t -> t option) ->
  slot:(int64 -> t option) ->
  lookup:(int64 -> Tid.t option) ->
  foreign_slots:Core.Int64.Set.t ->
  block_addrs:Tid.t Addr.Map.t ->
  envs:(Cbat_vsa.AI.t * Cbat_vsa.AI.t) Tid.Map.t ->
  sub term ->
  t
