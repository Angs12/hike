open Bap.Std
open Bap.Std.Bil.Types

(* The Stack-Arg promotion: the layout's slots become the sub's
   promoted parameters, call sites bind the stored values, and
   promoted-slot loads read the args. *)

(* The promotion's input facts: the promoted arity and the resolved
   direct targets (the vsa pass's products). *)
type facts = {
  prom_arity : int;
  prom_resolved : Tid.t option Tid.Map.t;
}

(** The resolved target (if any) of each indirect call site: the
    caller-side half of the promotion. *)
val call_resolution :
  denote:(blk:blk term -> ?def:def term -> exp ->
          (Cbat_vsa.WordSet.t, Type.error) Result.t) ->
  lookup:(int64 -> Tid.t option) ->
  sub term -> Tid.t option Tid.Map.t

(** The promotion rewrite: the sub gains its promoted parameters as
    real BIR args, the sites' outgoing stores gain their call-arg defs,
    and singleton-resolved indirect targets become direct. *)
val promote_sub :
  addr_bits:int -> facts -> sub term -> sub term


(** One call-site binding: the outgoing slot and the storing def. *)
type site_binding = {
  sb_slot : int;
  sb_def : def term;
}

(** The promoted slot count of a finalized tree: the highest Arg_slot
    cell index + 1; 0 when the tree names none. *)

(** The per-block store-to-call-slot correspondence. *)
val site_bindings_of_sub :
  word:int ->
  sp:var ->
  denote:(blk:blk term -> ?def:def term -> exp ->
          (Cbat_vsa.WordSet.t, Type.error) Result.t) ->
  sub term ->
  site_binding list Tid.Map.t

(** The promoted slots' arity: one per word cell the tree's Arg_slot
    members name, derived from each member's own address — the binding is
    never the unit. *)

(** The per-sub rewrite driver: promotion, the storage rewrite, and
    the layout stamp. *)
val rewrite_program :
  word:int ->
  entry:int64 ->
  facts:Hike_kb.facts ->
  spans:Hike_sections.data_span list ->
  ctx:Hike_sections.ctx ->
  program term ->
  program term

