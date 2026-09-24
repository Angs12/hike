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
  symtab:Symtab.t option ->
  name_tid:(string * Tid.t) list ->
  sub term -> Tid.t option Tid.Map.t

(** The promotion rewrite: the sub gains its promoted parameters as
    real BIR args, the sites' outgoing stores gain their call-arg defs,
    and singleton-resolved indirect targets become direct. *)
val promote_sub :
  abi:Hike_abi.t -> facts -> sub term -> sub term


(** One call-site binding: the outgoing slot, the storing def, and
    whether the final store covers the whole cell. *)
type site_binding = {
  sb_slot : int;
  sb_def : def term;
  sb_full : bool;
}

(** The per-block store-to-call-slot correspondence. *)
val site_bindings_of_sub :
  word:int ->
  abi:Hike_abi.t ->
  sp:var ->
  denote:(blk:blk term -> ?def:def term -> exp ->
          (Cbat_vsa.WordSet.t, Type.error) Result.t) ->
  sub term ->
  site_binding list Tid.Map.t

(** The per-sub rewrite driver: promotion, the storage rewrite, and
    the layout stamp. *)
val rewrite_program :
  word:int ->
  entry:int64 ->
  facts:Hike_kb.facts ->
  symtab:Symtab.t option ->
  spans:Hike_sections.data_span list ->
  ctx:Hike_sections.ctx ->
  program term ->
  program term

