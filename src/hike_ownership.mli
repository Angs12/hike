(* Ownership closure and storage-relative rewriting. *)

open Bap.Std

(** One def's rewrite facts: the access's conversion (the mem re-point)
    plus the storage-relative address forms — a value def's whole rhs,
    an access def's mem-node address. *)
type fact = {
  fr_conv : Hike_sections.conv;
  fr_bits : int;
  fr_addr : exp option;
  fr_rhs : exp option;
}

type rewrites = fact Tid.Map.t Tid.Map.t

(** The per-sub end trees, the access conversions recomputed on them,
    and the per-sub rewrite table. *)
type result = {
  sub_trees : Hike_sections.sub_tree Tid.Map.t;
  conversions : Hike_sections.conv Tid.Map.t;
  rewrites : rewrites;
}

(** Close the ownership constraints: merge only the logical ranges a
    consuming operation needs one native origin for, finalize the end
    tree once, then mint the synthetic bases. *)
val complete :
  facts:Hike_kb.facts ->
  word:int ->
  entry:int64 ->
  ctx:Hike_sections.ctx ->
  program term ->
  Hike_synth.table * result
