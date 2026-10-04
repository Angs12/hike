open Bap.Std

type result = {
  program : program term;
  facts : Hike_kb.facts;
}

(** Stamps dynamic allocations and section tags, promotes eligible storage,
    and returns the emitter spec and DCE roots with the rewritten program. *)
val run :
  facts:Hike_kb.facts ->
  word:int ->
  entry:int64 ->
  spans:Hike_sections.data_span list ->
  meta:Hike_sections.sec_meta option list ->
  relative:(int64 * int64) list ->
  externals:(int64 * string) list ->
  program term ->
  result
