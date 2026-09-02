(* The per-stage profiling counters — DEBUG adapter (the vsa-debug profile).

   The Q6 harness: the fixpoint's per-visit cost is exactly
   (denotation + join + equal + widen) plus the deep walk, and nothing in
   the tree could previously attribute time between them. That gap is how
   three separate changes this session got reported as "wins" while
   sitting inside measurement noise.

   Selected ONLY under --profile vsa-debug (src/cbat_vsa/dune); every
   other profile links [cbat_vsa_stages_prod.ml], the no-op twin with
   the same interface. AGENTS.md §6.

   L2 (2026-09-02) — the WALK-SCHEDULE metrics + the SCAFFOLD timer:

   - [walk_pops]: Kildall POP counter, incremented in [refine_edge]'s
     transfer closure (it fires exactly once per pop). The schedule
     metric: K = pops / distinct blocks visited (1.0 = the theoretical
     floor of the least fixpoint).
   - [walk_blocks]: distinct blocks visited, read per walk from the
     walk's own read-set accumulator (the ticket-03 [reads] ref — a
     conservative superset, but the visited set is what it measures).
   - [walk_truncs]: walks that stopped AT the 256-pop cap (Graphlib
     stops when iters hits [~steps] — a SILENT truncation; the sound
     but coarser live sets of a truncated walk are the precision lane
     the L2 schedule change exists to close).
   - [Scaffold]: the per-visit engine glue that sits in NO stage bucket
     today (process_vertex's pred listing, the C1 read-set bookkeeping,
     the sol snapshot creation, the version bumps) — the untimed-slice
     attribution candidate. *)
let enabled = true

let denote_calls = ref 0
let join_calls = ref 0
let equal_calls = ref 0
let widen_calls = ref 0
let walk_calls = ref 0

let t_denote = ref 0.
let t_join = ref 0.
let t_equal = ref 0.
let t_widen = ref 0.
let t_walk = ref 0.

let walk_pops = ref 0
let walk_blocks = ref 0
let walk_truncs = ref 0
let walk_max_pops = ref 0

let t_scaffold = ref 0.
let scaffold_calls = ref 0

let t_glue = ref 0.
let glue_calls = ref 0

(* The GC snapshot at [reset] — the allocation-delta baseline for the
   sub-attribution's GC hypothesis (see [report]). *)
let gc0 = ref (Gc.quick_stat ())

let reset () =
  denote_calls := 0; join_calls := 0; equal_calls := 0; widen_calls := 0;
  walk_calls := 0;
  t_denote := 0.; t_join := 0.; t_equal := 0.; t_widen := 0.;
  t_walk := 0.;
  walk_pops := 0; walk_blocks := 0; walk_truncs := 0; walk_max_pops := 0;
  t_scaffold := 0.; scaffold_calls := 0;
  t_glue := 0.; glue_calls := 0;
  gc0 := Gc.quick_stat ()

(* [time which f]: run [f], accumulating its wall time into [which]'s
   total. The clock read is [Unix.gettimeofday] (~50ns) — negligible
   against the operations being timed (a block denotation, an AI.join,
   a widening). *)
let time (which : [ `Denote | `Equal | `Glue | `Join | `Scaffold | `Walk | `Widen ])
    (f : unit -> 'a) : 'a =
  let t0 = Unix.gettimeofday () in
  let r = f () in
  let dt = Unix.gettimeofday () -. t0 in
  (match which with
   | `Denote -> incr denote_calls; t_denote := !t_denote +. dt
   | `Join -> incr join_calls; t_join := !t_join +. dt
   | `Equal -> incr equal_calls; t_equal := !t_equal +. dt
   | `Widen -> incr widen_calls; t_widen := !t_widen +. dt
   | `Walk -> incr walk_calls; t_walk := !t_walk +. dt
   | `Scaffold -> incr scaffold_calls; t_scaffold := !t_scaffold +. dt
   | `Glue -> incr glue_calls; t_glue := !t_glue +. dt);
  r

(* [bump_walk_pops n]: record [n] pops of ONE walk's Kildall (the
   closure counts them locally and commits at walk end — one call per
   walk, not per pop, so the debug adapter's cost stays out of the
   Kildall loop itself). [blocks] is the walk's distinct visited count
   ([|reads|]); [truncated] is whether the walk stopped at the 256 cap. *)
let bump_walk_pops ~(pops : int) ~(blocks : int) ~(truncated : bool) () : unit =
  walk_pops := !walk_pops + pops;
  walk_blocks := !walk_blocks + blocks;
  if truncated then incr walk_truncs;
  if pops > !walk_max_pops then walk_max_pops := pops

(* [report label]: the per-stage totals, call counts, the walk-schedule
   census, and the GC allocation deltas since [reset] (the L2
   sub-attribution's GC hypothesis: if the glue remainder is mostly
   major-GC slices landing in the mutator, the major-allocated delta
   correlates with it). *)
let gc_minor_words () =
  (Gc.quick_stat ()).Gc.minor_words -. (!gc0).Gc.minor_words
let gc_major_words () =
  (Gc.quick_stat ()).Gc.major_words -. (!gc0).Gc.major_words
let gc_promoted_words () =
  (Gc.quick_stat ()).Gc.promoted_words -. (!gc0).Gc.promoted_words

let report (label : string) : unit =
  Printf.printf
    "STAGES %s: denote %7.3fs/%d  join %7.3fs/%d  equal %7.3fs/%d  \
     widen %7.3fs/%d  walk %7.3fs/%d  scaffold %7.3fs/%d  glue %7.3fs/%d\n\
     WALKS %s: pops %d  blocks %d  truncs %d  max_pops %d\n\
     GC %s: minor %.0f  major %.0f  promoted %.0f\n%!"
    label !t_denote !denote_calls !t_join !join_calls !t_equal !equal_calls
    !t_widen !widen_calls !t_walk !walk_calls !t_scaffold !scaffold_calls
    !t_glue !glue_calls
    label !walk_pops !walk_blocks !walk_truncs !walk_max_pops
    label (gc_minor_words ()) (gc_major_words ()) (gc_promoted_words ())
