(* test_cbat/precision_probe.ml — PRECISION MEASUREMENT driver for the
   CBAT VSA port (src/cbat_vsa/).

   Usage:  dune exec test_cbat/precision_probe.exe -- <binary> [<binary> ...]

   For each binary on argv:
     - load it as a BAP Project (Project.create (Project.Input.file
       ~loader:"llvm" ~filename:path), the corpus_watch shape);
     - for EACH sub, run the full VSA fixpoint exactly the way
       corpus_watch.ml does (Relevance.analyze tagging, then
       Vsa.static_graph_vsa [] prog' sub' with the entry solution
       below);
     - then WALK every block of the (tagged) sub in def order,
       re-applying Vsa.denote_def sequentially from the fixpoint's
       per-block entry state (Solution.get sol (Term.tid b)), and
       classify every def's abstract value set and every Load/Store
       address value set into precision buckets.

   RESTRICTION is ALWAYS ON: run_sub always calls Relevance.analyze.
   The old HIKE_VSA_RESTRICTION=0 toggle was removed — an OFF run
   crashes in the single-sub shape (callee recursion into absent subs),
   so the toggle was cosmetic.

   ANCHOR MODE: removed 2026-08-13 (with the VSA's unanchored-mode
   flag) — the frame-correct rewrite is ALWAYS on: the fixpoint keys
   stack cells by offset-from-origin (the derived frame facts — the
   in-state relation, [AI.frame_of]).  The single default entry is
   [Vsa.init_sol sub'] (AI.top).  Known residual: the crt `_start`
   argument-slot reads after the non-affine stack-alignment
   (`and rsp, -16` — RSP's value-set becomes an infinite step-16 CLP;
   the [rsp+c] keys are sound-but-wide there).

   DIAGNOSTIC MODE (L2a): HIKE_VSA_DIAG_BOTTOM=1 emits, during the
   collect_stats recompute walk, one line per word def whose lhs value
   classifies as bottom (BOTH live and dead — the input_bottom flag
   distinguishes them):

     DIAG\t<binary>\t<sub>\t<blk_tid>\t<def_tid>\t<input_bottom:0|1>
       \t<tagged:0|1>\t<lhs>\t<kind>\t<op1>\t<op2>

   where binary = basename of the input file, blk_tid/def_tid =
   Tid.to_string, input_bottom = the containing block's AI.equal st0
   AI.bottom flag, tagged = Term.has_attr d Cbat_vsa_utils.relevant,
   lhs = Var.name (Def.lhs d), kind = the def's Bil shape (the Bil
   binop constructor name as written in the vendored code — PLUS/MINUS/
   TIMES/DIVIDE/SDIVIDE/MOD/SMOD/LSHIFT/RSHIFT/ARSHIFT/AND/OR/XOR/EQ/
   NEQ/LT/LE/SLT/SLE — or "load", or "cast:<op>" with op in
   UNSIGNED/SIGNED/HIGH/LOW, else "other"), and op1/op2 = the operand
   value-set class at the state BEFORE the def (denote_imm_exp):
   "empty" (is_bottom, or cardinality 0), "exact" (cardn 1), "fin:k"
   (cardn k, 2 <= k <= 64), "big" (cardn > 64), "top" (is_top), "err"
   (denote error).  For a load def op1 = the ADDRESS class and op2 =
   "n/a" (the loaded value is the def's own bottom value — the empty
   likely comes from the memory cell); for every other kind op1 = op2 =
   "n/a".  After each sub's walk one per-sub summary line is emitted:

     DIAG_SUM\t<binary>\t<sub>\t<bottom_live_total>\t<bottom_dead_total>

   whose totals are consistent with the def_bottom_live/
   def_bottom_dead columns exactly (same word-lhs bottom population,
   same input_bottom split).  When HIKE_VSA_DIAG_BOTTOM is unset the
   probe's output is BYTE-IDENTICAL to the standard 37-column format
   (the diagnostic is env-gated: no column changes, no extra lines).

   TSV OUTPUT (one line per sub, 37 tab-separated columns; flush stdout
   after every line):

     binary, sub, sub_ms,                                        (3)
     def_exact, def_b2_3, def_b4_8, def_b9_64, def_b65p,
       def_top, def_bottom_live, def_bottom_dead,                   (8, all defs)
     def_tagged_exact, def_tagged_b2_3, def_tagged_b4_8,
       def_tagged_b9_64, def_tagged_b65p, def_tagged_top,
       def_tagged_bottom_live, def_tagged_bottom_dead,
       def_tagged_count,                                            (9, tagged subset + count)
     ld_exact, ld_bounded, ld_top, ld_bottom_live, ld_bottom_dead,
       ld_denote_err,                                               (6)
     ldstk_exact, ldstk_bounded, ldstk_top, ldstk_bottom_live,
       ldstk_bottom_dead,                                           (5)
     ldstk_w_b64, ldstk_w_4k, ldstk_w_2m, ldstk_w_big, ldstk_w_max   (5)

   where
     sub_ms          fixpoint wall time in integer milliseconds
                     (Unix.gettimeofday around static_graph_vsa ONLY,
                     the corpus_watch.ml:73-78 idiom)
     def_*           word defs by value-set cardinality: 1 = exact,
                     [2,3] = b2_3, [4,8] = b4_8, [9,64] = b9_64,
                     > 64 (or un-convertible) = b65p; top = TOP (the
                     fixpoint runs to convergence — the former E7
                     budget-expired all-top degradation was removed;
                     all-top now reflects genuinely-unbounded values,
                     expected, not a bug); bottom = BOTTOM value set,
                     split by
                     the block's ENTRY state: bottom_dead when the
                     entry state is bottom (AI.equal st0 AI.bottom),
                     else bottom_live.  The cardinality word converts
                     with [Word.to_int] (bap_bitvector.mli:51 —
                     Or_error).  There is NO bitwidth guard: a
                     FinSet's/singleton's bitwidth is the ELEMENT width,
                     so a 64-bit singleton's cardinality is the small
                     word 1 and classifies as exact.
     def_tagged_*    the same 8 buckets restricted to defs tagged
                     Cbat_vsa_utils.relevant (Term.has_attr d
                     Cbat_vsa_utils.relevant); def_tagged_count = the
                     number of tagged word defs (the 8 tagged buckets
                     sum to it, and def_tagged_count <= the all-defs
                     series total).
     ld_*            Load/Store ADDRESS value sets: exact (cardinality
                     1), bounded (finite non-top, any size), top,
                     bottom (the empty FinSet — Ws.is_bottom checked
                     FIRST), denote_err (denote_imm_exp on the address
                     failed, a type error).  The bottom bucket is split
                     by the def's block INPUT state (L1, the same
                     discrimination as the def series): bottom_dead
                     when the block's ENTRY state is bottom
                     (AI.equal st0 AI.bottom — a stranded in-degree-0
                     block in the isolated-sub DAG: init_sol seeds only
                     the first block with AI.bottom, cbat_vsa.ml:597-
                     608, and pseudo-node removal strands the others,
                     :765-766), else bottom_live.
     ldstk_*         the stack-flagged address subset (see below) of
                     the matching ld_* bucket.
     ldstk_w_*       window-size bucket COUNTS over the stack-flagged
                     FINITE NON-TOP (exact or bounded) addresses, where
                     window = the set's SIGNED span (max_elem_signed -
                     min_elem_signed + 1 computed on words — the
                     stack-offset interpretation, matching the
                     production offsets' signed conversion in
                     hike_vsa.ml):
                       w_b64: window <= 64
                       w_4k:  window <= 4096
                       w_2m:  window <= 2^20 = 1048576
                       w_big: window > 2^20
                     Classification: bitwidth > 64 -> w_big; else
                     convert the window word via [Word.to_int64] —
                     NOTE the conversion is SIGNED (bitvec.ml:411-415:
                     a value in (max_signed, max_unsigned] converts via
                     signed_extract to a NEGATIVE int64), so a negative
                     result means window >= 2^63 -> w_big; a ZERO
                     result is the full-domain signed span (wrapped) ->
                     w_big; otherwise compare the int64 against
                     64/4096/1048576.  The signed span is the fix for
                     the straddling-set artifact: a set of small
                     positives ∪ negatives (the -O0 loop-index
                     offsets) has a huge UNSIGNED span but a small
                     signed one.
     ldstk_w_max     the largest window seen (int64; negative
                     conversions capped at Int64.max_int, as before).

   A def's lhs counts as a "word def" iff its type is Type.Imm (Type.Mem
   and Type.Unk lhs are skipped; there is no width to index find_word).
   The stack flag on an address is: ANY free var of the address exp has
   name "RSP"/"RBP", OR has a def in this sub tagged
   Cbat_vsa_utils.relevant (the precomputed var->defs map, base-normalized
   with Var.base — the Var.same env-key idiom, cbat_vsa.ml:637-641).

   After all subs of a binary, one "BIN" rollup line: the summed columns
   (def_tagged_count summed too; ldstk_w_max = the max), plus TWO
   percentages with 2 decimals ("n/a" on div-by-zero), printed in this
   order:
     ldstk_exact_pct_filtered = ldstk_exact/(ldstk_exact+ldstk_bounded+
       ldstk_top+ldstk_bottom_live)  — the L1 PRIMARY metric: the
       FILTERED population excludes dead-block bottoms;
     ldstk_exact_pct = ldstk_exact/(ldstk_exact+ldstk_bounded+ldstk_top+
       ldstk_bottom_live+ldstk_bottom_dead) — the full population, dead
       bottoms included (the pre-L1 metric, kept as secondary).
   Exit code: 0 if no fixpoint crash and every binary loaded; 1
   otherwise (corpus_watch's outcome tracking).  A final TOTAL line is
   printed. *)

open Bap.Std

(* Same module aliases as the D4-9 test / corpus_watch (test_cbat.ml:44-46);
   the fixpoint entry point is Cbat_vsa.static_graph_vsa. *)
module AI = Cbat_vsa.AI
module Mem = Cbat_vsa.Mem
module Vsa = Cbat_vsa

(* The set-composite domain of the AI word values; the [idx] passed to
   AI.find_word is the bitwidth (cbat_ai_representation.mli:25). *)
module Ws = Cbat_clp_set_composite
module W = Word

(* Same relevance-restriction hookup as corpus_watch: each sub is run
   through [Hike_vsa_relevance.analyze] before the fixpoint (it tags the
   relevant defs and arms the restriction switch).  run_sub ALWAYS calls
   analyze — the probe is restriction-ON-only; the old
   HIKE_VSA_RESTRICTION=0 toggle was removed (an OFF run crashes in the
   single-sub shape: callee recursion into absent subs).
   [Hike_vsa_relevance] is hike's production relevance pass
   (src/hike_vsa_relevance.ml), reached through the wrapped [hike]
   library's flat module name; [sp] comes from the project target. *)
module Relevance = Hike.Relevance

(* [diag_on]: default OFF; HIKE_VSA_DIAG_BOTTOM=1 enables the L2a
   diagnostic mode — one DIAG line per bottom word def plus a per-sub
   DIAG_SUM line (see the header comment).  When OFF the probe's output
   is byte-identical to the standard 37-column format. *)
let diag_on () : bool =
  match Sys.getenv_opt "HIKE_VSA_DIAG_BOTTOM" with
  | Some "1" -> true
  | _ -> false

(* [init_sol_of sub']: the fixpoint entry solution — [Vsa.init_sol
   sub'] (the production default, AI.top — the anchored-entry
   regression mode was removed 2026-08-13). *)
let init_sol_of (sub' : sub term) : Vsa.vsa_sol =
  Vsa.init_sol sub'

let () = Printexc.record_backtrace true

let describe_exn (e : exn) : string =
  match e with
  | Assert_failure (file, line, col) ->
    Printf.sprintf "Assert_failure (%s:%d:%d)" file line col
  | Failure msg -> Printf.sprintf "Failure(%s)" msg
  | Invalid_argument msg -> Printf.sprintf "Invalid_argument(%s)" msg
  | _ -> Printexc.to_string e

(* ------------------------------------------------------------------ *)
(* Classification buckets. *)

(* Def value-set buckets: the bottom bucket is split by the block's
   entry state (bottom_dead when the entry state is bottom, else
   bottom_live) — fix 4. *)
type def_bucket =
  [ `Exact | `B2_3 | `B4_8 | `B9_64 | `B65p | `Top
  | `Bottom_live | `Bottom_dead ]

(* Load/Store address-set buckets: the bottom bucket is split by the
   def's block INPUT state (L1): bottom_dead when the block's entry
   state is bottom (a stranded in-degree-0 block), else bottom_live. *)
type ld_bucket =
  [ `Exact | `Bounded | `Top | `Bottom_live | `Bottom_dead ]

(* Window-size buckets over stack-flagged finite non-top addresses
   (fix 6). *)
type win_bucket = [ `W_b64 | `W_4k | `W_2m | `W_big ]

(* ------------------------------------------------------------------ *)
(* Per-sub statistics record. *)

module Sub_stats = struct
  type t = {
    sname : string;
    mutable sub_ms : int;
    (* all-defs series (8 buckets) *)
    mutable def_exact : int;
    mutable def_b2_3 : int;
    mutable def_b4_8 : int;
    mutable def_b9_64 : int;
    mutable def_b65p : int;
    mutable def_top : int;
    mutable def_bottom_live : int;
    mutable def_bottom_dead : int;
    (* tagged-defs-only series (8 buckets + count) *)
    mutable def_tagged_exact : int;
    mutable def_tagged_b2_3 : int;
    mutable def_tagged_b4_8 : int;
    mutable def_tagged_b9_64 : int;
    mutable def_tagged_b65p : int;
    mutable def_tagged_top : int;
    mutable def_tagged_bottom_live : int;
    mutable def_tagged_bottom_dead : int;
    mutable def_tagged_count : int;
    (* load/store address series (6) *)
    mutable ld_exact : int;
    mutable ld_bounded : int;
    mutable ld_top : int;
    mutable ld_bottom_live : int;
    mutable ld_bottom_dead : int;
    mutable ld_denote_err : int;
    (* stack-flagged address subset (5) *)
    mutable ldstk_exact : int;
    mutable ldstk_bounded : int;
    mutable ldstk_top : int;
    mutable ldstk_bottom_live : int;
    mutable ldstk_bottom_dead : int;
    (* window-size buckets (5) *)
    mutable ldstk_w_b64 : int;
    mutable ldstk_w_4k : int;
    mutable ldstk_w_2m : int;
    mutable ldstk_w_big : int;
    mutable ldstk_w_max : int64;
  }

  let create (name : string) : t =
    { sname = name; sub_ms = 0;
      def_exact = 0; def_b2_3 = 0; def_b4_8 = 0; def_b9_64 = 0;
      def_b65p = 0; def_top = 0; def_bottom_live = 0;
      def_bottom_dead = 0;
      def_tagged_exact = 0; def_tagged_b2_3 = 0; def_tagged_b4_8 = 0;
      def_tagged_b9_64 = 0; def_tagged_b65p = 0; def_tagged_top = 0;
      def_tagged_bottom_live = 0; def_tagged_bottom_dead = 0;
      def_tagged_count = 0;
      ld_exact = 0; ld_bounded = 0; ld_top = 0; ld_bottom_live = 0;
      ld_bottom_dead = 0; ld_denote_err = 0;
      ldstk_exact = 0; ldstk_bounded = 0; ldstk_top = 0;
      ldstk_bottom_live = 0; ldstk_bottom_dead = 0;
      ldstk_w_b64 = 0; ldstk_w_4k = 0; ldstk_w_2m = 0; ldstk_w_big = 0;
      ldstk_w_max = 0L }

  (* [add_def s tagged b]: count a word def into the all-defs series
     and, when [tagged] (the def carries the Cbat_vsa_utils.relevant
     tag), into the tagged-defs series too (def_tagged_count bumps for
     every tagged word def — fix 3). *)
  let add_def (s : t) (tagged : bool) (b : def_bucket) : unit =
    (match b with
     | `Exact -> s.def_exact <- s.def_exact + 1
     | `B2_3 -> s.def_b2_3 <- s.def_b2_3 + 1
     | `B4_8 -> s.def_b4_8 <- s.def_b4_8 + 1
     | `B9_64 -> s.def_b9_64 <- s.def_b9_64 + 1
     | `B65p -> s.def_b65p <- s.def_b65p + 1
     | `Top -> s.def_top <- s.def_top + 1
     | `Bottom_live -> s.def_bottom_live <- s.def_bottom_live + 1
     | `Bottom_dead -> s.def_bottom_dead <- s.def_bottom_dead + 1);
    if tagged then begin
      s.def_tagged_count <- s.def_tagged_count + 1;
      match b with
      | `Exact -> s.def_tagged_exact <- s.def_tagged_exact + 1
      | `B2_3 -> s.def_tagged_b2_3 <- s.def_tagged_b2_3 + 1
      | `B4_8 -> s.def_tagged_b4_8 <- s.def_tagged_b4_8 + 1
      | `B9_64 -> s.def_tagged_b9_64 <- s.def_tagged_b9_64 + 1
      | `B65p -> s.def_tagged_b65p <- s.def_tagged_b65p + 1
      | `Top -> s.def_tagged_top <- s.def_tagged_top + 1
      | `Bottom_live ->
        s.def_tagged_bottom_live <- s.def_tagged_bottom_live + 1
      | `Bottom_dead ->
        s.def_tagged_bottom_dead <- s.def_tagged_bottom_dead + 1
    end

  let add_ld (s : t) (stack : bool) (b : ld_bucket) : unit =
    match b with
    | `Exact ->
      s.ld_exact <- s.ld_exact + 1;
      if stack then s.ldstk_exact <- s.ldstk_exact + 1
    | `Bounded ->
      s.ld_bounded <- s.ld_bounded + 1;
      if stack then s.ldstk_bounded <- s.ldstk_bounded + 1
    | `Top ->
      s.ld_top <- s.ld_top + 1;
      if stack then s.ldstk_top <- s.ldstk_top + 1
    | `Bottom_live ->
      s.ld_bottom_live <- s.ld_bottom_live + 1;
      if stack then s.ldstk_bottom_live <- s.ldstk_bottom_live + 1
    | `Bottom_dead ->
      s.ld_bottom_dead <- s.ld_bottom_dead + 1;
      if stack then s.ldstk_bottom_dead <- s.ldstk_bottom_dead + 1

  let add_window (s : t) (b : win_bucket) : unit =
    match b with
    | `W_b64 -> s.ldstk_w_b64 <- s.ldstk_w_b64 + 1
    | `W_4k -> s.ldstk_w_4k <- s.ldstk_w_4k + 1
    | `W_2m -> s.ldstk_w_2m <- s.ldstk_w_2m + 1
    | `W_big -> s.ldstk_w_big <- s.ldstk_w_big + 1
end

type outcome =
  | Ok of Sub_stats.t
  | Crash of string * string (* exception description * backtrace *)

(* ------------------------------------------------------------------ *)
(* Classification. *)

(* [classify_def ws]: a def value set into its precision bucket.
   - TOP/BOTTOM first (the composite's bottom is a FinSet — checked
     before the cardinality conversion; a [`Bottom] here is resolved
     by the caller to bottom_live/bottom_dead from the block's entry
     state).
   - NO bitwidth guard (the old "> 32 -> b65p" rule was a bug: a
     FinSet's/singleton's bitwidth is the ELEMENT width, so every
     64-bit singleton was misclassified): the cardinality is a word
     holding the count, converted with [Word.to_int]
     (bap_bitvector.mli:51 — Or_error); a count that fits an OCaml int
     buckets by size, anything else (>= 2^62, or conversion failure) is
     b65p. *)
let classify_def (ws : Ws.t) :
    [ `Exact | `B2_3 | `B4_8 | `B9_64 | `B65p | `Top | `Bottom ] =
  if Ws.is_top ws then `Top
  else if Ws.is_bottom ws then `Bottom
  else
    let cardn = Ws.cardinality ws in
    match W.to_int cardn with
    | Error _ -> `B65p
    | Ok n ->
      if n = 1 then `Exact
      else if n <= 3 then `B2_3
      else if n <= 8 then `B4_8
      else if n <= 64 then `B9_64
      else `B65p

(* [classify_ld ws input_bottom]: a Load/Store address value set into
   ld_exact (cardinality 1), ld_bounded (finite non-top, any size),
   ld_top or the split bottom bucket.  The bottom check comes FIRST
   (the empty FinSet is the composite's bottom); there is NO bitwidth
   guard — a huge finite set (finite, not convertible) is still
   ld_bounded.  [input_bottom] is the containing block's entry-state
   flag (L1): a bottom value set is bottom_dead iff the block's entry
   state is bottom, else bottom_live. *)
let classify_ld (ws : Ws.t) (input_bottom : bool) : ld_bucket =
  if Ws.is_bottom ws then
    (if input_bottom then `Bottom_dead else `Bottom_live)
  else if Ws.is_top ws then `Top
  else
    match W.to_int (Ws.cardinality ws) with
    | Ok 1 -> `Exact
    | _ -> `Bounded

(* [classify_operand ws]: the op1/op2 class of an operand value-set —
   the probe's bottom/top/cardinality reading, using the SAME
   primitives as [classify_def]/[classify_ld] (Ws.is_top, Ws.is_bottom,
   Ws.cardinality, Word.to_int — no new bucket semantics): "empty"
   (is_bottom, or cardinality 0), "exact" (cardn 1), "fin:k" (cardn k,
   2 <= k <= 64), "big" (cardn > 64, or a cardn that does not fit an
   OCaml int), "top". *)
let classify_operand (ws : Ws.t) : string =
  if Ws.is_top ws then "top"
  else if Ws.is_bottom ws then "empty"
  else
    match W.to_int (Ws.cardinality ws) with
    | Error _ -> "big"
    | Ok 0 -> "empty"
    | Ok 1 -> "exact"
    | Ok k when k <= 64 -> Printf.sprintf "fin:%d" k
    | Ok _ -> "big"

(* [binop_name op]: the Bil binop constructor name as written in the
   vendored BIL code (bap_bil.ml:23-43 — the hike fork's uppercase
   names). *)
let binop_name (op : Bil.binop) : string =
  match op with
  | Bil.PLUS -> "PLUS"
  | Bil.MINUS -> "MINUS"
  | Bil.TIMES -> "TIMES"
  | Bil.DIVIDE -> "DIVIDE"
  | Bil.SDIVIDE -> "SDIVIDE"
  | Bil.MOD -> "MOD"
  | Bil.SMOD -> "SMOD"
  | Bil.LSHIFT -> "LSHIFT"
  | Bil.RSHIFT -> "RSHIFT"
  | Bil.ARSHIFT -> "ARSHIFT"
  | Bil.AND -> "AND"
  | Bil.OR -> "OR"
  | Bil.XOR -> "XOR"
  | Bil.EQ -> "EQ"
  | Bil.NEQ -> "NEQ"
  | Bil.LT -> "LT"
  | Bil.LE -> "LE"
  | Bil.SLT -> "SLT"
  | Bil.SLE -> "SLE"

(* [cast_name ct]: the Bil cast constructor name (bap_bil.ml:10-15). *)
let cast_name (ct : Bil.cast) : string =
  match ct with
  | Bil.UNSIGNED -> "UNSIGNED"
  | Bil.SIGNED -> "SIGNED"
  | Bil.HIGH -> "HIGH"
  | Bil.LOW -> "LOW"

(* [window_metric_of ws]: for a finite non-top word set, the window-size
   bucket of the set's SPAN (computed on words — [Word.sub]/[Word.add])
   plus the window value as an int64 for the ldstk_w_max accumulator
   (None when no finite window exists, e.g. bitwidth > 64).

   The span is the SIGNED span ([min_elem_signed]..[max_elem_signed])
   — the stack-offset interpretation, matching the production offsets
   (hike_vsa.ml's classify/bounds_of convert the elements via
   [Word.to_int64], signed; the emitter's region spans consume the
   signed (lo, hi)).  A set straddling the sign boundary (small
   positives ∪ negatives — the -O0 loop-index offsets) has a huge
   UNSIGNED span but a small signed one; the unsigned reading is the
   w_big artifact (fix 6 + the signed-span fix).

   Classification: bitwidth > 64 -> w_big; else convert the window
   word via [Word.to_int64] — NOTE the conversion is SIGNED
   (bitvec.ml:411-415: a value in (max_signed, max_unsigned] converts
   via signed_extract to a NEGATIVE int64 rather than raising), so a
   negative result means span >= 2^63 -> w_big; a ZERO result is the
   full-domain signed span (the difference wrapped) -> w_big;
   otherwise compare the int64 against 64 / 4096 / 1048576 (2^20). *)
let window_metric_of (ws : Ws.t) : win_bucket * int64 option =
  if Ws.bitwidth ws > 64 then (`W_big, None)
  else
    match Ws.min_elem_signed ws, Ws.max_elem_signed ws with
    | Some mn, Some mx ->
      let w = Ws.bitwidth ws in
      let win = W.add (W.sub mx mn) (W.one w) in
      (match W.to_int64 win with
       | Ok v when v < 0L -> (`W_big, Some Int64.max_int)
       | Ok 0L -> (`W_big, Some Int64.max_int)
       | Ok v ->
         (if v <= 64L then `W_b64
          else if v <= 4096L then `W_4k
          else if v <= 1048576L then `W_2m
          else `W_big), Some v
       | Error _ -> (`W_big, Some Int64.max_int))
    | _ -> (`W_big, None)

(* ------------------------------------------------------------------ *)
(* Per-sub measurement. *)

(* [addr_exp_of_rhs e]: the ADDRESS argument of a Load/Store def rhs —
   BOTH BIL forms: `v := load(addr, ...)` and bare `store(addr, v, ...)`
   (a def whose rhs is Bil.Store).  Copied from
   hike_vsa_relevance.ml:58-62. *)
let addr_exp_of_rhs (e : exp) : exp option =
  match e with
  | Bil.Load (_, a, _, _) -> Some a
  | Bil.Store (_, a, _, _, _) -> Some a
  | _ -> None

(* [diag_bottom bname sub' b d input_bottom tagged st_before]: one L2a
   DIAG line for a word def whose lhs value classifies as bottom.  The
   operand classes come from [denote_imm_exp] at the state BEFORE the
   def (the same state the fixpoint used to denote it). *)
let diag_bottom (bname : string) (sub' : sub term) (b : blk term)
    (d : def term) (input_bottom : bool) (tagged : bool)
    (frame : Vsa.frame option) (st_before : AI.t) : unit =
  let class_of (e : exp) : string =
    match Vsa.denote_imm_exp e st_before with
    | Error _ -> "err"
    | Ok ws -> classify_operand ws in
  let kind, op1, op2 =
    match Def.rhs d with
    | Bil.BinOp (op, x, y) -> binop_name op, class_of x, class_of y
    | Bil.Load (_, a, _, _) ->
      "load", class_of (Vsa.rewrite_addr frame a), "n/a"
    | Bil.Cast (ct, _, _) -> "cast:" ^ cast_name ct, "n/a", "n/a"
    | _ -> "other", "n/a", "n/a" in
  Printf.printf "DIAG\t%s\t%s\t%s\t%s\t%d\t%d\t%s\t%s\t%s\t%s\n"
    bname (Sub.name sub') (Tid.to_string (Term.tid b))
    (Tid.to_string (Term.tid d))
    (if input_bottom then 1 else 0) (if tagged then 1 else 0)
    (Var.name (Def.lhs d)) kind op1 op2;
  flush stdout

(* [collect_stats bname sub' sol]: walk the (analyze-tagged) sub's
   blocks in def order, re-applying [Vsa.denote_def] sequentially from
   the fixpoint's per-block entry state, and classify.  [bname] is the
   binary basename, used only by the L2a DIAG lines. *)
let collect_stats (bname : string) (sub' : sub term)
    (sol : Vsa.vsa_sol) (tags : Vsa.vsa_sol) : Sub_stats.t =
  let s = Sub_stats.create (Sub.name sub') in
  (* L2a diagnostic counters: all bottom word defs, live vs dead (the
     DIAG_SUM totals must match the def_bottom_live/def_bottom_dead
     columns — same population, same split). *)
  let bottom_live = ref 0 in
  let bottom_dead = ref 0 in
  (* Precomputed once per sub: var (base-normalized) -> its defs of sub'.
     Normalization: [Var.base] keys, compared structurally — the
     [Var.same] env-key idiom (cbat_vsa.ml:637-641: [same x y] iff
     [equal (base x) (base y)]). *)
  let var_defs : (var, def term list) Hashtbl.t = Hashtbl.create 64 in
  Term.enum blk_t sub'
  |> Seq.iter ~f:(fun b ->
      Term.enum def_t b
      |> Seq.iter ~f:(fun d ->
          let v = Var.base (Def.lhs d) in
          let ds = Option.value ~default:[] (Hashtbl.find_opt var_defs v) in
          Hashtbl.replace var_defs v (d :: ds)));
  (* [has_relevant_def v]: does v have a def df in this sub tagged
     [Cbat_vsa_utils.relevant]?  The stack flag: a var is stack iff its
     name is RSP/RBP or it has a relevant def. *)
  let has_relevant_def (v : var) : bool =
    let v = Var.base v in
    match Hashtbl.find_opt var_defs v with
    | None -> false
    | Some ds -> List.exists (fun df -> Term.has_attr df Cbat_vsa_utils.relevant) ds in
  let is_stack_addr (a : exp) : bool =
    Exp.free_vars a
    |> Core.Set.exists ~f:(fun v ->
        let n = Var.name v in
        String.equal n "RSP" || String.equal n "RBP" || has_relevant_def v) in
  Term.enum blk_t sub'
  |> Seq.iter ~f:(fun b ->
      (* Per-block entry state from the fixpoint solution (the fixpoint
         runs to convergence — the former E7 budget-expired all-top
         degradation was removed; handled gracefully by the buckets). *)
      (* M6 (MIGRATED, ticket 02) — the per-block TAG state is the block's
         IN-state in the converged solution (the fused fixpoint refines
         the per-edge states inline; [tags = sol]): the walk's addresses
         are denoted with the IN-state so the loop-body dynamic-index
         accesses carry the index's iterate constraint (the w_big class
         leaves the bucket). *)
      let st0 = Graphlib.Std.Solution.get tags (Term.tid b) in
      (* WYSINWYX-2 (the in-state port): the frame relation lives IN
         the state — [denote_def] reads it for the address rewrite and
         advances it through each def, so the walk needs no mirroring.
         The classification ([rewrite_addr]) uses the PRE-def state's
         relation; the stack FLAG stays on the original address. *)
      (* [input_bottom]: computed once per block (fix 4) — a def whose
         value set is bottom counts as bottom_dead when the block's
         ENTRY state is bottom (AI.equal st0 AI.bottom), else
         bottom_live. *)
      let input_bottom = AI.equal st0 AI.bottom in
      let st = ref st0 in
      Term.enum def_t b
      |> Seq.iter ~f:(fun d ->
          let st_before = !st in
          (* Sequential def denotation, exactly like the fixpoint
             (denote_defs, cbat_vsa.ml:350-359). *)
          st := Vsa.denote_def d !st;
          (* Def-value metric: only word lhs (Type.Imm w — skip
             Type.Mem and Type.Unk lhs, no width to index find_word).
             The tagged flag (fix 3) is the per-def
             Cbat_vsa_utils.relevant tag; the bottom bucket is split
             by the block's entry state (fix 4). *)
          (match Var.typ (Def.lhs d) with
           | Type.Imm w ->
             let ws = AI.find_word w !st (Def.lhs d) in
             let tagged = Term.has_attr d Cbat_vsa_utils.relevant in
             let b =
               match classify_def ws with
               | `Bottom ->
                 (* L2a diagnostic: dump the operand value-sets of
                    bottom defs (env-gated — byte-identical when off).
                    The live/dead split uses the same [input_bottom]
                    flag as the bucket split below. *)
                 if input_bottom then begin
                   incr bottom_dead;
                   if diag_on () then
                     diag_bottom bname sub' b d input_bottom tagged
                       (Vsa.frame_of_state st_before) st_before
                 end else begin
                   incr bottom_live;
                   if diag_on () then
                     diag_bottom bname sub' b d input_bottom tagged
                       (Vsa.frame_of_state st_before) st_before
                 end;
                 if input_bottom then `Bottom_dead else `Bottom_live
               | `Exact -> `Exact
               | `B2_3 -> `B2_3
               | `B4_8 -> `B4_8
               | `B9_64 -> `B9_64
               | `B65p -> `B65p
               | `Top -> `Top
             in
             Sub_stats.add_def s tagged b
           | Type.Mem _ | Type.Unk -> ());
          (* Load/Store address metric (address = the addr argument of
             either BIL form, evaluated in the state BEFORE the def). *)
          (match addr_exp_of_rhs (Def.rhs d) with
           | Some a ->
             let stack = is_stack_addr a in
             let a' =
               Vsa.rewrite_addr (Vsa.frame_of_state st_before) a in
             (* M6 (MIGRATED, ticket 02) — the IN-state tag: the
                address's free vars are denoted with the block's
                IN-state values (the fused fixpoint's branch-sensitive
                state, refined inline by the accumulated edge conds),
                not the sequentially re-denoted ones — the loop-body
                index var `RAX := Load(cell)` would otherwise read the
                solution's widened cell. *)
             (* ARCH-1 — the M6 meet is THE MODULE's ([st_tag_of]):
                the production genuine-subset gate (a TOP sequential
                value is NOT refined) — the probe's former inline copy
                predated the Option B/c fix and kept refining TOPs;
                the divergence was an accident of history (the fix
                never reached this file), not an intent difference.
                Bucket numbers re-baselined with this commit. *)
             let st_tag =
               Vsa.Cbat_extraction.st_tag_of ~tags b a' st_before in
             (match Vsa.denote_imm_exp a' st_tag with
              | Error _ ->
                s.Sub_stats.ld_denote_err <- s.Sub_stats.ld_denote_err + 1
              | Ok ws ->
                (* The bottom split (L1) uses the same per-block
                   [input_bottom] flag as the def series. *)
                let lb = classify_ld ws input_bottom in
                Sub_stats.add_ld s stack lb;
                (* Window buckets (fix 6): stack-flagged FINITE NON-TOP
                   (exact or bounded) addresses only; the count goes
                   into w_b64/w_4k/w_2m/w_big and the window value
                   keeps ldstk_w_max. *)
                if stack && (lb = `Exact || lb = `Bounded) then begin
                  let wb, win = window_metric_of ws in
                  Sub_stats.add_window s wb;
                  match win with
                  | Some v ->
                    if Int64.compare v s.Sub_stats.ldstk_w_max > 0 then
                      s.Sub_stats.ldstk_w_max <- v
                  | None -> ()
                end)
           | None -> ())));
  (* L2a per-sub summary (env-gated): the totals must be consistent
     with the def_bottom_live/def_bottom_dead columns. *)
  if diag_on () then
    Printf.printf "DIAG_SUM\t%s\t%s\t%d\t%d\n" bname (Sub.name sub')
      !bottom_live !bottom_dead;
  flush stdout;
  s

(* ------------------------------------------------------------------ *)
(* Per-binary driver (corpus_watch.run_binary shape). *)

type bin_report = {
  bname : string;
  mutable nsubs : int;
  mutable nok : int;
  mutable ncrashes : int;
  mutable nloadfail : int;
  (* summed columns for the BIN rollup line *)
  mutable sum : Sub_stats.t;
}

(* The 36 per-sub columns as strings (see the header comment): sub,
   sub_ms, 8 def, 9 def_tagged, 6 ld, 5 ldstk, 5 ldstk_w.  The
   caller prefixes the binary name and (for the BIN rollup) appends the
   two pct metrics — the layout is a list, so the column count is
   obvious. *)
let row_of (s : Sub_stats.t) : string list =
  [ s.Sub_stats.sname; string_of_int s.Sub_stats.sub_ms;
    string_of_int s.Sub_stats.def_exact;
    string_of_int s.Sub_stats.def_b2_3;
    string_of_int s.Sub_stats.def_b4_8;
    string_of_int s.Sub_stats.def_b9_64;
    string_of_int s.Sub_stats.def_b65p;
    string_of_int s.Sub_stats.def_top;
    string_of_int s.Sub_stats.def_bottom_live;
    string_of_int s.Sub_stats.def_bottom_dead;
    string_of_int s.Sub_stats.def_tagged_exact;
    string_of_int s.Sub_stats.def_tagged_b2_3;
    string_of_int s.Sub_stats.def_tagged_b4_8;
    string_of_int s.Sub_stats.def_tagged_b9_64;
    string_of_int s.Sub_stats.def_tagged_b65p;
    string_of_int s.Sub_stats.def_tagged_top;
    string_of_int s.Sub_stats.def_tagged_bottom_live;
    string_of_int s.Sub_stats.def_tagged_bottom_dead;
    string_of_int s.Sub_stats.def_tagged_count;
    string_of_int s.Sub_stats.ld_exact;
    string_of_int s.Sub_stats.ld_bounded;
    string_of_int s.Sub_stats.ld_top;
    string_of_int s.Sub_stats.ld_bottom_live;
    string_of_int s.Sub_stats.ld_bottom_dead;
    string_of_int s.Sub_stats.ld_denote_err;
    string_of_int s.Sub_stats.ldstk_exact;
    string_of_int s.Sub_stats.ldstk_bounded;
    string_of_int s.Sub_stats.ldstk_top;
    string_of_int s.Sub_stats.ldstk_bottom_live;
    string_of_int s.Sub_stats.ldstk_bottom_dead;
    string_of_int s.Sub_stats.ldstk_w_b64;
    string_of_int s.Sub_stats.ldstk_w_4k;
    string_of_int s.Sub_stats.ldstk_w_2m;
    string_of_int s.Sub_stats.ldstk_w_big;
    Int64.to_string s.Sub_stats.ldstk_w_max ]

let print_sub_line (path : string) (s : Sub_stats.t) : unit =
  Printf.printf "%s\n" (String.concat "\t" (path :: row_of s));
  flush stdout

(* [add_sum dst src]: accumulate one sub's columns into the BIN sum
   (ldstk_w_max takes the max). *)
let add_sum (dst : Sub_stats.t) (src : Sub_stats.t) : unit =
  dst.Sub_stats.sub_ms <- dst.Sub_stats.sub_ms + src.Sub_stats.sub_ms;
  dst.Sub_stats.def_exact <- dst.Sub_stats.def_exact + src.Sub_stats.def_exact;
  dst.Sub_stats.def_b2_3 <- dst.Sub_stats.def_b2_3 + src.Sub_stats.def_b2_3;
  dst.Sub_stats.def_b4_8 <- dst.Sub_stats.def_b4_8 + src.Sub_stats.def_b4_8;
  dst.Sub_stats.def_b9_64 <- dst.Sub_stats.def_b9_64 + src.Sub_stats.def_b9_64;
  dst.Sub_stats.def_b65p <- dst.Sub_stats.def_b65p + src.Sub_stats.def_b65p;
  dst.Sub_stats.def_top <- dst.Sub_stats.def_top + src.Sub_stats.def_top;
  dst.Sub_stats.def_bottom_live <-
    dst.Sub_stats.def_bottom_live + src.Sub_stats.def_bottom_live;
  dst.Sub_stats.def_bottom_dead <-
    dst.Sub_stats.def_bottom_dead + src.Sub_stats.def_bottom_dead;
  dst.Sub_stats.def_tagged_exact <-
    dst.Sub_stats.def_tagged_exact + src.Sub_stats.def_tagged_exact;
  dst.Sub_stats.def_tagged_b2_3 <-
    dst.Sub_stats.def_tagged_b2_3 + src.Sub_stats.def_tagged_b2_3;
  dst.Sub_stats.def_tagged_b4_8 <-
    dst.Sub_stats.def_tagged_b4_8 + src.Sub_stats.def_tagged_b4_8;
  dst.Sub_stats.def_tagged_b9_64 <-
    dst.Sub_stats.def_tagged_b9_64 + src.Sub_stats.def_tagged_b9_64;
  dst.Sub_stats.def_tagged_b65p <-
    dst.Sub_stats.def_tagged_b65p + src.Sub_stats.def_tagged_b65p;
  dst.Sub_stats.def_tagged_top <-
    dst.Sub_stats.def_tagged_top + src.Sub_stats.def_tagged_top;
  dst.Sub_stats.def_tagged_bottom_live <-
    dst.Sub_stats.def_tagged_bottom_live + src.Sub_stats.def_tagged_bottom_live;
  dst.Sub_stats.def_tagged_bottom_dead <-
    dst.Sub_stats.def_tagged_bottom_dead + src.Sub_stats.def_tagged_bottom_dead;
  dst.Sub_stats.def_tagged_count <-
    dst.Sub_stats.def_tagged_count + src.Sub_stats.def_tagged_count;
  dst.Sub_stats.ld_exact <- dst.Sub_stats.ld_exact + src.Sub_stats.ld_exact;
  dst.Sub_stats.ld_bounded <- dst.Sub_stats.ld_bounded + src.Sub_stats.ld_bounded;
  dst.Sub_stats.ld_top <- dst.Sub_stats.ld_top + src.Sub_stats.ld_top;
  dst.Sub_stats.ld_bottom_live <-
    dst.Sub_stats.ld_bottom_live + src.Sub_stats.ld_bottom_live;
  dst.Sub_stats.ld_bottom_dead <-
    dst.Sub_stats.ld_bottom_dead + src.Sub_stats.ld_bottom_dead;
  dst.Sub_stats.ld_denote_err <-
    dst.Sub_stats.ld_denote_err + src.Sub_stats.ld_denote_err;
  dst.Sub_stats.ldstk_exact <-
    dst.Sub_stats.ldstk_exact + src.Sub_stats.ldstk_exact;
  dst.Sub_stats.ldstk_bounded <-
    dst.Sub_stats.ldstk_bounded + src.Sub_stats.ldstk_bounded;
  dst.Sub_stats.ldstk_top <- dst.Sub_stats.ldstk_top + src.Sub_stats.ldstk_top;
  dst.Sub_stats.ldstk_bottom_live <-
    dst.Sub_stats.ldstk_bottom_live + src.Sub_stats.ldstk_bottom_live;
  dst.Sub_stats.ldstk_bottom_dead <-
    dst.Sub_stats.ldstk_bottom_dead + src.Sub_stats.ldstk_bottom_dead;
  dst.Sub_stats.ldstk_w_b64 <-
    dst.Sub_stats.ldstk_w_b64 + src.Sub_stats.ldstk_w_b64;
  dst.Sub_stats.ldstk_w_4k <-
    dst.Sub_stats.ldstk_w_4k + src.Sub_stats.ldstk_w_4k;
  dst.Sub_stats.ldstk_w_2m <-
    dst.Sub_stats.ldstk_w_2m + src.Sub_stats.ldstk_w_2m;
  dst.Sub_stats.ldstk_w_big <-
    dst.Sub_stats.ldstk_w_big + src.Sub_stats.ldstk_w_big;
  if Int64.compare src.Sub_stats.ldstk_w_max
      dst.Sub_stats.ldstk_w_max > 0 then
    dst.Sub_stats.ldstk_w_max <- src.Sub_stats.ldstk_w_max

(* [print_bin_line]: the BIN rollup line — the summed columns plus TWO
   percentages (2 decimals, "n/a" on div-by-zero), filtered FIRST:
   ldstk_exact_pct_filtered (dead-block bottoms excluded — the L1
   primary metric) then ldstk_exact_pct (full population, dead bottoms
   included — the pre-L1 metric, secondary). *)
let print_bin_line (r : bin_report) : unit =
  let s = r.sum in
  let denom_filtered = s.Sub_stats.ldstk_exact + s.Sub_stats.ldstk_bounded
                       + s.Sub_stats.ldstk_top
                       + s.Sub_stats.ldstk_bottom_live in
  let denom_full = denom_filtered + s.Sub_stats.ldstk_bottom_dead in
  let pct_filtered =
    if denom_filtered = 0 then "n/a"
    else Printf.sprintf "%.2f"
        (100.0 *. float s.Sub_stats.ldstk_exact /. float denom_filtered) in
  let pct_full =
    if denom_full = 0 then "n/a"
    else Printf.sprintf "%.2f"
        (100.0 *. float s.Sub_stats.ldstk_exact /. float denom_full) in
  (* The BIN rollup reuses the sub row layout: the binary column is the
     literal "BIN", the sub column is the binary basename, and the
     sub_ms/... columns are the summed [row_of]. *)
  let cols = Filename.basename r.bname :: List.tl (row_of s) in
  Printf.printf "%s\n"
    (String.concat "\t" ("BIN" :: cols @ [ pct_filtered; pct_full ]));
  flush stdout

let rec run_binary (path : string) : bin_report =
  let r = { bname = path; nsubs = 0; nok = 0; ncrashes = 0; nloadfail = 0;
            sum = Sub_stats.create "BIN" } in
  try
    match Project.create (Project.Input.file ~loader:"llvm" ~filename:path) with
    | Error e ->
      r.nloadfail <- 1;
      Printf.printf "LOAD-FAIL\t%s\t%s\n" path (Core_kernel.Error.to_string_hum e);
      flush stdout;
      r
    | Ok proj ->
      let prog = Project.program proj in
      let bname = Filename.basename path in
      let sp = Hike.Abi.sp (Project.target proj) in
      Term.enum sub_t prog
      |> Seq.iter ~f:(fun sub ->
          r.nsubs <- r.nsubs + 1;
          match run_sub sp prog bname sub with
          | Ok st ->
            r.nok <- r.nok + 1;
            add_sum r.sum st;
            print_sub_line path st
          | Crash (es, bt) ->
            r.ncrashes <- r.ncrashes + 1;
            Printf.printf "CRASH\t%s\t%s\t%s\n" path (Sub.name sub) es;
            (match bt with
             | "" -> ()
             | _ -> Printf.printf "  backtrace:\n%s\n" bt);
            flush stdout);
      print_bin_line r;
      r
  with e ->
    (* Project.create / enumeration blew up (catches most things
       itself, but not, e.g., the empty-input assert). *)
    r.nloadfail <- 1;
    Printf.printf "LOAD-FAIL\t%s\texception: %s\n" path (describe_exn e);
    flush stdout;
    r

(* One sub, one full fixpoint — the corpus_watch invocation shape (the
   D4-9 invocation, test_cbat.ml:581) with the relevance-analyze
   hookup (ALWAYS — restriction ON only), the entry solution,
   (fix 8), the per-sub fixpoint wall time (fix 5: Unix.gettimeofday
   around static_graph_vsa ONLY, the corpus_watch.ml:73-78 idiom), and
   the precision measurement walk.  [bname] is the binary basename,
   used only by the L2a DIAG lines. *)
and run_sub (sp : var) (prog : program term) (bname : string)
    (sub : sub term) : outcome =
  try
    let sub' = Relevance.analyze sp sub in
    let prog' = Program.create ~subs:[ sub' ] () in
    let t0 = Unix.gettimeofday () in
    let sol =
      Vsa.static_graph_vsa [] prog' sub' (init_sol_of sub') in
    let t1 = Unix.gettimeofday () in
    (* MIGRATED (ticket 02, the Phase B deletion): the per-block TAG state
       is the block's IN-state read directly from the converged solution —
       the fused fixpoint refines the per-edge states INLINE (the deep
       walk at every out-edge, driven by the ACCUMULATED
       [Graphs.Ir.Edge.cond]), so [tags = sol]: the walk's addresses are
       denoted with the IN-state so the loop-body dynamic-index accesses
       carry the index's iterate constraint (the w_big class leaves the
       bucket).  (The consumer [Hike_vsa.offsets_of_sub] reads the same
       way — docs/trace-partitioning-plan.md §7.) *)
    let st = collect_stats bname sub' sol sol in
    st.Sub_stats.sub_ms <- int_of_float ((t1 -. t0) *. 1000.0);
    Ok st
  with e ->
    Crash (describe_exn e, Printexc.get_backtrace ())

let () =
  let paths = List.tl (Array.to_list Sys.argv) in
  match paths with
  | [] ->
    Printf.printf "usage: %s <binary> [<binary> ...]\n" Sys.argv.(0);
    flush stdout;
    exit 0
  | _ ->
    (* Initializes the BAP environment (loads the installed plugins,
       incl. the x86 disassembler backend). *)
    (match Bap_main.init ~argv:[|Sys.executable_name|] () with
     | Ok () -> ()
     | Error failed ->
       Format.eprintf "precision_probe: BAP initialization failed: %a@\n%!"
         Bap_main.Extension.Error.pp failed;
       exit 1);
    Printf.printf "=== precision probe (restriction ON) ===\n";
    flush stdout;
    let reports = List.map run_binary paths in
    Printf.printf "\n=== precision probe summary ===\n";
    Printf.printf "%-28s %7s %6s %8s %10s\n"
      "binary" "subs" "ok" "crashes" "loadfail";
    List.iter
      (fun r ->
        Printf.printf "%-28s %7d %6d %8d %10d\n"
          (Filename.basename r.bname) r.nsubs r.nok r.ncrashes r.nloadfail)
      reports;
    let crashes = List.fold_left (fun acc r -> acc + r.ncrashes) 0 reports in
    let loadfails = List.fold_left (fun acc r -> acc + r.nloadfail) 0 reports in
    Printf.printf "TOTAL: %d crashes, %d load failures\n"
      crashes loadfails;
    Printf.printf "%s\n"
      (if crashes = 0 && loadfails = 0 then
         "PRECISION PROBE: PASS (no crashes)"
       else "PRECISION PROBE: FAIL (crashes present)");
    flush stdout;
    exit (if crashes = 0 && loadfails = 0 then 0 else 1)
