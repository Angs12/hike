# Ticket 04 — the constraint-lane merges (twin deletion, gate-free rules untouched)

Deps: none. One battery-verified commit. The F1/L3/L-B fixtures pin every
behavior; the battery IS the proof.

Merges (all inside the VSA engine's backward lane):
- ~~The bounds→CLP constructor twins~~ DEAD BY MEASUREMENT (2026-09-08):
  `circular_hull` and `interval_of_bounds` differ by exactly the lo>hi
  guard, and the guard is the contract: the backward PLUS/MINUS/SDIVIDE
  rows pin WRAPPED hulls (S8, L3c3-1, R2-1, M5-1 — modular wrap makes
  lo>hi reachable at all five sites). The re-point was tried, the suite
  went 10-red (the 4 hull pins + 6 downstream F1 landmark pins), and it
  was reverted the same session: both spellings stay, with comments
  recording why. Do not re-propose.
- The HIGH-cast pre-image twin: the leaf-constraint extractor keeps the pure
  pre-image; the walk's HIGH arm = pre-image + meet + recurse (it already
  ends in the same bounds call).
- The LSHIFT pre-image twin: one option-returning pre-image; the meeting
  variant and the pairing variant consume it.
- The NEQ complement row: one named helper (TOP minus a point, with the
  bottom check) replacing the four inline builds.
- The guard decomposition's const-left/const-right mirror arms: parameterize
  by the side selector + the flip; the two `True/False × NEQ/EQ` rows become
  the NEQ helper's two spellings.
- The word-meet triple: ~~one word-refine helper~~ DEAD BY MEASUREMENT
  (2026-09-08): the three sites LOOK identical but differ in load-bearing
  corners — the tag-state meet has NO width check and a singleton-tolerance
  (width-polymorphic vars, the Bug C class: the same name stored at one
  width and read at another, reach the meet with mismatched widths), and
  the trace fold likewise skips the check. Unifying them under one checked
  helper moved 3 corpus binaries (array_local/sret_big/union_overlap —
  one tag wobble + two downstream order swaps; candidate self-consistent,
  control self-consistent, so not the flake). Reverted same session; the
  question whether the check-free corners are load-bearing for soundness
  belongs to a soundness lane with its own fixtures, not a cleanup.
- The unsat-observer twin arms (the var case and the generic case run the
  same observe block): one observer closure.
- The widening-need Kosaraju vs the WTO module's: functorize the SCC over
  the key type; both call it. The six accumulator refs inside this block
  die with the functorization (see ticket 05's overlap note).
- The run-context record-update triple-nesting: two one-line update helpers
  at the context module, used by every memo/transfer update site.

RULES (non-negotiable, from the design principles): no gate may be
introduced; every merged rule keeps its identity arm (top / no constraint)
as the sound fallback; a merged row that can claim BOTTOM on a live path is
a bug — the merge must preserve each arm's exact bottom conditions.

Acceptance: full battery (the F1-NEQ strict acceptance test and the L3c
families are the pins); corpus IR byte-identity 32/32; referee stanza green.
