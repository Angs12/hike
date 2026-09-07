# Ticket 04 — the constraint-lane merges (twin deletion, gate-free rules untouched)

Deps: none. One battery-verified commit. The F1/L3/L-B fixtures pin every
behavior; the battery IS the proof.

Merges (all inside the VSA engine's backward lane):
- The bounds→CLP constructor twins: one name (the circular-hull spelling
  dies; its four call sites re-point). NOTE the honest-gate's exact step-1
  meet lane landed near this area — re-verify which spelling survived before
  editing; do not touch the step-1 lane's own body.
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
- The word-meet triple (the var-meet discipline, the tag-state meet, the
  trace meet's inner fold): one word-refine helper; the tag-state variant's
  meet-tolerance rides as a flag.
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
