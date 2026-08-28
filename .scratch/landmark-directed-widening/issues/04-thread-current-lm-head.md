# 04: Thread current_lm_head through the fixpoint

**What to build:** The fixpoint knows, at each block during denotation, which WTO head is innermost, so acquisition/consumption can attribute landmarks correctly. Bind the current-head ref around block denotation. This is tracking only — no analysis-result change yet.

**Blocked by:** T01 (Recover cbat_landmarks.ml (compiling API surface)).

**Status:** ready-for-agent

- [ ] `current_lm_head` is bound around `denote_block_with_stores` and reflects the innermost enclosing WTO head
- [ ] No change to analysis results yet (only head tracking)
