# 05: Wire acquisition: observe_unsat in meet_var on empty meet

**What to build:** During the fixpoint, whenever a guard meets a value set to empty, `meet_var` calls `observe_unsat` and attributes the excluded boundary + distance to `current_lm_head`, populating `landmark_env`. This connects acquisition (T02) to the live fixpoint (T04).

**Blocked by:** T02 (Implement landmark acquisition (observe_unsat + landmark_env + heads_of_wto)), T04 (Thread current_lm_head through the fixpoint).

**Status:** ready-for-agent

- [ ] An empty meet in a loop body records a landmark attributed to the correct head
- [ ] Analysis remains sound (no result change vs the threshold baseline on non-loop cases)
