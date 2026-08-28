# 02: Implement landmark acquisition (observe_unsat + landmark_env + heads_of_wto)

**What to build:** The data structures and logic for the "acquisition" half of Simon & King: given a WTO and a value-set meet that comes back empty, the excluded boundary and its distance to the enclosing loop head are recorded in the landmark environment. `heads_of_wto` discovers the loop-head set from the current WTO.

**Blocked by:** T01 (Recover cbat_landmarks.ml (compiling API surface)).

**Status:** ready-for-agent

- [ ] `observe_unsat` records the excluded boundary + distance keyed by WTO head in `landmark_env`
- [ ] `heads_of_wto` returns the set of loop heads from the current WTO
- [ ] Unit-checkable: an empty meet on a 1-D variable produces one landmark at the correct head
