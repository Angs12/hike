# 18: Coreutils 93/93 + semantic/allocas gates

**What to build:** The golden corpus rate is reproducible end-to-end: `scripts/coreutils_pipeline.sh` reports 93/93 coreutils native-vs-lifted success, plus `run_semantic_all.sh` 31/31 and `check_allocas.sh` 124/0. This is the user-visible "golden state" corpus gate.

**Blocked by:** T16 (dune build + runtest green), T17 (Verify/close the 10 green-gate issues).

**Status:** ready-for-agent

- [ ] `scripts/coreutils_pipeline.sh` reports 93/93
- [ ] `run_semantic_all.sh` 31/31
- [ ] `check_allocas.sh` 124/0
