# 15: FP regression probe

**What to build:** A regression probe guarding the corrected FP modeling: `div.c` prints exact double, a COMISS-guarded branch is correct, and no same-name diff-width lane conflation occurs. This is the FP gate that must stay green as landmark work proceeds.

**Blocked by:** T12 (create_native_fp_call binds every consumer-width view), T13 (COMISS/COMISD semantics-table entries).

**Status:** ready-for-agent

- [ ] `div.c` prints exact double in the harness
- [ ] A COMISS-guarded branch is correct
- [ ] `run_semantic_all.sh` 31/31 and `check_allocas.sh` 124/0 stay green (FP gate)
