# 13: COMISS/COMISD semantics-table entries

**What to build:** The installed SSE semantics table lacked COMISS/COMISD entries, so the lifter dropped the instruction and branches consumed stale integer flags. Add COMISD{rm,rr}/COMISS{rm,rr} with UC-identical BIL (they differ only in signalling-NaN exceptions) and fix the rr `fp-compare` macro typo (`(compare-floats rt rm rm)` compared a register with itself).

**Blocked by:** None (can start immediately).

**Status:** ready-for-agent

- [ ] COMISS/COMISD entries present; a COMISS-guarded conditional branch takes the correct path
- [ ] The rr `fp-compare` macro compares distinct operands
- [ ] Verifiable via a COMISS/COMISD-guarded corpus binary behaving byte-identically to native
