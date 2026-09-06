# 05 — Semantic Gate & Full Corpus Validation

**Status:** ready-for-agent  
**Depends on:** 04  
**Blocks:** (none — the closing ticket)  

**READ FIRST:**
- The spec: `.scratch/directional-infs/spec.md` (§7, Ticket 5)
- Validation scripts:
  - `scripts/run_corpus.sh`
  - `scripts/semantic/run_semantic.sh` (8-bin oracle)
  - `scripts/semantic/run_semantic_all.sh` (35-bin corpus)
  - `scripts/check_allocas.sh`

**Tasks:**
- [ ] Build & install plugin: `dune build @install && dune install && bash src/record_provenance.sh`.
- [ ] Run 8-bin oracle: `scripts/semantic/run_semantic.sh /tmp/corpus <ir_dir> <out_dir>`: assert 8/8 PASS.
- [ ] Run full corpus emission on `/tmp/corpus` and `/tmp/opencode/corpus35`:
  - Assert all 35 binaries emit with `rc=0` and 0 surviving diagnostics.
- [ ] Run semantic harness `scripts/semantic/run_semantic_all.sh`:
  - Assert `/tmp/corpus/variadic` flips to **PASS** (`sum = 280`).
  - Assert `/tmp/corpus/va_arg_vacopy` flips to **PASS** (`1 2 3 4 5 6`).
  - Assert 0 regressions across all other 33 binaries (35/35 passing).
- [ ] Run `scripts/check_allocas.sh`: assert 160/160 checks pass.

**Verification:**
- Complete test run log recorded and cited.
