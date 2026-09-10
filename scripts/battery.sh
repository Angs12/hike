#!/usr/bin/env bash
# The corpus battery: the full gate chain the repo rules require for any
# change, in one driver. Run from a tree whose plugin is INSTALLED and
# PROVENANCE-RECORDED (dune build @install && dune install; bash
# src/record_provenance.sh). Consumes /tmp/corpus and /tmp/corpus_o2.
#
# Usage: battery.sh <out-dir> [tag]
# Writes <out-dir>/battery-<tag>.summary and exits non-zero iff any HARD
# gate is red. The pinned -O2 gate is reported as PIN-MOVED (with the
# failing-set delta) rather than a hard fail: a deliberate flip updates
# scripts/semantic/o2_known_failures.txt + AGENTS.md in the same commit
# and re-runs; an unexplained movement stops the merge.
set -u
OUT="${1:?usage: battery.sh <out-dir> [tag]}"
TAG="${2:-$(date +%H%M%S)}"
HERE="$(cd "$(dirname "$0")" && pwd)"
SUM="$OUT/battery-$TAG.summary"
mkdir -p "$OUT"

command -v bap >/dev/null 2>&1 || { echo "FATAL: bap not found (eval \$(opam env) first)" >&2; exit 2; }
command -v opt-21 >/dev/null 2>&1 || { echo "FATAL: opt-21 not found (the gate pins the optimizer)" >&2; exit 2; }
C0=/tmp/corpus; C2=/tmp/corpus_o2
[ -d "$C0" ] && [ -d "$C2" ] || { echo "FATAL: corpus dirs missing ($C0, $C2)" >&2; exit 2; }
# Corpus identity: the -O2 lane must be genuinely -O2. The sp_reload-era
# rebuild once left an -O0 COPY in $C2 (compile_corpus.sh <dir> builds -O0
# unless <dir> ends in -o2), and every -O2 gate silently tested -O0
# binaries. These two vectorization canaries must DIFFER from the -O0 lane.
for canary in byte_copy fizzbuzz_safe; do
  if cmp -s "$C0/$canary" "$C2/$canary" 2>/dev/null; then
    echo "FATAL: $C2 is an -O0 copy (canary $canary identical to $C0)." >&2
    echo "       Rebuild the lanes: compile_corpus.sh /tmp/corpus-o2; cp -a /tmp/corpus-o2 /tmp/corpus_o2" >&2
    exit 2
  fi
done

# Provenance: the installed plugin must be THIS tree's build (by content).
# The src hash must re-derive EXACTLY as record_provenance.sh does — sha256sum
# output embeds the path strings, so find the CANONICAL src path.
SRC_DIR="$(cd "$HERE/../src" && pwd)"
SRC_HASH=$(find "$SRC_DIR" -name '*.ml' -o -name '*.mli' -o -name 'dune' | sort | xargs sha256sum 2>/dev/null | sha256sum | cut -c1-16)
PROV="$(find "$(opam var prefix 2>/dev/null)/lib/hike" -maxdepth 1 -name 'hike.cmxs.provenance' 2>/dev/null | head -1)"
PROV_TREE=$(grep '^tree:' "$PROV" 2>/dev/null | awk '{print $2}')
PROV_SRC=$(grep '^src_sha16:' "$PROV" 2>/dev/null | awk '{print $2}')
PROV_BUNDLE=$(grep '^bundle_sha16:' "$PROV" 2>/dev/null | awk '{print $2}')
if [ "$(cd "$HERE/.." && pwd)" != "$PROV_TREE" ] || [ "$SRC_HASH" != "$PROV_SRC" ]; then
  echo "FATAL: installed plugin is NOT this tree's build (provenance: tree=$PROV_TREE src=$PROV_SRC; this tree src=$SRC_HASH)" >&2
  echo "       rebuild + reinstall + record_provenance.sh, then re-run." >&2
  exit 2
fi
echo "provenance: OK (bundle=$PROV_BUNDLE tree=$PROV_TREE)" | tee -a "$SUM"

REDS=0
gate() { # gate <name> <logfile> <rc> [pin-delta-file]
  local name="$1" log="$2" rc="$3" pin="${4:-}"
  if [ "$rc" -eq 0 ]; then
    echo "PASS  $name (log: $log)" | tee -a "$SUM"
  elif [ -n "$pin" ]; then
    echo "PIN-MOVED  $name (log: $log; delta: $pin)" | tee -a "$SUM"
  else
    echo "FAIL  $name (log: $log)" | tee -a "$SUM"
    REDS=$((REDS+1))
  fi
}

# 0. unit suite + differential referee (dune-local; no plugin).
dune runtest >"$OUT/runtest.log" 2>&1
gate "dune runtest (units + clpequiv referee)" "$OUT/runtest.log" $?

# 1. -O0 corpus: emission, structural asserts, strict semantics, strict opt-safety.
bash "$HERE/run_corpus.sh" "$C0" "$OUT/emit-o0" >"$OUT/emit-o0.log" 2>&1
gate "-O0 emission (run_corpus, 33/33 rc=0)" "$OUT/emit-o0.log" $?
bash "$HERE/check_allocas.sh" "$OUT/emit-o0" >"$OUT/allocas-o0.log" 2>&1
gate "-O0 structural asserts (check_allocas)" "$OUT/allocas-o0.log" $?
bash "$HERE/semantic/run_semantic.sh" "$C0" "$OUT/emit-o0" "$OUT/sem-o0" >"$OUT/sem-o0.log" 2>&1
gate "-O0 semantics strict (33 PASS / 0 FAIL)" "$OUT/sem-o0.log" $?
bash "$HERE/semantic/run_semantic_opt.sh" "$C0" "$OUT/emit-o0" "$OUT/semopt-o0" >"$OUT/semopt-o0.log" 2>&1
gate "-O0 opt-safety strict (33 PASS / 0 FAIL)" "$OUT/semopt-o0.log" $?

# 2. -O2 corpus: emission, structural asserts, PINNED semantics.
bash "$HERE/run_corpus.sh" "$C2" "$OUT/emit-o2" >"$OUT/emit-o2.log" 2>&1
gate "-O2 emission (run_corpus, 33/33 rc=0)" "$OUT/emit-o2.log" $?
bash "$HERE/check_allocas.sh" "$OUT/emit-o2" >"$OUT/allocas-o2.log" 2>&1
gate "-O2 structural asserts (check_allocas)" "$OUT/allocas-o2.log" $?
PIN="$HERE/semantic/o2_known_failures.txt"
bash "$HERE/semantic/run_semantic.sh" "$C2" "$OUT/emit-o2" "$OUT/sem-o2" "$PIN" >"$OUT/sem-o2.log" 2>&1
RC_PIN=$?
PIN_DELTA="$OUT/sem-o2.pin-delta"
if [ "$RC_PIN" -ne 0 ]; then
  # The pin log names REGRESSION/IMPROVEMENT; extract the failing set delta for the merger.
  grep -iE "REGRESSION|IMPROVEMENT|newly|now pass" "$OUT/sem-o2.log" >"$PIN_DELTA" 2>/dev/null || true
fi
gate "-O2 semantics pinned (set == o2_known_failures.txt)" "$OUT/sem-o2.log" "$RC_PIN" "$PIN_DELTA"

# 3. The convergence report (the quality instrument; informative, never red).
bash "$HERE/semantic/convergence_report.sh" "$C0" "$C2" "$OUT/emit-o0" "$OUT/emit-o2" "$OUT/conv" >"$OUT/conv.log" 2>&1
echo "INFO  convergence report (log: $OUT/conv.log; table: $OUT/conv/)" | tee -a "$SUM"

echo "battery: $REDS hard red(s); summary: $SUM" | tee -a "$SUM"
exit $REDS
