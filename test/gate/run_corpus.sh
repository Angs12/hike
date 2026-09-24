#!/usr/bin/env bash
# Runs hike-convlir over the corpus, asserts every lift exits 0, and writes
# the full diagnostics catalogue.
#
# Usage: run_corpus.sh [corpus_dir] [out_dir]
#
# Per binary: out_<name>.ll / err_<name>.txt / stdout_<name>.txt /
# rc_<name>.txt.  Plus diagnostics.txt (every `hike:` line, every class,
# not just the two formerly-grepped prefixes) and a one-line summary.
#
# STRICT: a non-zero lift rc is a loud failure (exit 1).  Diagnostics are
# catalogue-only: recorded and summarised, never asserted on.

set -u

HERE="$(cd "$(dirname "$0")" && pwd)"

CORPUS="${1:-/tmp/corpus}"
OUT="${2:-/tmp/hike-emit}"
mkdir -p "$OUT"

# Corpus executables in sorted order (skips sources/stubs).
BINS=""
for f in "$CORPUS"/*; do
  [ -f "$f" ] && [ -x "$f" ] || continue
  case "$f" in *.c|*.h) continue ;; esac
  BINS="$BINS $(basename "$f")"
done

: >"$OUT/diagnostics.txt"
fail=0
n=0
for f in $BINS; do
  n=$((n + 1))
  # --no-cache is load-bearing: bap's lift cache can serve a stale
  # (previously-rewritten) lift and the emitted IR silently differs.
  timeout 300 bap "$CORPUS/$f" --pass=hike-convlir --no-cache \
    --hike-output-file="$OUT/out_$f.ll" \
    >"$OUT/stdout_$f.txt" 2>"$OUT/err_$f.txt"
  rc=$?
  echo "$rc" >"$OUT/rc_$f.txt"
  if [ "$rc" -ne 0 ]; then
    printf 'FAIL %s rc=%d\n' "$f" "$rc"
    fail=$((fail + 1))
  else
    printf 'PASS %s\n' "$f"
  fi
  {
    printf '===== %s (rc=%d)\n' "$f" "$rc"
    grep -E 'hike:' "$OUT/err_$f.txt" 2>/dev/null
  } >>"$OUT/diagnostics.txt"
done

# One pass over the diagnostics: count + class set together.
diag_stats="$(awk '/^hike:/ { n++; if (match($0, /^hike: [a-z-]+:/)) { c=substr($0, RSTART+6, RLENGTH-7); cls[c]=1 } } END { printf "%d", n; for (k in cls) printf " %s", k }' "$OUT/diagnostics.txt" 2>/dev/null)"
ndiag="${diag_stats%% *}"
classes="${diag_stats#* }"
printf '\nlift: %d binaries, %d failed; %s diagnostic line(s) [classes: %s]\n' \
  "$n" "$fail" "${ndiag:-0}" "${classes:-none}"

[ "$fail" -eq 0 ] || exit 1
