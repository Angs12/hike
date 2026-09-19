#!/usr/bin/env bash
# Runs hike-convlir over the corpus and prints the surviving-diagnostics table.
# Usage: run_corpus.sh [corpus_dir] [out_dir]
# Writes out_<name>.ll / err_<name>.txt / stdout_<name>.txt / rc_<name>.txt per binary.
# Surviving classes: hike: guarded: (unresolvable access) and hike: undef-read:.
#
# HIKE_BATCH=1 lifts the whole corpus in one process through the batch
# driver (dune exec bin/hike_batch.exe) instead of one bap spawn per
# binary — same chain, amortized startup. Default stays bap.

set -u

HERE="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "$HERE/.." && pwd)"

CORPUS="${1:-/tmp/corpus}"
OUT="${2:-/tmp/heritage_p5}"
mkdir -p "$OUT"

# Corpus executables in sorted order (skips sources/stubs).
BINS=""
for f in "$CORPUS"/*; do
  [ -f "$f" ] && [ -x "$f" ] || continue
  case "$f" in *.c|*.h) continue ;; esac
  BINS="$BINS $(basename "$f")"
done

if [ "${HIKE_BATCH:-0}" = "1" ]; then
  (cd "$REPO_ROOT" && dune build bin/hike_batch.exe) || exit 1
  ARGS=""
  for f in $BINS; do
    [ -x "$CORPUS/$f" ] || { echo "MISSING $f (expected $CORPUS/$f) — skipping"; continue; }
    ARGS="$ARGS $CORPUS/$f"
  done
  # shellcheck disable=SC2086
  (cd "$REPO_ROOT" && dune exec bin/hike_batch.exe -- \
      --output-dir="$OUT" --prefix=out_ $ARGS) \
      >"$OUT/batch_stdout.txt" 2>"$OUT/batch_stderr.txt"
  # Per-binary rc from the driver's end markers; the diagnostics
  # split per binary on the begin markers.
  for f in $BINS; do
    [ -x "$CORPUS/$f" ] || continue
    if grep -q "hike: batch: end $f rc=0" "$OUT/batch_stderr.txt"; then
      echo 0 >"$OUT/rc_$f.txt"
    else
      echo 1 >"$OUT/rc_$f.txt"
    fi
  done
  awk -v out="$OUT" '
    /hike: batch: begin / { file = out "/err_" $NF ".txt" }
    file { print > file }
  ' "$OUT/batch_stderr.txt"
else
  for f in $BINS; do
    if [ ! -x "$CORPUS/$f" ]; then
      echo "MISSING $f (expected $CORPUS/$f) — skipping"
      continue
    fi
    # --no-cache is load-bearing: bap's lift cache can serve a stale
    # (previously-rewritten) lift and the emitted IR silently differs.
    timeout 300 bap "$CORPUS/$f" --pass=hike-convlir --no-cache \
      --hike-output-file="$OUT/out_$f.ll" \
      >"$OUT/stdout_$f.txt" 2>"$OUT/err_$f.txt"
    rc=$?
    echo "$f rc=$rc"
    echo "$rc" >"$OUT/rc_$f.txt"
  done
fi

echo
printf '%-22s %-6s %s\n' "binary" "rc" "per-function emission diagnostics"
for f in $BINS; do
  [ -f "$OUT/err_$f.txt" ] || continue
  rc=$(cat "$OUT/rc_$f.txt" 2>/dev/null || echo n/a)
  echo "===== $f (rc=$rc)"
  diags="$(grep -E "hike: (guarded|undef-read):" "$OUT/err_$f.txt" 2>/dev/null)"
  if [ -n "$diags" ]; then
    printf '%s\n' "$diags" | sed 's/^/  /'
  else
    echo "  (no surviving diagnostics)"
  fi
done
