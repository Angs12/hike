#!/usr/bin/env bash
# Corpus runner for the hike-convlir plugin (H-R1 final state, post model
# deletion).
#
# Runs the plugin over the full test corpus (real + synth binaries, all
# compiled PIE — plain `gcc -O0 -fno-stack-protector`, ET_DYN; see
# compile_corpus.sh) and prints a per-binary /
# per-function table of the SURVIVING emission diagnostics:
#
#   hike: guarded: <sub>: ...      unresolvable access -> poison/drop, warned
#                                  (the line ends with its "(dynamic
#                                  fallback)" note)
#   hike: undef-read: ...          a read of a never-defined var -> [undef]
#                                  (data reads warn individually, deduped per
#                                  block+var; the structural model-ABI lanes
#                                  aggregate into one per-sub summary line —
#                                  the 2026-09-01 poison-phi fix)
#
# The heritage-model diagnostics ("heritage ok", "heritage gate rejected",
# "heritage failed", "hike: range-diff", "hike: stack-args cross-check")
# died with the model deletion (P3) and are no longer grepped.  The
# "hike: bounded store:" and "hike: no-legacy:" classes had no emitters
# left in src/ and were dropped from the table (2026-08-22).
#
# Usage: run_corpus.sh [corpus_dir] [out_dir]
#   corpus_dir  default /tmp/corpus  (binaries; see compile_corpus.sh)
#   out_dir     default /tmp/heritage_p5
#
# Outputs out_<name>.ll / err_<name>.txt / stdout_<name>.txt / rc_<name>.txt
# per binary (the corpus protocol) and the per-binary diagnostic table to
# stdout.  Requires the hike plugin installed (bap --pass=hike-convlir must
# be available).

set -u

CORPUS="${1:-/tmp/corpus}"
OUT="${2:-/tmp/heritage_p5}"
mkdir -p "$OUT"

# Discover corpus executables (skip sources/stubs); deterministic sorted order.
BINS=""
for f in "$CORPUS"/*; do
  [ -f "$f" ] && [ -x "$f" ] || continue
  case "$f" in *.c|*.h) continue ;; esac
  BINS="$BINS $(basename "$f")"
done

for f in $BINS; do
  if [ ! -x "$CORPUS/$f" ]; then
    echo "MISSING $f (expected $CORPUS/$f) — skipping"
    continue
  fi
  timeout 300 bap "$CORPUS/$f" --pass=hike-convlir \
    --hike-output-file="$OUT/out_$f.ll" \
    >"$OUT/stdout_$f.txt" 2>"$OUT/err_$f.txt"
  rc=$?
  echo "$f rc=$rc"
  echo "$rc" >"$OUT/rc_$f.txt"
done

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
