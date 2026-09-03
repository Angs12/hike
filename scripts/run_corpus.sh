#!/usr/bin/env bash
# Runs hike-convlir over the corpus and prints the surviving-diagnostics table.
# Usage: run_corpus.sh [corpus_dir] [out_dir]
# Writes out_<name>.ll / err_<name>.txt / stdout_<name>.txt / rc_<name>.txt per binary.
# Surviving classes: hike: guarded: (unresolvable access) and hike: undef-read:.

set -u

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
