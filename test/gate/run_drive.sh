#!/usr/bin/env bash
# Lifts the corpus with the installed hike (ADR 0032) and compares
# every emission and its diagnostics against the plugin path's.
#
# Usage: run_drive.sh [corpus_dir] [plugin_emit_dir] [out_dir]
#
# The plugin emissions come from the lift stage.  Block labels carry KB
# object numbers, which differ between the two entries, so the
# comparison renames them by first appearance; everything else must be
# identical.  STRICT: a non-zero lift rc or any difference is a failure.

set -u

HERE="$(cd "$(dirname "$0")" && pwd)"

CORPUS="${1:-/tmp/corpus-o2}"
PLUGIN="${2:-/tmp/hike-emit}"
OUT="${3:-/tmp/hike-drive-emit}"
mkdir -p "$OUT"

if ! compgen -G "$PLUGIN/out_*.ll" >/dev/null; then
  echo "FATAL: no plugin emissions in $PLUGIN (run the lift stage first)" >&2
  exit 2
fi

LIBDIR="$(opam var lib 2>/dev/null || true)"
PROV="$LIBDIR/hike/hike.cmxs.provenance"
if [ ! -f "$PROV" ] || ! cmp -s "$PROV" "$PLUGIN/.plugin_provenance"; then
  echo "FATAL: the emissions in $PLUGIN were not produced by the installed plugin — re-run the lift stage" >&2
  exit 2
fi
cp "$PROV" "$OUT/.plugin_provenance"

: >"$OUT/diagnostics.txt"
fail=0
n=0
for f in "$CORPUS"/*; do
  [ -f "$f" ] && [ -x "$f" ] || continue
  case "$f" in *.c|*.h) continue ;; esac
  name="$(basename "$f")"
  n=$((n + 1))
  rm -f "$OUT/out_$name.ll"
  timeout 300 hike "$f" -o "$OUT/out_$name.ll" \
    >"$OUT/stdout_$name.txt" 2>"$OUT/err_$name.txt"
  rc=$?
  echo "$rc" >"$OUT/rc_$name.txt"
  {
    printf '===== %s (rc=%d)\n' "$name" "$rc"
    grep -E 'hike:' "$OUT/err_$name.txt" 2>/dev/null
  } >>"$OUT/diagnostics.txt"
  if [ "$rc" -ne 0 ]; then
    printf 'FAIL %s rc=%d\n' "$name" "$rc"
    fail=$((fail + 1))
  elif ! python3 "$HERE/compare_drive.py" "$PLUGIN" "$OUT" "$name"; then
    fail=$((fail + 1))
  else
    printf 'SAME %s\n' "$name"
  fi
done

ndiag="$(grep -c '^hike:' "$OUT/diagnostics.txt")"
printf '\ndrive: %d binaries, %d failed; %s diagnostic line(s)\n' "$n" "$fail" "$ndiag"
[ "$fail" -eq 0 ] || exit 1
