#!/usr/bin/env bash
# Lifts the corpus with the installed hike executable (Hike.Drive, ADR
# 0032), asserts every lift exits 0, and writes the full diagnostics
# catalogue.
#
# Usage: run_corpus.sh [corpus_dir] [out_dir]
#
# Per binary: out_<name>.ll / err_<name>.txt / stdout_<name>.txt /
# rc_<name>.txt.  Plus diagnostics.txt (every `hike:` line, every class)
# and a one-line summary.
#
# The lift is INCREMENTAL: an emission is reused when the toolchain and the
# binary are both unchanged — the lift's only inputs — recorded as a stamp
# beside it.  FRESH=1 forces a full re-lift.
#
# STRICT: a non-zero lift rc is a loud failure (exit 1).  Diagnostics are
# catalogue-only: recorded and summarised, never asserted on.

set -u

HERE="$(cd "$(dirname "$0")" && pwd)"
. "$HERE/lib.sh"

CORPUS="${1:-/tmp/corpus-o2}"
OUT="${2:-/tmp/hike-emit}"
mkdir -p "$OUT"

if [ -z "$(ls -A "$CORPUS" 2>/dev/null)" ]; then
  echo "FATAL: no corpus at $CORPUS (run the corpus gate first)" >&2
  exit 2
fi

# Bind every emission in $OUT to the build that produced it: the toolchain
# stamp names the hike executable and the bap plugin objects it loads.
# The BAP library root is explicit: the stamp must cover the plugin
# objects the executable loads, not just the executable.
LIBDIR="$(bap_libdir)" || {
  echo "FATAL: cannot locate the BAP library root: set HIKE_LIBDIR" >&2
  exit 2
}
if [ ! -d "$LIBDIR" ]; then
  echo "FATAL: BAP library root $LIBDIR is not a directory (set HIKE_LIBDIR)" >&2
  exit 2
fi

# The whole toolchain the lift reads: the hike executable and the bap plugin
# objects it loads.  A stamp naming only the hike build would serve a stale
# emission after a bap upgrade or a lifter rebuild — the stale-IR-green class
# the gate exists to stop.
HIKE_BIN="$(hike_exe)" || exit 2
if [ ! -x "$HIKE_BIN" ]; then
  echo "FATAL: hike executable $HIKE_BIN is not executable" >&2
  exit 2
fi
TOOLCHAIN_SHA="$({ sha256sum "$HIKE_BIN" 2>/dev/null
                   [ -n "${HIKE_SIGNATURES:-}" ] && sha256sum "$HIKE_SIGNATURES"
                   find "$LIBDIR" -maxdepth 3 -path '*bap*' \
                     \( -name '*.cmxs' -o -name '*.cmxa' -o -name '*.cma' \) -print 2>/dev/null \
                     | sort | xargs sha256sum 2>/dev/null
                 } | sha256sum | cut -d' ' -f1)"

# Corpus executables in sorted order (skips sources/stubs).
BINS=""
for f in "$CORPUS"/*; do
  [ -f "$f" ] && [ -x "$f" ] || continue
  case "$f" in *.c|*.h) continue ;; esac
  BINS="$BINS $(basename "$f")"
done

if [ -z "$BINS" ]; then
  echo "FATAL: no corpus executables under $CORPUS" >&2
  exit 2
fi

: >"$OUT/diagnostics.txt"
fail=0
n=0
cached=0
skipped=0
for f in $BINS; do
  if is_expected_lift_red "$f"; then
    skipped=$((skipped + 1))
    printf 'SKIP %s (known lift red)\n' "$f"
    continue
  fi
  n=$((n + 1))
  bin_sha="$(sha256sum "$CORPUS/$f" | cut -d' ' -f1)"
  stamp="$OUT/.lift_$f"
  if [ "${FRESH:-0}" != "1" ] && [ -f "$stamp" ] && [ -f "$OUT/out_$f.ll" ] \
     && [ -f "$OUT/rc_$f.txt" ] && [ "$(cat "$stamp")" = "$bin_sha $TOOLCHAIN_SHA" ]; then
    rc="$(cat "$OUT/rc_$f.txt")"
    cached=$((cached + 1))
    printf 'CACHED %s\n' "$f"
  else
    rm -f "$OUT/out_$f.ll"
    timeout 300 "$HIKE_BIN" "$CORPUS/$f" -o "$OUT/out_$f.ll" \
      ${HIKE_SIGNATURES:+--signatures "$HIKE_SIGNATURES"} \
      >"$OUT/stdout_$f.txt" 2>"$OUT/err_$f.txt"
    rc=$?
    echo "$rc" >"$OUT/rc_$f.txt"
    printf '%s\n' "$bin_sha $TOOLCHAIN_SHA" >"$stamp"
    if [ "$rc" -ne 0 ]; then
      printf 'FAIL %s rc=%d\n' "$f" "$rc"
    else
      printf 'PASS %s\n' "$f"
    fi
  fi
  [ "$rc" -eq 0 ] || fail=$((fail + 1))
  {
    printf '===== %s (rc=%d)\n' "$f" "$rc"
    grep -E 'hike:' "$OUT/err_$f.txt" 2>/dev/null
  } >>"$OUT/diagnostics.txt"
done

# One pass over the diagnostics: count + class set together.
diag_stats="$(awk '/^hike:/ { n++; if (match($0, /^hike: [a-z-]+:/)) { c=substr($0, RSTART+6, RLENGTH-7); cls[c]=1 } } END { printf "%d", n; for (k in cls) printf " %s", k }' "$OUT/diagnostics.txt" 2>/dev/null)"
ndiag="${diag_stats%% *}"
classes="${diag_stats#* }"
if [ "${ndiag:-0}" -gt 0 ]; then
  KNOWN_CLASSES="discover emit fp split-blocks summary undef-read"
  for c in $classes; do
    case " $KNOWN_CLASSES " in
      *" $c "*) ;;
      *) echo "FAIL unknown diagnostic class: $c" >&2; fail=$((fail + 1)) ;;
    esac
  done
fi
printf '\nlift: %d binaries, %d failed, %d cached, %d skipped expected; %s diagnostic line(s) [classes: %s]\n' \
  "$n" "$fail" "$cached" "$skipped" "${ndiag:-0}" "${classes:-none}"

[ "$fail" -eq 0 ] || exit 1
