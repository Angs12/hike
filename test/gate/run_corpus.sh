#!/usr/bin/env bash
# Runs hike-convlir over the corpus, asserts every lift exits 0, and writes
# the full diagnostics catalogue.
#
# Usage: run_corpus.sh [corpus_dir] [out_dir]
#
# Per binary: out_<name>.ll / err_<name>.txt / stdout_<name>.txt /
# rc_<name>.txt.  Plus diagnostics.txt (every `hike:` line, every class)
# and a one-line summary.
#
# The lift is INCREMENTAL: an emission is reused when the plugin and the
# binary are both unchanged — the lift's only inputs — recorded as a stamp
# beside it.  FRESH=1 forces a full re-lift.  bap's own cache stays disabled
# (--no-cache): it cannot tell a stale rewrite from a fresh one, while this
# stamp is keyed on exactly the two things the lift reads.
#
# STRICT: a non-zero lift rc is a loud failure (exit 1).  Diagnostics are
# catalogue-only: recorded and summarised, never asserted on.

set -u

HERE="$(cd "$(dirname "$0")" && pwd)"

CORPUS="${1:-/tmp/corpus-o2}"
OUT="${2:-/tmp/hike-emit}"
mkdir -p "$OUT"

if [ -z "$(ls -A "$CORPUS" 2>/dev/null)" ]; then
  echo "FATAL: no corpus at $CORPUS (run the corpus gate first)" >&2
  exit 2
fi

# Bind every emission in $OUT to the plugin that produced it: a later
# consumer compares this copy with the installed plugin's provenance.
LIBDIR="$(opam var lib 2>/dev/null || true)"
PROV="$LIBDIR/hike/hike.cmxs.provenance"
if [ ! -f "$PROV" ]; then
  echo "FATAL: no installed plugin provenance — run src/record_provenance.sh" >&2
  exit 2
fi
cp "$PROV" "$OUT/.plugin_provenance"
PROV_SHA="$(sha256sum "$PROV" | cut -d' ' -f1)"

# The whole toolchain the lift reads: the hike plugin (through its
# provenance, which covers the installed bundle), the bap binary, and bap's
# own plugin objects.  A stamp naming only the hike plugin would serve a
# stale emission after a bap upgrade or a lifter rebuild — the
# stale-IR-green class the gate exists to stop.
BAP_BIN="$(command -v bap 2>/dev/null || true)"
TOOLCHAIN_SHA="$({ sha256sum "$BAP_BIN" 2>/dev/null
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
for f in $BINS; do
  n=$((n + 1))
  bin_sha="$(sha256sum "$CORPUS/$f" | cut -d' ' -f1)"
  stamp="$OUT/.lift_$f"
  if [ "${FRESH:-0}" != "1" ] && [ -f "$stamp" ] && [ -f "$OUT/out_$f.ll" ] \
     && [ -f "$OUT/rc_$f.txt" ] && [ "$(cat "$stamp")" = "$bin_sha $PROV_SHA $TOOLCHAIN_SHA" ]; then
    rc="$(cat "$OUT/rc_$f.txt")"
    cached=$((cached + 1))
    printf 'CACHED %s\n' "$f"
  else
    timeout 300 bap "$CORPUS/$f" --pass=hike-convlir --no-cache \
      --hike-output-file="$OUT/out_$f.ll" \
      >"$OUT/stdout_$f.txt" 2>"$OUT/err_$f.txt"
    rc=$?
    echo "$rc" >"$OUT/rc_$f.txt"
    printf '%s\n' "$bin_sha $PROV_SHA $TOOLCHAIN_SHA" >"$stamp"
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
printf '\nlift: %d binaries, %d failed, %d cached; %s diagnostic line(s) [classes: %s]\n' \
  "$n" "$fail" "$cached" "${ndiag:-0}" "${classes:-none}"

[ "$fail" -eq 0 ] || exit 1
