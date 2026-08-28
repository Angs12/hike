#!/usr/bin/env bash
# Poor-man's lift profiler (perf_event_paranoid=3 blocks perf on this box):
# repeatedly samples the running pipeline's stack via gdb batch backtraces
# and aggregates the hottest OCaml frames.  Uses the dune-built stage_timer
# (compiled with -g), so frames resolve to Hike__*/Cbat_* functions.
#
# Usage: profile_lift.sh <binary> [subname] [seconds-budget]
set -u
BIN="${1:?binary}"; SUB="${2:-main}"; BUDGET="${3:-90}"
cd "$(dirname "$0")/.."
export OCAMLRUNPARAM="${OCAMLRUNPARAM:-s=8M}"

OUT=/tmp/opencode/profile-$(basename "$BIN")
mkdir -p "$OUT"; : > "$OUT/samples.txt"

dune exec zz_scratch_probe/stage_timer.exe -- "$BIN" "$SUB" \
    > "$OUT/stages.txt" 2>&1 &
PID=$!
sleep 3   # let it reach the analysis stages

n=0
while kill -0 $PID 2>/dev/null && [ "$(date +%s)" -lt "$(( $(date +%s) ))" ]; do :; done 2>/dev/null # noop guard
while kill -0 $PID 2>/dev/null; do
    gdb -p "$PID" -batch -ex 'bt 30' --readnever 2>/dev/null \
        | grep '^#' \
        | sed -E 's/^#[0-9]+ +0x[0-9a-f]+ in //; s/\(.*//; s/ .*//; s/\.$//' \
        | grep -vE '^$|^__|^_IO|^malloc|^free|^caml_alloc|^caml_call|^caml_c_cal' \
        >> "$OUT/samples.txt"
    n=$((n+1))
    sleep 0.35
done
wait $PID || true

echo "=== $BIN ($SUB) — stage times ==="
cat "$OUT/stages.txt" | grep -E "STAGE|TOTAL"
echo "=== sampled stacks: $n samples ==="
sort "$OUT/samples.txt" | uniq -c | sort -rn | head -25
