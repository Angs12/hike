#!/usr/bin/env bash
# Lifts one coreutils binary; the pipeline calls it serially (parallel
# lifts OOM the box).
set -u
. "$(cd "$(dirname "$0")" && pwd)/lib.sh"
name="$1"
BINS="$2"; IR="$3"; OUT="$4"; TIMES="$5"; LLOG="$6"
b="$BINS/$name"; ll="$IR/out_$name.ll"
t0=$(date +%s.%N)
if timeout 600 "$(hike_exe)" "$b" -o "$ll" ${HIKE_SIGNATURES:+--signatures "$HIKE_SIGNATURES"} \
   > "$OUT/$name.lift.log" 2>&1 \
   && [ -s "$ll" ]; then
    echo "OK   $name" >> "$LLOG"
    t1=$(date +%s.%N)
    awk -v n="$name" -v a="$t0" -v b="$t1" 'BEGIN{printf "%s\t%.2f\n", n, b-a}' >> "$TIMES"
else
    echo "FAIL $name ($(grep -m1 -oE 'hike:.*' "$OUT/$name.lift.log" | head -c 160))" >> "$LLOG"
    rm -f "$ll"
fi
