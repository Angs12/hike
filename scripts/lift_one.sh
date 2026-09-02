#!/usr/bin/env bash
# lift_one.sh — one coreutils binary's hike lift (the pipeline's serial
# worker; kept as a standalone file since the 2026-09-01 serial-only
# directive — the old xargs -P parallel form is DELETED, parallel lifts
# OOM the box).
set -u
name="$1"
BINS="$2"; IR="$3"; OUT="$4"; TIMES="$5"; LLOG="$6"
b="$BINS/$name"; ll="$IR/out_$name.ll"
t0=$(date +%s.%N)
if timeout 600 bap "$b" --no-cache --pass=hike-convlir \
       --hike-output-file="$ll" > "$OUT/$name.bap.log" 2>&1 \
   && [ -s "$ll" ]; then
    echo "OK   $name" >> "$LLOG"
    t1=$(date +%s.%N)
    awk -v n="$name" -v a="$t0" -v b="$t1" 'BEGIN{printf "%s\t%.2f\n", n, b-a}' >> "$TIMES"
else
    echo "FAIL $name ($(grep -m1 -oE 'hike:.*|The pass .* failed.*' "$OUT/$name.bap.log" | head -c 160))" >> "$LLOG"
    rm -f "$ll"
fi
