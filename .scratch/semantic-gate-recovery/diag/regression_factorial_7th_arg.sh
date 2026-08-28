#!/usr/bin/env bash
# Regression test for the 7th-onward arg passing bug (the alphabetical-register-order
# signature emission + missing caller-side store for stack args).
#
# Symptom: the lifted factorial binary returns a non-deterministic exit code
# (0..224) instead of the correct 25 (= inc(24, 0, 0, 0, 0, 0, 1) = 4! + 1).
# Native factorial returns 25 reliably.
#
# Usage: regression_factorial_7th_arg.sh [ir_dir] [harness_dir] [out_dir]
set -u
IR="${1:-/tmp/heritage_p5}"
HARNESS="${2:-/home/tovpr/Documents/hike/scripts/semantic}"
OUT="${3:-/tmp/sem_diag}"

LL="$IR/out_factorial.ll"
NATIVE=/tmp/corpus/factorial
EXPECTED=25
RUNS=10
PASS=0
FAIL=0
declare -a RCS=()

if [ ! -f "$LL" ]; then echo "FAIL: no IR at $LL"; exit 1; fi
if [ ! -x "$NATIVE" ]; then echo "FAIL: no native at $NATIVE"; exit 1; fi

# rebuild lifted binary
sed -e 's/@main/@hike_main/g' \
    -e 's/@_dl_relocate_static_pie/@_dl_relocate_static_pie_lifted/g' \
    "$LL" >"$OUT/factorial_lifted_test.ll"
llc -O0 -filetype=obj "$OUT/factorial_lifted_test.ll" -o "$OUT/factorial_lifted_test.o"
gcc -O0 -no-pie -o "$OUT/factorial_lifted_test" \
    "$OUT/factorial_lifted_test.o" "$HARNESS/harness.c"

# verify native
nrc=$("$NATIVE" >/dev/null 2>&1; echo $?)
if [ "$nrc" -ne "$EXPECTED" ]; then
  echo "FAIL: native factorial returned $nrc, expected $EXPECTED (corpus build broken?)"
  exit 2
fi

# run lifted 10x, assert rc == EXPECTED
for i in $(seq 1 $RUNS); do
  lrc=$("$OUT/factorial_lifted_test" >/dev/null 2>&1; echo $?)
  RCS+=("$lrc")
  if [ "$lrc" -eq "$EXPECTED" ]; then
    PASS=$((PASS + 1))
  else
    FAIL=$((FAIL + 1))
  fi
done

# summary
UNIQ=$(printf '%s\n' "${RCS[@]}" | sort -u | tr '\n' ' ')
echo "factorial regression: $PASS/$RUNS PASS, expected rc=$EXPECTED, observed rcs=[$UNIQ]"
if [ $FAIL -gt 0 ]; then
  echo "FAIL: lifted factorial did not return the expected rc=$EXPECTED"
  exit 1
fi
echo "PASS"
exit 0
