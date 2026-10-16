#!/usr/bin/env bash
# The lift and semantic gates over a corpus, through the UNINSTALLED
# drive executable (`dune exec`): lift each binary, rebuild it through
# opt-21 -O<level>, llc and gcc -pie, then diff stdout and exit status
# against the native binary (no arguments).  One lift at a time.
#
# Usage: corpus_uninstalled.sh [corpus_dir] [out_dir]
#   corpus_dir  default /tmp/corpus-o2
#   out_dir     default /tmp/corpus-uninstalled
#   HIKE_OPT_LEVEL  optimization level for the consumer opt (default 2)
# Prints one line per binary and a summary; also runs check_allocas.sh over
# the emitted IR.  Exit 0 iff every lift, build and comparison passed.

set -u

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
CORPUS="${1:-/tmp/corpus-o2}"
OUT="${2:-/tmp/corpus-uninstalled}"
LEVEL="${HIKE_OPT_LEVEL:-2}"
mkdir -p "$OUT"

dune build --root "$ROOT" -j 4 src/drive/main.exe 2>&1 | tail -3

pass=0
fail=0
for b in "$CORPUS"/*; do
  [ -f "$b" ] && [ -x "$b" ] || continue
  n="$(basename "$b")"
  ll="$OUT/out_$n.ll"
  if ! timeout 900 dune exec --no-build --root "$ROOT" src/drive/main.exe -- \
        "$b" -o "$ll" >"$OUT/$n.stdout" 2>"$OUT/$n.err"; then
    echo "FAIL $n (lift: $(grep -m1 'hike:' "$OUT/$n.err" | cut -c1-120))"
    fail=$((fail + 1))
    continue
  fi
  if ! opt-21 -O"$LEVEL" -S "$ll" -o "$OUT/$n.opt.ll" 2>"$OUT/$n.build" \
     || ! llc -relocation-model=pic -filetype=obj "$OUT/$n.opt.ll" -o "$OUT/$n.o" 2>>"$OUT/$n.build" \
     || ! gcc -O0 -pie -o "$OUT/$n.bin" "$OUT/$n.o" -lpthread 2>>"$OUT/$n.build"; then
    echo "FAIL $n (build)"
    fail=$((fail + 1))
    continue
  fi
  timeout 15 bash -c 'exec -a prog "$1"' _ "$OUT/$n.bin" >"$OUT/$n.lifted.out" 2>&1
  lrc=$?
  timeout 15 bash -c 'exec -a prog "$1"' _ "$b" >"$OUT/$n.native.out" 2>&1
  nrc=$?
  if [ "$lrc" -eq "$nrc" ] && cmp -s "$OUT/$n.lifted.out" "$OUT/$n.native.out"; then
    echo "PASS $n"
    pass=$((pass + 1))
  else
    echo "FAIL $n (lifted rc=$lrc native rc=$nrc)"
    fail=$((fail + 1))
  fi
done

echo "corpus: $pass passed, $fail failed"
bash "$ROOT/test/gate/check_allocas.sh" "$OUT" | grep -E "FAIL|check_allocas:"
[ "$fail" -eq 0 ]
