#!/usr/bin/env bash
# Builds the VLA fixtures (src/synth/vla_*.c, alloca_vla.c) with GCC
# and Clang at several optimization levels, lifts each with the
# uninstalled drive executable, rebuilds it through opt/llc/gcc and
# compares stdout and exit code with the native binary for 0, 1 and 3
# extra arguments.
#
# Usage: vla_fixtures.sh [out_dir] [levels]
#   out_dir  default /tmp/vla-fixtures
#   levels   default "O0 O2"; e.g. "O0 O1 O2 O3 Os Oz"
# Runs one lift at a time. Exit 1 if any fixture fails.

set -u
set -o pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
OUT="${1:-/tmp/vla-fixtures}"
LEVELS="${2:-O0 O2}"
SRC="$ROOT/src/synth"
mkdir -p "$OUT/bin" "$OUT/lift"

dune build --root "$ROOT" -j 4 src/drive/main.exe 2>&1 | tail -3 || exit 1

fixtures="alloca_vla vla_loop vla_call vla_iter vla_2d vla_big vla_nested vla_thread vla_clash"
fail=0
for cc in gcc clang; do
  for lvl in $LEVELS; do
    for f in $fixtures; do
      extra=""
      [ "$f" = vla_clash ] && extra="-fstack-clash-protection"
      n="$f.$cc.$lvl"
      $cc -$lvl $extra -fno-stack-protector -fPIE -pie -o "$OUT/bin/$n" \
        "$SRC/$f.c" -lpthread 2>"$OUT/bin/$n.cc.err" || { echo "$n: COMPILE-FAIL"; fail=1; continue; }
      objcopy --strip-all "$OUT/bin/$n"
      b="$OUT/bin/$n"
      dune exec --no-build --root "$ROOT" src/drive/main.exe -- "$b" \
        -o "$OUT/lift/$n.ll" >"$OUT/lift/$n.out" 2>"$OUT/lift/$n.err"
      rc=$?
      res="lift rc=$rc"
      if [ "$rc" -ne 0 ]; then
        res="$res $(grep -m1 'hike:' "$OUT/lift/$n.err" | cut -c1-150)"; fail=1
      elif opt-19 -O2 -S "$OUT/lift/$n.ll" -o "$OUT/lift/$n.opt.ll" 2>"$OUT/lift/$n.build.err" \
        && llc -relocation-model=pic -filetype=obj "$OUT/lift/$n.opt.ll" -o "$OUT/lift/$n.o" 2>>"$OUT/lift/$n.build.err" \
        && gcc -O0 -pie -o "$OUT/lift/$n.bin" "$OUT/lift/$n.o" -lpthread 2>>"$OUT/lift/$n.build.err"; then
        for a in "" "x" "x y z"; do
          l=$(timeout 15 "$OUT/lift/$n.bin" $a 2>&1; echo "rc=$?")
          nv=$(timeout 15 "$b" $a 2>&1; echo "rc=$?")
          if [ "$l" == "$nv" ]; then res="$res pass"; else res="$res FAIL"; fail=1; fi
        done
      else
        res="$res BUILD-FAIL"; fail=1
      fi
      echo "$n: $res"
    done
  done
done
exit "$fail"
