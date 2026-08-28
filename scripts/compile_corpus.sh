#!/usr/bin/env bash
# Phase 5 (validation): compile the full test corpus PIE-ONLY (user
# directive 2026-08-26: "only work on PIE with no fallbacks"): plain
# gcc -O0 -fno-stack-protector = distro-style ET_DYN / PIE executables.
# There is NO -no-pie mode anymore; every consumer of this corpus
# (run_corpus.sh, check_allocas.sh, semantic/*, the probes) receives
# ET_DYN inputs exclusively.
#
# Usage: compile_corpus.sh [out_dir]   (default /tmp/corpus)
#
# list.c is a library (no main) — linked with a trivial main stub.
# The synth sources live in src/progs/synth/.

set -u

OUT="${1:-/tmp/corpus}"
mkdir -p "$OUT"
cd "$(dirname "$0")/../src/progs" || exit 1

for f in *.c; do
  [ "$f" = "list.c" ] && continue
  name="${f%.c}"
  gcc -O0 -fno-stack-protector -o "$OUT/$name" "$f" || echo "FAIL $name"
done

# list.c: ADT library — needs a main stub to link.  The stub source
# lives in $OUT/.build/ (NOT the corpus dir itself: run_corpus.sh and
# the probes glob the corpus dir, and a stray .c there used to need a
# `grep -v stub` band-aid in the listing below).
mkdir -p "$OUT/.build"
printf 'int main(void){return 0;}\n' > "$OUT/.build/list_main_stub.c"
gcc -O0 -fno-stack-protector -o "$OUT/list" list.c "$OUT/.build/list_main_stub.c" \
  || echo "FAIL list"

# All synth sources (incl. new corpus-expansion tests) are picked up automatically.
for f in synth/*.c; do
  name="$(basename "$f" .c)"
  gcc -O0 -fno-stack-protector -o "$OUT/$name" "$f" || echo "FAIL $name"
done

# Guard: the corpus MUST be ET_DYN (PIE). An accidental non-PIE binary
# here would silently reintroduce the ET_EXEC recipe downstream.
pie_fail=0
for b in "$OUT"/*; do
  [ -x "$b" ] || continue
  file -b "$b" | grep -q 'ELF 64-bit.*pie executable' || { echo "FAIL $(basename "$b"): NOT PIE ($(file -b "$b" | cut -d, -f1))"; pie_fail=1; }
done
[ "$pie_fail" -eq 0 ] || exit 1

echo "PIE corpus built in $OUT:"
ls -la "$OUT"
