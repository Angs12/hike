#!/usr/bin/env bash
# Builds the PIE-only test corpus (plain gcc -O0 -fno-stack-protector).
# Usage: compile_corpus.sh [out_dir] (default /tmp/corpus)

set -u

OUT="${1:-/tmp/corpus}"
mkdir -p "$OUT"
cd "$(dirname "$0")/../src/progs" || exit 1

for f in *.c; do
  [ "$f" = "list.c" ] && continue
  name="${f%.c}"
  gcc -O0 -fno-stack-protector -o "$OUT/$name" "$f" || echo "FAIL $name"
done

# list.c needs a main stub; the stub lives in $OUT/.build/ so the
# corpus dir holds binaries only.
mkdir -p "$OUT/.build"
printf 'int main(void){return 0;}\n' > "$OUT/.build/list_main_stub.c"
gcc -O0 -fno-stack-protector -o "$OUT/list" list.c "$OUT/.build/list_main_stub.c" \
  || echo "FAIL list"

# synth sources are picked up automatically.
for f in synth/*.c; do
  name="$(basename "$f" .c)"
  gcc -O0 -fno-stack-protector -o "$OUT/$name" "$f" || echo "FAIL $name"
done

# Guard: every binary must be ET_DYN (PIE).
pie_fail=0
for b in "$OUT"/*; do
  [ -x "$b" ] || continue
  file -b "$b" | grep -q 'ELF 64-bit.*pie executable' || { echo "FAIL $(basename "$b"): NOT PIE ($(file -b "$b" | cut -d, -f1))"; pie_fail=1; }
done
[ "$pie_fail" -eq 0 ] || exit 1

echo "PIE corpus built in $OUT:"
ls -la "$OUT"
