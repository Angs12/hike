#!/usr/bin/env bash
# Builds the PIE-only test corpus.
# Usage: compile_corpus.sh [out_dir] (default /tmp/corpus)
#
# Two lanes, one corpus dir each:
#   -O0 (the primary corpus, distro-style PIE)
#   -O2 (the optimization lane: same sources, gcc -O2 — the -O2 gates are
#        semantic + allocas; no IR baseline exists, snapshotting would pin
#        bugs)
# The -O2 lane writes <out>-o2 next to the -O0 dir unless OUT already ends
# in -o2 (then it is the only lane built).

set -u

OUT="${1:-/tmp/corpus}"
cd "$(dirname "$0")/../src/progs" || exit 1

build_lane () {
  local flags="$1" dest="$2"
  mkdir -p "$dest"
  for f in *.c; do
    [ "$f" = "list.c" ] && continue
    name="${f%.c}"
    gcc $flags -fno-stack-protector -o "$dest/$name" "$f" || echo "FAIL $name"
  done

  # list.c needs a main stub; the stub lives in $dest/.build/ so the
  # corpus dir holds binaries only.
  mkdir -p "$dest/.build"
  printf 'int main(void){return 0;}\n' > "$dest/.build/list_main_stub.c"
  gcc $flags -fno-stack-protector -o "$dest/list" list.c "$dest/.build/list_main_stub.c" \
    || echo "FAIL list"

  # synth sources are picked up automatically.
  for f in synth/*.c; do
    name="$(basename "$f" .c)"
    gcc $flags -fno-stack-protector -o "$dest/$name" "$f" || echo "FAIL $name"
  done

  # Guard: every binary must be ET_DYN (PIE) — both lanes, hard-fail.
  local pie_fail=0
  for b in "$dest"/*; do
    [ -x "$b" ] || continue
    file -b "$b" | grep -q 'ELF 64-bit.*pie executable' || { echo "FAIL $(basename "$b"): NOT PIE ($(file -b "$b" | cut -d, -f1))"; pie_fail=1; }
  done
  [ "$pie_fail" -eq 0 ] || exit 1

  echo "PIE corpus built in $dest:"
  ls -la "$dest"
}

if [ "${OUT%-o2}" != "$OUT" ]; then
  build_lane "-O2" "$OUT"
else
  build_lane "-O0" "$OUT"
  build_lane "-O2" "$OUT-o2"
fi
