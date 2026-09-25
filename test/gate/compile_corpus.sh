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
cd "$(dirname "$0")/../../src/progs" || exit 1

build_lane () {
  local flags="$1" dest="$2"
  local fail=0
  mkdir -p "$dest"
  for f in *.c; do
    [ "$f" = "list.c" ] && continue
    name="${f%.c}"
    gcc $flags -fno-stack-protector -o "$dest/$name" "$f" || { echo "FAIL $name (compile)"; fail=1; }
  done

  # list.c needs a main stub; the stub lives in $dest/.build/ so the
  # corpus dir holds binaries only.
  mkdir -p "$dest/.build"
  printf 'int main(void){return 0;}\n' > "$dest/.build/list_main_stub.c"
  gcc $flags -fno-stack-protector -o "$dest/list" list.c "$dest/.build/list_main_stub.c" \
    || { echo "FAIL list (compile)"; fail=1; }

  # synth sources are picked up automatically.
  for f in synth/*.c; do
    name="$(basename "$f" .c)"
    gcc $flags -fno-stack-protector -o "$dest/$name" "$f" || { echo "FAIL $name (compile)"; fail=1; }
  done

  # One binary per source: a silently-shrunk corpus masks everything
  # downstream.
  local expected built
  expected=$(( $(ls *.c | grep -v '^list\.c$' | wc -l) \
            + $(ls synth/*.c 2>/dev/null | wc -l) + 1 ))
  built=$(find "$dest" -maxdepth 1 -type f -perm -u+x | wc -l)
  if [ "$built" -ne "$expected" ]; then
    echo "FAIL: $built binaries built, $expected sources (see the FAIL lines above)"
    fail=1
  fi

  # Guard: every binary must be ET_DYN (PIE) — both lanes, hard-fail
  # on the ELF header's own word, never file(1) prose.
  local pie_fail=0
  for b in "$dest"/*; do
    [ -x "$b" ] || continue
    if ! readelf -h "$b" 2>/dev/null | grep -qE 'Type:[[:space:]]+DYN'; then
      echo "FAIL $(basename "$b"): NOT PIE"
      pie_fail=1
    fi
  done
  [ "$pie_fail" -eq 0 ] || exit 1
  [ "$fail" -eq 0 ] || exit 1

  echo "PIE corpus built in $dest:"
  ls -la "$dest"
}

if [ "${OUT%-o2}" != "$OUT" ]; then
  build_lane "-O2" "$OUT"
else
  build_lane "-O0" "$OUT"
  build_lane "-O2" "$OUT-o2"
fi
