#!/usr/bin/env bash
# Builds the PIE-only test corpus: the -O2 lane, every binary stripped.
# Usage: compile_corpus.sh [out_dir] (default /tmp/corpus-o2)

set -u

HERE="$(cd "$(dirname "$0")" && pwd)"
OUT="${1:-/tmp/corpus-o2}"
cd "$(dirname "$0")/../../src/progs" || exit 1

build_lane () {
  local flags="$1" dest="$2"
  local fail=0
  mkdir -p "$dest"
  for f in *.c; do
    [ "$f" = "list.c" ] && continue
    name="${f%.c}"
    gcc $flags -fno-stack-protector -o "$dest/$name" "$f" -lpthread || { echo "FAIL $name (compile)"; fail=1; }
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
    gcc $flags -fno-stack-protector -o "$dest/$name" "$f" -lpthread || { echo "FAIL $name (compile)"; fail=1; }
  done

  for model in local-exec initial-exec global-dynamic local-dynamic; do
    gcc $flags -fno-stack-protector -ftls-model="$model" \
      -o "$dest/tls_models_$model" synth/tls_models.c -lpthread \
      || { echo "FAIL tls_models_$model (compile)"; fail=1; }
  done

  # One binary per source: a silently-shrunk corpus masks everything
  # downstream.
  local expected built
  expected=$(( $(ls *.c | grep -v '^list\.c$' | wc -l) \
            + $(ls synth/*.c 2>/dev/null | wc -l) + 5 ))
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

  # The class-(b) fixture asserts its own coverage while the symbols
  # are still there (the check reads them): the word is present at its
  # expected offset and no relocation names it.  A missing binary is
  # the check's own failure — guarding on it would let the fixture
  # stop testing silently.
  python3 "$HERE/check_class_b.py" "$dest/class_b_word" || fail=1

  # The corpus arrives the way real binaries do: stripped.  Sections,
  # dynamic symbols and relocations survive; the class-b check above
  # is the guard that stripping never precedes its own assertion.
  local strip_fail=0
  for b in "$dest"/*; do
    [ -x "$b" ] || continue
    objcopy --strip-all "$b" || { echo "FAIL $(basename "$b") (strip)"; strip_fail=1; }
  done
  [ "$strip_fail" -eq 0 ] || exit 1

  [ "$fail" -eq 0 ] || exit 1

  echo "PIE corpus built in $dest:"
  ls -la "$dest"
}

build_lane "-O2" "$OUT"
