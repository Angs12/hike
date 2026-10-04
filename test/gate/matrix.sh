#!/usr/bin/env bash
# The robustness matrix (T18): the corpus under every optimization
# level, compiler, stack-protector mode, and consumer recompile level —
# harness-free (llc pic, gcc -pie, stdout+rc byte-diffed against the
# native binary), stripped and unstripped.
#
# Usage: matrix.sh <stage>
#   stages: opts compilers protector recomp strip
# Each stage prints one line per cell: PASS/FAIL counts + the red list.

set -u

HERE="$(cd "$(dirname "$0")" && pwd)"
TREE="$(cd "$HERE/../.." && pwd)"
. "$HERE/lib.sh"

WORK="${HIKE_MATRIX:-/tmp/hike-matrix}"
SRC="$TREE/src/progs"
OPT="${HIKE_OPT:-opt-21}"
LLC="${HIKE_LLC:-llc-21}"

provenance_ok "$TREE" || exit $?

# One matrix cell: compile every corpus source with $1, lift each
# binary, llc+link harness-free, run both, byte-diff stdout and rc.
# Prints "CELL <tag>: <n>/<total> pass[; reds: ...]" and appends the
# per-binary details to $WORK/<tag>.log.
cell () {
  local tag="$1" cc="$2" optflag="$3" sp="$4" strip="$5"
  local dir="$WORK/$tag" log="$WORK/$tag.log"
  mkdir -p "$dir"
  : > "$log"

  local srcs=() names=()
  local f name
  for f in "$SRC"/*.c; do
    name="$(basename "$f" .c)"
    [ "$name" = "list" ] && continue
    srcs+=("$f"); names+=("$name")
  done
  for f in "$SRC"/synth/*.c; do
    name="$(basename "$f" .c)"
    srcs+=("$f"); names+=("$name")
  done

  local n=0 total=0 reds=""
  for i in "${!srcs[@]}"; do
    f="${srcs[$i]}"; name="${names[$i]}"
    total=$((total + 1))
    local bin="$dir/$name" ll="$dir/$name.ll" o="$dir/$name.o" exe="$dir/$name.lifted"
    if ! $cc $optflag $sp -o "$bin" "$f" 2>>"$log"; then
      echo "  $name: COMPILE-FAIL" >> "$log"; reds="$reds $name(compile)"
      continue
    fi
    [ "$strip" = "strip" ] && objcopy --strip-all "$bin"
    if ! OCAMLPATH="$TREE/_build/install/default/lib" bap "$bin" \
         --pass=hike-convlir --hike-output-file="$ll" \
         --cache-dir="$dir/.cache-$name" >>"$log" 2>&1; then
      echo "  $name: LIFT-FAIL" >> "$log"; reds="$reds $name(lift)"
      continue
    fi
    if ! $LLC -O0 -relocation-model=pic -filetype=obj "$ll" -o "$o" 2>>"$log"; then
      echo "  $name: LLC-FAIL" >> "$log"; reds="$reds $name(llc)"
      continue
    fi
    if ! gcc -pie "$o" -o "$exe" 2>>"$log"; then
      echo "  $name: LINK-FAIL" >> "$log"; reds="$reds $name(link)"
      continue
    fi
    local lout="$dir/$name.l.out" nout="$dir/$name.n.out" lrc nrc
    "$exe" > "$lout" 2>/dev/null; lrc=$?
    "$bin" > "$nout" 2>/dev/null; nrc=$?
    if [ "$lrc" = "$nrc" ] && cmp -s "$lout" "$nout"; then
      n=$((n + 1)); echo "  $name: PASS" >> "$log"
    else
      echo "  $name: DIFF (rc l=$lrc n=$nrc)" >> "$log"; reds="$reds $name(diff)"
    fi
  done
  if [ -n "$reds" ]; then
    echo "CELL $tag: $n/$total pass;reds:$reds"
  else
    echo "CELL $tag: $n/$total pass"
  fi
}

stage_opts () {
  for o in O0 O1 O2 O3 Os Oz; do
    cell "gcc-$o-nosp-nostrip" gcc "-$o" "-fno-stack-protector" nostrip
  done
}

stage_compilers () {
  for cc in gcc clang; do
    for o in O0 O2; do
      cell "$cc-$o-nosp-nostrip" "$cc" "-$o" "-fno-stack-protector" nostrip
    done
  done
}

stage_protector () {
  for sp in "-fno-stack-protector" "-fstack-protector-all"; do
    for o in O0 O2; do
      local t="gcc-$o-${sp//-/}-nostrip"
      cell "$t" gcc "-$o" "$sp" nostrip
    done
  done
}

stage_strip () {
  for o in O0 O1 O2 O3 Os Oz; do
    cell "gcc-$o-nosp-strip" gcc "-$o" "-fno-stack-protector" strip
  done
}

# The recompile sweep runs the semantic gate's own machinery over the
# recorded -O2 stripped corpus emissions, one consumer level at a time.
stage_recomp () {
  local corpus="${HIKE_CORPUS:-/tmp/corpus-o2}"
  for lvl in 0 1 2 3 s; do
    local out="$WORK/recomp-$lvl"
    mkdir -p "$out"
    HIKE_OPT_LEVEL="$lvl" "$HERE/semantic/run_semantic.sh" "$corpus" \
      "${HIKE_EMIT:-/tmp/hike-emit}" "$out" > "$out/summary.log" 2>&1
    local line
    line="$(grep 'semantic-opt:' "$out/summary.log" | tail -1)"
    echo "CELL recomp-$lvl: ${line:-NO-RESULT}"
  done
}

case "${1:-}" in
  opts)      stage_opts ;;
  compilers) stage_compilers ;;
  protector) stage_protector ;;
  strip)     stage_strip ;;
  recomp)    stage_recomp ;;
  *) echo "usage: matrix.sh <opts|compilers|protector|strip|recomp>" >&2; exit 2 ;;
esac
