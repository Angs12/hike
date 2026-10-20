#!/usr/bin/env bash
# The complete robustness matrix: every native configuration, all four
# TLS models, and LLVM O0/O3/Oz, compared with native runs.

set -u
set -o pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
TREE="$(cd "$HERE/../.." && pwd)"
. "$HERE/lib.sh"

WORK="${HIKE_MATRIX:-/tmp/hike-matrix}"
SRC="$TREE/src/synth"
LLC="${HIKE_LLC:-llc-21}"

if [ "$#" -ne 0 ]; then
  echo "matrix.sh takes no arguments; it always runs the complete matrix" >&2
  exit 2
fi

# One matrix cell: compile and lift every source, then rebuild through
# each LLVM optimization level and compare execution with native.
# Prints "CELL <tag>: <n>/<total> pass[; reds: ...]" and appends the
# per-binary details to $WORK/<tag>.log.
cell () {
  local tag="$1" cc="$2" optflag="$3" sp="$4" strip="$5" model="${6:-}"
  local dir="$WORK/$tag" log="$WORK/$tag.log"
  mkdir -p "$dir"
  : > "$log"

  local srcs=() names=()
  local f name
  for f in "$SRC"/*.c; do
    name="$(basename "$f" .c)"
    srcs+=("$f"); names+=("$name")
  done

  local n=0 total=0 reds=""
  local -A level_pass=([0]=0 [3]=0 [z]=0)
  for i in "${!srcs[@]}"; do
    f="${srcs[$i]}"; name="${names[$i]}"
    if [ -n "$model" ] && [ "$name" != "tls_models" ]; then continue; fi
    total=$((total + 1))
    local bin="$dir/$name" ll="$dir/$name.ll" o="$dir/$name.o" exe="$dir/$name.lifted"
    local extra=()
    if [ "$name" = "list" ]; then
      extra=(-I"$SRC" "$HERE/fixtures/list_main.c")
    fi
    if ! $cc $optflag $sp $model -o "$bin" "$f" "${extra[@]}" -lpthread 2>>"$log"; then
      echo "  $name: COMPILE-FAIL" >> "$log"; reds="$reds $name(compile)"
      continue
    fi
    [ "$strip" = "strip" ] && objcopy --strip-all "$bin"
    if ! timeout 600 "$(hike_exe)" "$bin" -o "$ll" >>"$log" 2>&1; then
      echo "  $name: LIFT-FAIL" >> "$log"; reds="$reds $name(lift)"
      continue
    fi
    if grep -Eq 'call .*@(\"[^\"]*)?(intrinsic:)?(x86:)?(lock|unlock|[mls]fence)(\"|\()' "$ll"; then
      echo "  $name: EXTERNAL-ATOMIC-CALL" >> "$log"; reds="$reds $name(atomic-call)"
      continue
    fi
    local nout="$dir/$name.n.out" lrc nrc
    local repeats=1 run passed=1 lvl level_ok
    case "$name" in tls_pthreads|tls_initialized|tls_models) repeats=20 ;; esac
    for lvl in 0 3 z; do
      local optll="$dir/$name.O$lvl.ll" lout="$dir/$name.O$lvl.l.out"
      if ! opt-21 -O"$lvl" -S "$ll" -o "$optll" 2>>"$log"; then
        echo "  $name: OPT-FAIL O$lvl" >> "$log"
        reds="$reds $name(O$lvl-opt)"; passed=0; continue
      fi
      if ! $LLC -O0 -relocation-model=pic -filetype=obj "$optll" -o "$o" 2>>"$log"; then
        echo "  $name: LLC-FAIL O$lvl" >> "$log"
        reds="$reds $name(O$lvl-llc)"; passed=0; continue
      fi
      if ! gcc -pie "$o" -o "$exe" -lpthread 2>>"$log"; then
        echo "  $name: LINK-FAIL O$lvl" >> "$log"
        reds="$reds $name(O$lvl-link)"; passed=0; continue
      fi
      level_ok=1
      for ((run=1; run<=repeats; run++)); do
        timeout "$HIKE_RUN_TIMEOUT" bash -c 'exec -a prog "$1"' _ "$exe" > "$lout" 2>&1; lrc=$?
        timeout "$HIKE_RUN_TIMEOUT" bash -c 'exec -a prog "$1"' _ "$bin" > "$nout" 2>&1; nrc=$?
        if [ "$lrc" -eq 124 ] || [ "$nrc" -eq 124 ]; then
          echo "  $name: TIMEOUT O$lvl run=$run/$repeats (rc l=$lrc n=$nrc)" >> "$log"
          reds="$reds $name(O$lvl-timeout)"; level_ok=0; break
        fi
        if [ "$lrc" != "$nrc" ] || ! cmp -s "$lout" "$nout"; then
          echo "  $name: DIFF O$lvl run=$run/$repeats (rc l=$lrc n=$nrc)" >> "$log"
          reds="$reds $name(O$lvl-diff-run-$run)"; level_ok=0; break
        fi
        if [ "$lrc" -ge 128 ]; then
          echo "  $name: SIGNAL O$lvl run=$run/$repeats (rc=$lrc)" >> "$log"
          reds="$reds $name(O$lvl-signal)"; level_ok=0; break
        fi
      done
      if [ "$level_ok" = 1 ]; then
        level_pass[$lvl]=$(( ${level_pass[$lvl]} + 1 ))
        echo "  $name: PASS O$lvl runs=$repeats" >> "$log"
      else
        passed=0
      fi
    done
    if [ "$passed" = 1 ]; then
      n=$((n + 1))
    fi
  done
  local levels="" lvl
  for lvl in 0 3 z; do levels="$levels O$lvl=${level_pass[$lvl]}/$total"; done
  if [ -n "$reds" ]; then
    echo "CELL $tag: $n/$total pass; LLVM:$levels; reds:$reds"
  else
    echo "CELL $tag: $n/$total pass; LLVM:$levels"
  fi
  [ "$total" -gt 0 ] && [ "$n" -eq "$total" ]
}

stage_cells () {
  python3 "$HERE/matrix_cases.py" "$1" |
    { failed=0; rows=0
      while IFS=$'\t' read -r tag cc optflag sp strip model; do
        rows=$((rows + 1))
        cell "$tag" "$cc" "$optflag" "$sp" "$strip" "$model" || failed=1
      done
      [ "$rows" -gt 0 ] || exit 1
      exit "$failed"; }
}

failed=0
for stage in opts compilers protector protector-strip strip tls-models; do
  stage_cells "$stage" || failed=1
done
exit "$failed"
