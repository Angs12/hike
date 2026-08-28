#!/usr/bin/env bash
# Tight feedback loop for the 11 failing semantic-gate binaries.
# Re-runs run_semantic_all.sh and prints a per-binary failure fingerprint.
# Usage: check_sem_failures.sh [ir_dir] [out_dir] [corpus_dir]
set -u
IR="${1:-/tmp/heritage_p5}"
OUT="${2:-/tmp/sem_diag}"
CORPUS="${3:-/tmp/corpus}"
# harness.c + setjmp_stub.S live here (read-only reference)
HARNESS="/home/tovpr/Documents/hike/scripts/semantic"
HERE="$HARNESS"

mkdir -p "$OUT"

# 11 known-failing binaries
FAILS=(bitfield_struct factorial many_args mixed_fp_int nested_struct ptr_chain rec_struct struct_by_value va_arg_mixed va_arg_vacopy variadic)

run_one() {
  local f="$1"
  local ll="$IR/out_${f}.ll"
  [ -f "$ll" ] || { echo "$f: NO IR"; return; }
  local native="$CORPUS/$f"
  [ -x "$native" ] || { echo "$f: NO native"; return; }

  # rename
  sed -e 's/@main/@hike_main/g' \
      -e 's/@_dl_relocate_static_pie/@_dl_relocate_static_pie_lifted/g' \
      "$ll" >"$OUT/out_${f}_lifted.ll" || { echo "$f: rename FAIL"; return; }
  # llc
  llc -O0 -filetype=obj "$OUT/out_${f}_lifted.ll" -o "$OUT/out_${f}_lifted.o" 2>"$OUT/llc_${f}.err" || {
    echo "$f: llc FAIL"
    cat "$OUT/llc_${f}.err" | head -3
    return
  }
  STUB=""
  if grep -q '@_setjmp\|@longjmp' "$ll"; then STUB="$HERE/setjmp_stub.S"; fi
  # link
  gcc -O0 -no-pie -o "$OUT/out_${f}_lifted" \
      "$OUT/out_${f}_lifted.o" "$HERE/harness.c" $STUB 2>"$OUT/link_${f}.err" || {
    echo "$f: link FAIL"
    cat "$OUT/link_${f}.err" | head -3
    return
  }

  # run both
  timeout 15 bash -c 'exec -a "$1" "$2"' _ prog "$OUT/out_${f}_lifted" >"$OUT/out_${f}_lifted.out" 2>&1
  local lrc=$?
  timeout 15 bash -c 'exec -a "$1" "$2"' _ prog "$native" >"$OUT/out_${f}_native.out" 2>&1
  local nrc=$?

  # classify
  local verdict="PASS"
  if [ $lrc -eq 124 ] || [ $nrc -eq 124 ]; then
    verdict="TIMEOUT"
  elif [ "$lrc" -ne "$nrc" ]; then
    verdict="RC_DIFF(lrc=$lrc nrc=$nrc)"
  elif ! cmp -s "$OUT/out_${f}_lifted.out" "$OUT/out_${f}_native.out"; then
    # classify the diff
    local ls=$(wc -c <"$OUT/out_${f}_lifted.out")
    local ns=$(wc -c <"$OUT/out_${f}_native.out")
    if [ "$ls" -eq 0 ]; then
      verdict="EMPTY_OUT(rc=$lrc)"
    else
      local d=$(diff "$OUT/out_${f}_native.out" "$OUT/out_${f}_lifted.out" | head -1 | head -c 70)
      verdict="OUT_DIFF(${ns}b_vs_${ls}b)"
    fi
  fi
  printf "%-22s %s\n" "$f" "$verdict"
}

# Header
echo "=== semantic-gate failures — $(date +%H:%M:%S) ==="
for f in "${FAILS[@]}"; do
  run_one "$f"
done
