#!/usr/bin/env bash
# Native-vs-lifted harness over an explicit binary list (the 8-bin oracle).
# Usage: run_semantic.sh [corpus_dir] [ir_dir] [out_dir] [extra_bins]
# Renames @main, llc -O0, links harness.c (+ setjmp_stub.S for setjmp
# users: lifted jmp_bufs hold model addresses real glibc would deref),
# byte-diffs stdout. Never re-emits; operates on run_corpus.sh output.
# The lifted link stays -no-pie: a linker constraint of the harness
# artifact (baked absolute constants + extern_weak refs reject DT_TEXTREL).
# Exit 0 iff every binary passes.
set -u

# Regression baseline lives in the repo, so bare runs need no /tmp state.
HERE="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "$HERE/../.." && pwd)"

CORPUS="${1:-/tmp/corpus}"
IR="${2:-$REPO_ROOT/baselines/heritage_baseline_copy}"
OUT="${3:-/tmp/sem_out}"
# Optional 4th arg: extra ad-hoc binaries beyond the regression set.
EXTRA_BINS="${4:-}"
mkdir -p "$OUT"

# Explicit list: each entry pins a converted shape (arg-area GEPs, RMW
# stores, bounded-store regression). Ad-hoc extras join the same gate.
BINS="setjmp_loop struct_arr_dynidx out_struct deep_recursion array_local factorial many_args rmw_oob"

# Empty by default, so the regression set stays exactly eight binaries.
BINS="$BINS $EXTRA_BINS"

fail=0

for name in $BINS; do
# out_struct lifts corpus binary `struct` (names differ).
    case "$name" in
    out_struct) src=struct ;;
    *) src="$name" ;;
    esac
    ll="$IR/out_$src.ll"
    native="$CORPUS/$src"
    if [ ! -f "$ll" ] || [ ! -x "$native" ]; then
        echo "MISSING $name ($ll or $native)"
        fail=1
        continue
    fi

    # Rename the module entry + crt1-colliding symbol, then compile.
    sed -e 's/@main/@hike_main/g' \
        -e 's/@_dl_relocate_static_pie/@_dl_relocate_static_pie_lifted/g' \
        "$ll" > "$OUT/${name}_lifted.ll" || { echo "FAIL $name (rename)"; fail=1; continue; }
    llc -O0 -filetype=obj "$OUT/${name}_lifted.ll" -o "$OUT/${name}_lifted.o" \
        || { echo "FAIL $name (llc)"; fail=1; continue; }

    # Setjmp stub only when the module uses setjmp/longjmp.
    STUB=""
    if grep -q '@_setjmp\|@longjmp' "$ll"; then
        STUB="$HERE/setjmp_stub.S"
    fi
    gcc -O0 -no-pie -o "$OUT/${name}_lifted" \
        "$OUT/${name}_lifted.o" "$HERE/harness.c" $STUB \
        || { echo "FAIL $name (link)"; fail=1; continue; }

    # Run both and compare stdout byte-for-byte.
    "$OUT/${name}_lifted" > "$OUT/${name}_lifted.out" 2>&1; lrc=$?
    "$native"            > "$OUT/${name}_native.out" 2>&1; nrc=$?

    if [ "$nrc" -eq "$lrc" ] \
       && diff -q "$OUT/${name}_native.out" "$OUT/${name}_lifted.out" >/dev/null; then
        echo "PASS $name (stdout byte-identical)"
    else
        echo "FAIL $name (native rc=$nrc vs lifted rc=$lrc; stdout diff:)"
        diff "$OUT/${name}_native.out" "$OUT/${name}_lifted.out"
        fail=1
    fi
done

exit "$fail"
