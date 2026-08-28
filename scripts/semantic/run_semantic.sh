#!/usr/bin/env bash
# Semantic native-vs-lifted harness for the heritage port.
#
# Runbook style: this complements scripts/run_corpus.sh (plugin emission
# + per-binary table) and scripts/check_allocas.sh (structural check);
# where those verify that the plugin EMITS, this verifies that the
# emitted module SEMANTICALLY BEHAVES like the native binary.
#
# IMPORTANT — the plugin must be the FRESH bundle: a stale installed
# plugin silently runs old code, so the out_*.ll inputs must have been
# emitted by the current build (dune build @install + pack/install, see
# .slim/deepwork/corpus-expand.md P4-C).  This script never re-emits;
# it operates on the out_<name>.ll left behind by run_corpus.sh.
#
# Per binary in BINS:
#   1. rename @main -> @hike_main and @_dl_relocate_static_pie ->
#      @_dl_relocate_static_pie_lifted (avoids the crt1 entry collision);
#      the latter symbol only ever appears in legacy static-pie lifts,
#      dynamic-PIE lifts never define it — the sed is kept for old IR);
#   2. compile: llc -O0 -filetype=obj, then link with harness.c
#      (+ setjmp_stub.S when the module declares setjmp/longjmp — the
#      lifted code passes MODEL stack addresses as jmp_buf, which real
#      glibc would dereference; the stub overrides glibc's symbols);
#   3. run lifted + native, diff stdout byte-for-byte.
#
# The CORPUS binaries are PIE (ET_DYN) since 2026-08-26 (user directive:
# "only work on PIE with no fallbacks"), but the LIFTED-EXECUTABLE link
# here intentionally stays -no-pie. That is not a corpus fallback — it
# is a hard linker constraint of the harness artifact itself: the
# emitted modules carry baked absolute i64 constants (@got.plt[0] = the
# .dynamic vaddr) and extern_weak references (@__gmon_start__ et al)
# from read-only .rodata; a -pie link can only place them by creating
# DT_TEXTREL, which modern ld rejects for PIE. The native-vs-lifted
# equivalence being tested does not depend on the harness exec's own
# ELF type.
#
# Usage: run_semantic.sh [corpus_dir] [ir_dir] [out_dir]
#   corpus_dir  default /tmp/corpus        (native binaries)
#   ir_dir      default $REPO_ROOT/baselines/heritage_baseline_copy (post-COPY-design emitted IR)
#   out_dir     default /tmp/sem_out        (lifted artifacts + stdouts)
#
# Exit status: 0 iff every binary PASSes.
set -u

# Repo-relative defaults: the semantic regression baseline lives in the repo
# (baselines/heritage_baseline_copy = post-COPY-design emitted IR), so a bare
# invocation is reproducible without /tmp state.
# NOTE: that checked-in baseline holds IR emitted from the PRE-PIE (ET_EXEC)
# corpus; against today's PIE corpus a FRESH ir_dir from run_corpus.sh must
# be passed as arg 2 (the default remains for archaeology on old emissions).
HERE="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "$HERE/../.." && pwd)"

CORPUS="${1:-/tmp/corpus}"
IR="${2:-$REPO_ROOT/baselines/heritage_baseline_copy}"
OUT="${3:-/tmp/sem_out}"
# Optional 4th arg: extra binaries to verify AD-HOC beyond the permanent
# regression set (space-separated corpus names). Used e.g. to semantically
# verify adversarial shapes whose IR changed outside the fixed set (the
# va_arg u128/YMM family) without growing the default gate.
EXTRA_BINS="${4:-}"
mkdir -p "$OUT"

# Explicit list (run_corpus.sh does glob-driven discovery; for the
# permanent semantic regression binaries an explicit list is clearer).
# array_local added per ora-F C2: pins the @main dynamic-load path that
# upgraded from poison to bounds-checked with the RSP-removal (8263 entry).
# factorial + many_args added per GATE 1 F1 (ora-1): the demonstrated
# 0/8-boundary miscompile pair — `inc` (factorial) and `sum12` (many_args)
# must emit a GEP into the arg-area copy alloca for their stack-arg reads
# at +8 (the COPY design), NOT a GEP into the local alloca (native
# factorial exits 25, many_args prints "sum = 450").  struct_arr_dynidx +
# array_local flipped to PASS under P2 (H-R1: RMW stores +
# materialization); rmw_oob added per P2 as the bounded-store RMW
# regression (sum = 184).  PASS expectations.
BINS="setjmp_loop struct_arr_dynidx out_struct deep_recursion array_local factorial many_args rmw_oob"

# Ad-hoc extras join the same PASS/FAIL gate; empty by default so the
# permanent regression set is exactly the eight binaries above.
BINS="$BINS $EXTRA_BINS"

fail=0

for name in $BINS; do
    # out_struct is the lifted artifact of the corpus binary `struct`
    # (IR out_struct.ll, native /corpus/struct) — map the names.
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

    # setjmp/longjmp emulation stub, only when the module uses them.
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
