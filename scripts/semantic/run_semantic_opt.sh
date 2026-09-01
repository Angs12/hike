#!/usr/bin/env bash
# run_semantic_opt.sh — the OPTIMIZATION-SAFETY gate: the same
# native-vs-lifted equivalence as run_semantic_all.sh, but the emitted
# IR is pushed through `opt -O2` between rename and llc.  What a real
# consumer (llc -O2, clang -O2, an inliner) does to the module must
# not change the lifted binary's behavior — this gate proves it.
#
# Born 2026-09-01 at 23/32; the poison-phi definedness fix (same day,
# below) flipped mixed_fp_int — the proven poison-class member — to
# 24/32.  The remaining failures are the gate's work-list, not an
# excuse to widen: 5 are opt-INDUCED and all instcombine-family (the
# model-SP-lane/push class: fizzbuzz, fptr_table, setjmp_longjmp,
# struct_arr_dynidx, union_overlap — see the 2026-09-01 optimizability
# review), 3 are the pre-existing -O0 knowns (nested_struct, variadic,
# va_arg_vacopy — tickets T02/T03/T05 in .scratch/one-frame-anchor-
# removal/, they fail run_semantic_all.sh identically and are listed
# here for completeness, NOT exempted).  There is no allowlist and no
# exemption logic: every red binary is red, every failure line carries
# its cause.
#
# opt version: pinned to opt-21 (system LLVM 21).  The emitter's OCaml
# binding is 19.1.7, but the gate tests what MODERN consumers do; the
# 21 pipeline is a superset in practice (its instcombine is stricter —
# it is the one that surfaces the fixpoint error class).  Both opt-19
# and opt-21 exist on this machine; if opt-21 is missing, fail loudly
# rather than silently falling back (NO FALLBACKS).
#
# Usage: run_semantic_opt.sh [corpus_dir] [ir_dir] [out_dir]
#   corpus_dir  default /tmp/corpus        (native binaries)
#   ir_dir      default /tmp/heritage_p6   (the emitted out_*.ll)
#   out_dir     default /tmp/sem_opt       (kept artifacts: *_opt.ll,
#                                           the post-opt IR, is the
#                                           reproducible failure record)
#
# Per out_<name>.ll:
#   1. rename @main -> @hike_main (harness collision), as always;
#   2. opt -O2 -S          -> kept as <name>_opt.ll;
#   3. llc -O0 + harness link, 15 s timeout, byte-diff vs native;
#   4. on failure: AUTO-BISECT — each pass in BISECT_PASSES runs alone
#      over the renamed IR, and EVERY failing pass is listed.  The
#      multiplicity is the diagnosis: instcombine alone = the poison/
#      canonicalization class; sroa+instcombine+inline together = the
#      model-SP-lane class.  One extra opt run per pass, seconds each.
# Exit: 0 iff every binary PASSes.

set -u
CORPUS="${1:-/tmp/corpus}"
IR="${2:-/tmp/heritage_p6}"
OUT="${3:-/tmp/sem_opt}"
HERE="$(cd "$(dirname "$0")" && pwd)"
mkdir -p "$OUT"

# The pinned optimizer.  Plain `opt` on this machine is 21; pin the
# explicit name so a future default switch cannot silently change the
# gate's meaning.
OPT=opt-21
command -v "$OPT" >/dev/null 2>&1 || {
	echo "FATAL: $OPT not found (the gate pins the opt version; NO FALLBACKS)"
	exit 2
}

# Single-pass bisect list.  A pass that CRASHES opt (the fixpoint class)
# is a failure too — crash and miscompile are both "this pass broke it".
BISECT_PASSES="mem2reg sroa instcombine simplifycfg dse inline function-attrs argpromotion globalopt early-cse"

pass=0
fail=0
skip=0
declare -a FAILED=()

for ll in "$IR"/out_*.ll; do
	[ -f "$ll" ] || continue
	base="$(basename "$ll" .ll)" # out_<name>
	name="${base#out_}"
	case "$name" in
	list) native="$CORPUS/list" ;; # list.c + stub main
	*) native="$CORPUS/$name" ;;
	esac
	[ -x "$native" ] || {
		echo "SKIP $base (no native $native)"
		skip=$((skip + 1))
		continue
	}

	sed -e 's/@main/@hike_main/g' \
		-e 's/@_dl_relocate_static_pie/@_dl_relocate_static_pie_lifted/g' \
		"$ll" >"$OUT/${base}_renamed.ll" || {
		echo "FAIL $base (rename)"
		fail=$((fail + 1))
		FAILED+=("$base")
		continue
	}

	# The gate step itself.
	"$OPT" -O2 -S "$OUT/${base}_renamed.ll" -o "$OUT/${base}_opt.ll" 2>"$OUT/${base}_opt.err" || {
		echo "FAIL $base (opt -O2): $(head -1 "$OUT/${base}_opt.err")"
		fail=$((fail + 1))
		FAILED+=("$base")
		continue
	}

	llc -O0 -filetype=obj "$OUT/${base}_opt.ll" -o "$OUT/${base}_opt.o" 2>/dev/null ||
		{
			echo "FAIL $base (llc after opt)"
			fail=$((fail + 1))
			FAILED+=("$base")
			continue
		}
	STUB=""
	if grep -q '@_setjmp\|@longjmp' "$ll"; then STUB="$HERE/setjmp_stub.S"; fi
	gcc -O0 -no-pie -o "$OUT/${base}_opt.bin" \
		"$OUT/${base}_opt.o" "$HERE/harness.c" $STUB 2>/dev/null ||
		{
			echo "FAIL $base (link after opt)"
			fail=$((fail + 1))
			FAILED+=("$base")
			continue
		}

	# exec -a forces identical argv[0]: glibc usage messages print the
	# program's own path, so raw invocation compares argv[0]s, not behavior.
	timeout 15 bash -c 'exec -a "$1" "$2"' _ prog "$OUT/${base}_opt.bin" >"$OUT/${base}_opt.out" 2>&1
	lrc=$?
	timeout 15 bash -c 'exec -a "$1" "$2"' _ prog "$native" >"$OUT/${base}_native.out" 2>&1
	nrc=$?
	if [ $lrc -eq 124 ] || [ $nrc -eq 124 ]; then
		echo "FAIL $base (timeout after opt: lifted rc=$lrc native rc=$nrc)"
		fail=$((fail + 1))
		FAILED+=("$base (timeout)")
		continue
	fi
	if [ "$lrc" -ne "$nrc" ] || ! cmp -s "$OUT/${base}_opt.out" "$OUT/${base}_native.out"; then
		echo "FAIL $base (opt -O2; native rc=$nrc vs lifted rc=$lrc)"
		diff "$OUT/${base}_native.out" "$OUT/${base}_opt.out" | head -3 | sed 's/^/    /'
		# AUTO-BISECT: every pass that alone breaks this binary.
		bisect_line="    broken by:"
		any_bisect=0
		for p in $BISECT_PASSES; do
			"$OPT" "-passes=$p" -S "$OUT/${base}_renamed.ll" -o "$OUT/${base}_bisect_$p.ll" 2>/dev/null ||
				{
					bisect_line="$bisect_line $p(CRASH)"
					any_bisect=1
					continue
				}
			llc -O0 -filetype=obj "$OUT/${base}_bisect_$p.ll" -o "$OUT/${base}_bisect_$p.o" 2>/dev/null ||
				{
					bisect_line="$bisect_line $p(llc)"
					any_bisect=1
					continue
				}
			gcc -O0 -no-pie -o "$OUT/${base}_bisect_$p.bin" \
				"$OUT/${base}_bisect_$p.o" "$HERE/harness.c" $STUB 2>/dev/null ||
				{
					bisect_line="$bisect_line $p(link)"
					any_bisect=1
					continue
				}
			timeout 15 bash -c 'exec -a "$1" "$2"' _ prog "$OUT/${base}_bisect_$p.bin" >"$OUT/${base}_bisect_$p.out" 2>&1
			prc=$?
			if [ "$prc" -ne "$nrc" ] || ! cmp -s "$OUT/${base}_bisect_$p.out" "$OUT/${base}_native.out"; then
				bisect_line="$bisect_line $p"
				any_bisect=1
			fi
		done
		[ $any_bisect -eq 1 ] && echo "$bisect_line"
		fail=$((fail + 1))
		FAILED+=("$base")
		continue
	fi
	echo "PASS $base (opt -O2)"
	pass=$((pass + 1))
done

echo "----------------------------------------"
echo "semantic-opt: $pass PASS, $fail FAIL, $skip SKIP (of $(ls "$IR"/out_*.ll | wc -l) emitted)"
if [ "$fail" -gt 0 ]; then
	printf 'failed: %s\n' "${FAILED[@]}"
fi
exit $((fail > 0))
