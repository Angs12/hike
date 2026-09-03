#!/usr/bin/env bash
# Optimization-safety gate: native-vs-lifted equivalence with opt -O2
# between rename and llc. Strict: no allowlist; failures auto-bisect
# every pass in BISECT_PASSES and list each breaking pass (CRASH = opt
# crashed). Keeps *_renamed.ll/*_opt.ll as repro artifacts.
# Pins opt-21 (fails loudly when missing); exit 0 iff all pass.
# Usage: run_semantic_opt.sh [corpus_dir] [ir_dir] [out_dir]

set -u
CORPUS="${1:-/tmp/corpus}"
IR="${2:-/tmp/heritage_p6}"
OUT="${3:-/tmp/sem_opt}"
HERE="$(cd "$(dirname "$0")" && pwd)"
mkdir -p "$OUT"

# Pinned optimizer; a default switch must not silently change the gate.
OPT=opt-21
command -v "$OPT" >/dev/null 2>&1 || {
	echo "FATAL: $OPT not found (the gate pins the opt version; NO FALLBACKS)"
	exit 2
}

# Single-pass bisect list; an opt crash counts as breaking too.
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

	# The gate step.
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

	# exec -a keeps argv[0] identical (glibc prints it in usage messages).
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
		# Auto-bisect: list every pass that alone breaks this binary.
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
