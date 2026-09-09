#!/usr/bin/env bash
# Native-vs-lifted equivalence for EVERY emitted corpus binary.
# Usage: run_semantic.sh [corpus_dir] [ir_dir] [out_dir] [expected_failures]
# Renames @main, llc -O0, links harness.c (+ setjmp_stub.S for setjmp
# users), runs both with a 15 s timeout, byte-diffs stdout.
# The lifted link stays -no-pie: a linker constraint of the harness
# artifact (baked absolute constants + extern_weak refs reject DT_TEXTREL).
#
# With a 4th argument (a golden-list file: one binary name per line, `#`
# comments allowed), the gate is PINNED-KNOWNS mode: green (rc=0) iff the
# failing set equals the golden list EXACTLY. Any difference is red
# (rc=1) — newly failing = REGRESSION, golden-listed now passing =
# IMPROVEMENT — forcing a deliberate golden-list + AGENTS.md update (the
# re-baseline rule). Without it: strict mode, rc=1 on ANY failure.

set -u
CORPUS="${1:-/tmp/corpus}"
IR="${2:-/tmp/heritage_p6}"
OUT="${3:-/tmp/sem_all}"
EXPECTED="${4:-}"
HERE="$(cd "$(dirname "$0")" && pwd)"
mkdir -p "$OUT"

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
		"$ll" >"$OUT/${base}_lifted.ll" || {
		echo "FAIL $base (rename)"
		fail=$((fail + 1))
		FAILED+=("$base")
		continue
	}
	llc -O0 -filetype=obj "$OUT/${base}_lifted.ll" -o "$OUT/${base}_lifted.o" 2>/dev/null ||
		{
			echo "FAIL $base (llc)"
			fail=$((fail + 1))
			FAILED+=("$base")
			continue
		}
	STUB=""
	if grep -q '@_setjmp\|@longjmp' "$ll"; then STUB="$HERE/setjmp_stub.S"; fi
	gcc -O0 -no-pie -o "$OUT/${base}_lifted" \
		"$OUT/${base}_lifted.o" "$HERE/harness.c" $STUB 2>/dev/null ||
		{
			echo "FAIL $base (link)"
			fail=$((fail + 1))
			FAILED+=("$base")
			continue
		}

	# exec -a keeps argv[0] identical (glibc prints it in usage messages).
	timeout 15 bash -c 'exec -a "$1" "$2"' _ prog "$OUT/${base}_lifted" >"$OUT/${base}_lifted.out" 2>&1
	lrc=$?
	timeout 15 bash -c 'exec -a "$1" "$2"' _ prog "$native" >"$OUT/${base}_native.out" 2>&1
	nrc=$?
	if [ $lrc -eq 124 ] || [ $nrc -eq 124 ]; then
		echo "FAIL $base (timeout: lifted rc=$lrc native rc=$nrc)"
		fail=$((fail + 1))
		FAILED+=("$base (timeout)")
		continue
	fi
	if [ "$lrc" -ne "$nrc" ] || ! cmp -s "$OUT/${base}_lifted.out" "$OUT/${base}_native.out"; then
		echo "FAIL $base (native rc=$nrc vs lifted rc=$lrc)"
		diff "$OUT/${base}_native.out" "$OUT/${base}_lifted.out" | head -3 | sed 's/^/    /'
		fail=$((fail + 1))
		FAILED+=("$base")
		continue
	fi
	echo "PASS $base"
	pass=$((pass + 1))
done

echo "----------------------------------------"
echo "semantic-all: $pass PASS, $fail FAIL, $skip SKIP (of $(ls "$IR"/out_*.ll | wc -l) emitted)"
if [ "$fail" -gt 0 ]; then
	printf 'failed: %s\n' "${FAILED[@]}"
fi
if [ -n "$EXPECTED" ]; then
	# Pinned-knowns mode: green iff the failing set equals the golden list
	# exactly; any difference is red (the re-baseline rule).
	actual="$(printf '%s\n' ${FAILED[@]+"${FAILED[@]}"} | sed 's/ .*//; s/^out_//' | grep -v '^$' | sort)"
	expected="$(sed 's/#.*//' "$EXPECTED" | tr -s '[:space:]' '\n' | grep -v '^$' | sort)"
	growth="$(comm -13 <(printf '%s\n' "$expected") <(printf '%s\n' "$actual"))"
	shrink="$(comm -23 <(printf '%s\n' "$expected") <(printf '%s\n' "$actual"))"
	if [ -z "$growth" ] && [ -z "$shrink" ]; then
		echo "semantic-pin: OK — failing set == golden list ($(printf '%s\n' "$expected" | grep -c '^') knowns)"
		exit 0
	fi
	if [ -n "$growth" ]; then
		echo "semantic-pin: REGRESSION — newly failing (not in golden list):"
		printf '%s\n' "$growth" | sed 's/^/    /'
	fi
	if [ -n "$shrink" ]; then
		echo "semantic-pin: IMPROVEMENT — golden-listed binaries now passing:"
		printf '%s\n' "$shrink" | sed 's/^/    /'
	fi
	echo "semantic-pin: update the golden list + AGENTS.md deliberately (the re-baseline rule)"
	exit 1
fi
exit $((fail > 0))
