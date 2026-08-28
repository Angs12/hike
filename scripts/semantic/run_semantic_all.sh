#!/usr/bin/env bash
# run_semantic_all.sh — semantic native-vs-lifted equivalence for EVERY
# emitted corpus binary (the 8-bin run_semantic.sh list + the other 20).
#
# The corpus is PIE (ET_DYN, compile_corpus.sh since 2026-08-26); the
# lifted-executable link stays -no-pie — see run_semantic.sh's header for
# why that is a linker constraint of the harness artifact (baked @got.plt
# constants + extern_weak .rodata refs → DT_TEXTREL), not a corpus fallback.
#
# Usage: run_semantic_all.sh [corpus_dir] [ir_dir] [out_dir]
#   corpus_dir  default /tmp/corpus          (native binaries)
#   ir_dir      default /tmp/heritage_p6     (the emitted out_*.ll)
#   out_dir     default /tmp/sem_all
#
# Per out_<name>.ll: rename @main/@_dl_relocate_static_pie, llc -O0,
# link with harness.c (+ setjmp_stub.S when the module uses setjmp/
# longjmp), run lifted + native, byte-diff stdout, record rc.  Each
# run is wrapped in a 15 s timeout (a lifted binary that infinite-loops
# must not stall the batch).

set -u
CORPUS="${1:-/tmp/corpus}"
IR="${2:-/tmp/heritage_p6}"
OUT="${3:-/tmp/sem_all}"
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

	# exec -a forces identical argv[0]: glibc usage messages print the
	# program's own path, so raw invocation compares argv[0]s, not behavior.
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
exit $((fail > 0))
