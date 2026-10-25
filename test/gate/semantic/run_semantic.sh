#!/usr/bin/env bash
# THE semantic gate: the lifted module links and runs like a program —
# llc -relocation-model=pic, gcc -pie, no harness, no rename, no stub —
# and its stdout and exit status are byte-diffed against the native
# binary at the consumer optimizer's HIKE_OPT_LEVEL (default 2; 0 = no
# optimization passes).  Strict: no allowlist; failures auto-bisect
# every pass in BISECT_PASSES and list each breaking pass (CRASH = opt
# crashed).  Keeps *_opt.ll as the repro artifact.  Pins opt-19 (fails
# loudly when missing); exit 0 iff all pass.
# Usage: run_semantic.sh [corpus_dir] [ir_dir] [out_dir]

set -u
CORPUS="${1:-/tmp/corpus-o2}"
IR="${2:-/tmp/emit}"
OUT="${3:-/tmp/sem_opt}"
HERE="$(cd "$(dirname "$0")" && pwd)"
. "$HERE/../lib.sh"
mkdir -p "$OUT"

if ! compgen -G "$IR/out_*.ll" >/dev/null; then
	echo "FATAL: no emitted IR in $IR (run the lift gate first)" >&2
	exit 2
fi

# Pinned optimizer; a default switch must not silently change the gate.
OPT=opt-19
OPT_LEVEL="${HIKE_OPT_LEVEL:-2}"
command -v "$OPT" >/dev/null 2>&1 || {
	echo "FATAL: $OPT not found (the gate pins the opt version; NO FALLBACKS)"
	exit 2
}
command -v "$LLC" >/dev/null 2>&1 || {
	echo "FATAL: $LLC not found (set HIKE_LLC to pin one)"
	exit 2
}

# The cache key covers the IR and every tool that can change its rendering.
TOOL_SHA="$({ sha256sum "$(command -v "$OPT")" "$(command -v "$LLC")" \
                "$(command -v gcc)" 2>/dev/null
              printf '%s\n' "$OPT_LEVEL"; } | sha256sum | cut -d' ' -f1)"

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
	list) native="$CORPUS/list" ;; # list.c + functional driver
	*) native="$CORPUS/$name" ;;
	esac
	[ -x "$native" ] || {
		echo "SKIP $base (no native $native)"
		skip=$((skip + 1))
		continue
	}

	# Rebuild only when the IR changed (the recorded sha gates the
	# rename/opt/llc/link pipeline); FRESH=1 forces the rebuild.
	bin="$OUT/${base}_opt.bin"
	sha_now="$(sha256sum "$ll" | cut -d' ' -f1)"
	sha_was="$(cat "$OUT/.sha_${base}" 2>/dev/null || true)"
	if [ "${FRESH:-0}" != "1" ] && [ -x "$bin" ] \
	   && [ -n "$sha_was" ] && [ "$sha_now $TOOL_SHA" = "$sha_was" ]; then
		timeout "${HIKE_RUN_TIMEOUT:-15}" bash -c 'exec -a "$1" "$2"' _ prog "$bin" >"$OUT/${base}_opt.out" 2>&1
		lrc=$?
		timeout "${HIKE_RUN_TIMEOUT:-15}" bash -c 'exec -a "$1" "$2"' _ prog "$native" >"$OUT/${base}_native.out" 2>&1
		nrc=$?
		if [ "$lrc" -eq 124 ] || [ "$nrc" -eq 124 ]; then
			echo "FAIL $base (timeout, cached: lifted rc=$lrc native rc=$nrc)"
			fail=$((fail + 1))
			FAILED+=("$base (timeout)")
			continue
		fi
		if [ "$lrc" -eq "$nrc" ] && cmp -s "$OUT/${base}_opt.out" "$OUT/${base}_native.out"; then
			echo "PASS $base (opt -O$OPT_LEVEL, IR unchanged)"
			pass=$((pass + 1))
			continue
		fi
		# A cached binary that no longer passes falls through to the
		# full rebuild below (FRESH-like behavior for the stale one).
	fi
	# The gate step.
	"$OPT" -O$OPT_LEVEL -S "$ll" -o "$OUT/${base}_opt.ll" 2>"$OUT/${base}_opt.err" || {
		echo "FAIL $base (opt -O$OPT_LEVEL): $(head -1 "$OUT/${base}_opt.err")"
		fail=$((fail + 1))
		FAILED+=("$base")
		continue
	}

	hike_llc "$OUT/${base}_opt.ll" "$OUT/${base}_opt.o" -relocation-model=pic \
		2>>"$OUT/.llc.log" ||
		{
			echo "FAIL $base (llc after opt; see $OUT/.llc.log)"
			fail=$((fail + 1))
			FAILED+=("$base")
			continue
		}
	if ! gcc -O0 -pie -o "$OUT/${base}_opt.bin" "$OUT/${base}_opt.o" -latomic -lm 2>>"$OUT/.gcc.log"; then
		echo "FAIL $base (link after opt; see $OUT/.gcc.log)"
		fail=$((fail + 1))
		FAILED+=("$base")
		continue
	fi
	printf '%s\n' "$sha_now $TOOL_SHA" >"$OUT/.sha_${base}"

	# exec -a keeps argv[0] identical (glibc prints it in usage messages).
	timeout "${HIKE_RUN_TIMEOUT:-15}" bash -c 'exec -a "$1" "$2"' _ prog "$OUT/${base}_opt.bin" >"$OUT/${base}_opt.out" 2>&1
	lrc=$?
	timeout "${HIKE_RUN_TIMEOUT:-15}" bash -c 'exec -a "$1" "$2"' _ prog "$native" >"$OUT/${base}_native.out" 2>&1
	nrc=$?
	if [ $lrc -eq 124 ] || [ $nrc -eq 124 ]; then
		echo "FAIL $base (timeout after opt: lifted rc=$lrc native rc=$nrc)"
		fail=$((fail + 1))
		FAILED+=("$base (timeout)")
		continue
	fi
	if [ "$lrc" -ne "$nrc" ] || ! cmp -s "$OUT/${base}_opt.out" "$OUT/${base}_native.out"; then
		echo "FAIL $base (opt -O$OPT_LEVEL; native rc=$nrc vs lifted rc=$lrc)"
		diff "$OUT/${base}_native.out" "$OUT/${base}_opt.out" | head -3 | sed 's/^/    /'
		# Auto-bisect: list every pass that alone breaks this binary.
		bisect_line="    broken by:"
		any_bisect=0
		for p in $BISECT_PASSES; do
			"$OPT" "-passes=$p" -S "$ll" -o "$OUT/${base}_bisect_$p.ll" 2>/dev/null ||
				{
					bisect_line="$bisect_line $p(CRASH)"
					any_bisect=1
					continue
				}
			hike_llc "$OUT/${base}_bisect_$p.ll" "$OUT/${base}_bisect_$p.o" -O0 -relocation-model=pic 2>/dev/null ||
				{
					bisect_line="$bisect_line $p(llc)"
					any_bisect=1
					continue
				}
			gcc -O0 -pie -o "$OUT/${base}_bisect_$p.bin" \
				"$OUT/${base}_bisect_$p.o" -latomic -lm 2>/dev/null ||
				{
					bisect_line="$bisect_line $p(link)"
					any_bisect=1
					continue
				}
			timeout "${HIKE_RUN_TIMEOUT:-15}" bash -c 'exec -a "$1" "$2"' _ prog "$OUT/${base}_bisect_$p.bin" >"$OUT/${base}_bisect_$p.out" 2>&1
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
	echo "PASS $base (opt -O$OPT_LEVEL)"
	pass=$((pass + 1))
done

echo "----------------------------------------"
echo "semantic-opt: $pass PASS, $fail FAIL, $skip SKIP (of $(ls "$IR"/out_*.ll | wc -l) emitted)"
if [ "$fail" -gt 0 ]; then
	printf 'failed: %s\n' "${FAILED[@]}"
fi
if [ "$skip" -gt 0 ]; then
	echo "FATAL: $skip emitted binaries had no native counterpart — corpus/emission mismatch" >&2
fi
exit $((fail > 0 || skip > 0))
