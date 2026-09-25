#!/usr/bin/env bash
# Native-vs-lifted equivalence for EVERY emitted corpus binary.
# Usage: run_semantic.sh [corpus_dir] [ir_dir] [out_dir]
# Renames @main, llc -O0, links harness.c (+ setjmp_stub.S for setjmp
# users), runs both with a 15 s timeout, byte-diffs stdout.
#
# STRICT: rc=1 on ANY failure — a failing binary is a loud red, never an
# allowlisted known.  The render/link/run/compare recipe lives in
# test/gate/lib.sh, shared with the other gates.

set -u
CORPUS="${1:-/tmp/corpus}"
IR="${2:-/tmp/hike-emit}"
OUT="${3:-/tmp/hike-sem}"
HERE="$(cd "$(dirname "$0")" && pwd)"
. "$HERE/../lib.sh"
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

	# Rebuild only when the IR changed: the recorded sha gates the
	# rename/llc/link pipeline.  FRESH=1 forces the rebuild.
	bin="$OUT/${base}_lifted"
	sha_now="$(sha256sum "$ll" | cut -d' ' -f1)"
	sha_was="$(cat "$OUT/.sha_${base}" 2>/dev/null || true)"
	if [ "${FRESH:-0}" != "1" ] && [ -x "$bin" ] \
	   && [ -n "$sha_was" ] && [ "$sha_now" = "$sha_was" ]; then
		echo "SKIP-RUN $base (IR unchanged)"
		if hike_run_cmp "$bin" "$native" "$OUT" "$base"; then
			pass=$((pass + 1))
		else
			fail=$((fail + 1))
			FAILED+=("$base")
		fi
		continue
	fi
	if ! hike_rename "$ll" "$OUT/${base}_lifted.ll"; then
		echo "FAIL $base (rename)"
		fail=$((fail + 1))
		FAILED+=("$base")
		continue
	fi
	if ! hike_llc "$OUT/${base}_lifted.ll" "$OUT/${base}_lifted.o" 2>/dev/null; then
		echo "FAIL $base (llc)"
		fail=$((fail + 1))
		FAILED+=("$base")
		continue
	fi
	if ! hike_link "$OUT/${base}_lifted.o" "$ll" "$bin" "$HERE" 2>/dev/null; then
		echo "FAIL $base (link)"
		fail=$((fail + 1))
		FAILED+=("$base")
		continue
	fi
	printf '%s\n' "$sha_now" >"$OUT/.sha_${base}"
	if hike_run_cmp "$OUT/${base}_lifted" "$native" "$OUT" "$base"; then
		echo "PASS $base"
		pass=$((pass + 1))
	else
		fail=$((fail + 1))
		FAILED+=("$base")
	fi
done

echo "----------------------------------------"
echo "semantic-all: $pass PASS, $fail FAIL, $skip SKIP (of $(ls "$IR"/out_*.ll | wc -l) emitted)"
if [ "$fail" -gt 0 ]; then
	printf 'failed: %s\n' "${FAILED[@]}"
fi
exit $((fail > 0))
