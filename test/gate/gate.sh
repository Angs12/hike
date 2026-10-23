#!/usr/bin/env bash
# The gate orchestrator: one entry point for the strict integration chain.
#
#   gate.sh <stage>
#     stages: corpus lift allocas semantics unit referee sysv
#             performance all
#
# Every lift runs the installed hike executable (Hike.Drive, ADR 0032).
#
# `all` runs the documented chain in order and aborts on the first failure.
# Every stage is strict (non-zero exit on any failure).
#
# Paths are overridable: HIKE_CORPUS, HIKE_EMIT, HIKE_SEMOUT.

set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
TREE="$(cd "$HERE/../.." && pwd)"
. "$HERE/lib.sh"

CORPUS="${HIKE_CORPUS:-/tmp/corpus-o2}"
EMIT="${HIKE_EMIT:-/tmp/hike-emit}"
SEMOUT="${HIKE_SEMOUT:-/tmp/hike-sem}"

usage() {
  echo "usage: gate.sh <corpus|lift|allocas|semantics|unit|referee|sysv|performance|all> [performance options and binaries]" >&2
  exit 2
}

need_renderer() {
  command -v "$LLC" >/dev/null 2>&1 || {
    echo "FATAL: $LLC not found on PATH (set HIKE_LLC to pin one)" >&2
    exit 2
  }
  echo "  tools: $("$LLC" --version 2>/dev/null | head -1)"
}

stage() {
  local selected="$1"
  shift
  case "$selected" in
    corpus)     "$HERE/compile_corpus.sh" "$CORPUS" ;;
    lift)       "$HERE/run_corpus.sh" "$CORPUS" "$EMIT" ;;
    allocas)    "$HERE/check_allocas.sh" "$EMIT" &&
                python3 "$HERE/check_initializers.py" "$EMIT" "$CORPUS" ;;
    semantics)  need_renderer; "$HERE/semantic/run_semantic.sh" "$CORPUS" "$EMIT" "$SEMOUT" ;;
    unit)       ( cd "$TREE" && dune runtest --force ) ;;
    referee)    ( cd "$TREE" && dune exec test/unit/test_clp_equiv.exe ) ;;
    sysv)       ( cd "$TREE" && dune build --root . test/probe/sysv/sysv_classify.exe &&
                  for seed in 1 2 3 4 5; do
                    python3 "$HERE/sysv_oracle.py" --cases 1000 --seed "$seed" || exit 1
                  done ) ;;
    performance)
      local perfout="${HIKE_PERFOUT:-${TMPDIR:-/tmp}/hike-performance-$(date -u +%Y%m%dT%H%M%S)}"
      python3 "$HERE/performance.py" --output "$perfout" "$@"
      ;;
    *)          usage ;;
  esac
}

STAGE="${1:-}"
[ -n "$STAGE" ] || usage

if [ "$STAGE" = all ]; then
  for s in corpus lift allocas semantics unit referee sysv; do
    echo "=== gate: $s"
    stage "$s" || {
      echo "gate FAILED at stage: $s" >&2
      exit 1
    }
  done
  echo "=== gate: ALL GREEN"
  exit 0
fi

stage "$@"
