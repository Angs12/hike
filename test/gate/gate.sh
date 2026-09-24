#!/usr/bin/env bash
# The gate orchestrator: one entry point for the strict integration chain.
#
#   gate.sh <stage>
#     stages: fail-before provenance corpus lift allocas semantics opt-safety
#             unit all
#
# `all` runs the documented chain in order and aborts on the first failure.
# Every stage is strict (non-zero exit on any failure) and provenance is
# verified before any stage that consumes an emission.
#
# Paths are overridable: HIKE_CORPUS, HIKE_EMIT, HIKE_SEMOUT, HIKE_SEMOPT.

set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
TREE="$(cd "$HERE/../.." && pwd)"
. "$HERE/lib.sh"

CORPUS="${HIKE_CORPUS:-/tmp/corpus}"
EMIT="${HIKE_EMIT:-/tmp/hike-emit}"
SEMOUT="${HIKE_SEMOUT:-/tmp/hike-sem}"
SEMOPT="${HIKE_SEMOPT:-/tmp/hike-semopt}"

usage() {
  echo "usage: gate.sh <provenance|corpus|lift|allocas|semantics|opt-safety|unit|fail-before|all>" >&2
  exit 2
}

need_provenance() { provenance_ok "$TREE" || exit $?; }

stage() {
  case "$1" in
    provenance) need_provenance ;;
    corpus)     "$HERE/compile_corpus.sh" "$CORPUS" ;;
    lift)       need_provenance; "$HERE/run_corpus.sh" "$CORPUS" "$EMIT" ;;
    allocas)    "$HERE/check_allocas.sh" "$EMIT" ;;
    semantics)  need_provenance; "$HERE/semantic/run_semantic.sh" "$CORPUS" "$EMIT" "$SEMOUT" ;;
    opt-safety) need_provenance; "$HERE/semantic/run_semantic_opt.sh" "$CORPUS" "$EMIT" "$SEMOPT" ;;
    unit)       ( cd "$TREE" && dune runtest --force ) ;;
    fail-before) "$HERE/fail_before.sh" ;;
    *)          usage ;;
  esac
}

STAGE="${1:-}"
[ -n "$STAGE" ] || usage

if [ "$STAGE" = all ]; then
  for s in provenance corpus lift allocas semantics opt-safety unit fail-before; do
    echo "=== gate: $s"
    stage "$s" || {
      echo "gate FAILED at stage: $s" >&2
      exit 1
    }
  done
  echo "=== gate: ALL GREEN"
  exit 0
fi

stage "$STAGE"
