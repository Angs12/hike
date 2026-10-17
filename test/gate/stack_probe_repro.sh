#!/usr/bin/env bash
# T35 reproduction: a two-page stack-probe loop must lift with its return
# classified. Uses the uninstalled drive executable (`dune exec`).
#
# Usage: stack_probe_repro.sh [work_dir] (default: a fresh mktemp dir)
# Exit: 0 lifts, 1 the T35 unresolved-return diagnostic, 2 any other failure.

set -u

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
WORK="${1:-$(mktemp -d)}"
mkdir -p "$WORK"
SRC="$ROOT/src/synth/stack_probe_loop.S"

gcc -pie -o "$WORK/stack_probe_loop" "$SRC" || exit 2
if dune exec --root "$ROOT" -j 4 src/drive/main.exe -- \
     "$WORK/stack_probe_loop" -o "$WORK/stack_probe_loop.ll" \
     >"$WORK/stack_probe_loop.log" 2>&1; then
  echo 'PASS: stack-probe loop lifts'
  exit 0
fi
if grep -Eq 'indirect tail call.*sub @main.*has no enumerated destinations' \
     "$WORK/stack_probe_loop.log"; then
  echo 'FAIL: stack-probe loop return remains unresolved'
  tail -1 "$WORK/stack_probe_loop.log"
  exit 1
fi
cat "$WORK/stack_probe_loop.log"
exit 2
