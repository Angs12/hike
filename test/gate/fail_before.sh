#!/usr/bin/env bash
# The mechanical fail-before check: prove a pin is not tautological by
# disabling its mechanism and asserting the pin goes red.
#
# One pin has a clean, test-only sabotage hook: CLEQ-01 (the CLP referee)
# corrupts its inlined reference under HIKE_FAIL_BEFORE.  Every other pin's
# disable recipe lives in test/pins.md and is re-demonstrated by review,
# because production src/ may hold no runtime-variable switch (ADR 0017,
# the instrumentation rule).
#
# Usage: fail_before.sh      (exit 0 iff the sabotage is caught)

set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
TREE="$(cd "$HERE/../.." && pwd)"

run_referee() {
  ( cd "$TREE" && eval "$(opam env 2>/dev/null)" && \
    dune exec test/unit/test_clp_equiv.exe >/dev/null 2>&1 )
}

# Baseline: the pin must be green.
if ! run_referee; then
  echo "fail-before: baseline CLEQ-01 is RED (the suite is broken)" >&2
  exit 1
fi

# Sabotage: the corrupted reference must be caught.
if HIKE_FAIL_BEFORE=1 run_referee; then
  echo "fail-before: CLEQ-01 did NOT go red under sabotage (tautological pin!)" >&2
  exit 1
fi

echo "fail-before: CLEQ-01 caught the sabotaged reference (red demonstrated)"
