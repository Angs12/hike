#!/usr/bin/env bash
# Verify the installed hike plugin was built from this tree.
#
#   provenance.sh [tree]     (default: the repo root two levels up)
#
# Exit 0 on a match; 2 when no provenance record exists; 3 on a mismatch.
# This is the check the deleted battery owned and no surviving script
# implemented.
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
. "$HERE/lib.sh"
TREE="${1:-$(cd "$HERE/../.." && pwd)}"
provenance_ok "$TREE" || exit $?
echo "provenance ok: $TREE"
