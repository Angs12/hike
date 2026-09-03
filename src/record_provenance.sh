#!/usr/bin/env bash
# Writes the build identity next to the installed plugin, so battery.sh
# verifies the tested plugin was built from this tree (by content, not
# mtime). Records bundle content hash, git identity, and tree path;
# battery.sh fails on mismatch.

set -euo pipefail

PLUGIN_DST="${HIKE_PLUGIN_DST:-}"
if [ -z "$PLUGIN_DST" ]; then
  # locate the installed bundle via the active switch's plugin dir
  for base in "${OPAM_SWITCH_PREFIX:-}" "$(opam switch show --safe 2>/dev/null | sed "s|^|$HOME/.opam/|")" "$HOME/.opam"; do
    [ -n "$base" ] || continue
    cand=$(find "$base/lib/bap-common/plugins" -maxdepth 1 -name 'hike.plugin' 2>/dev/null | head -1)
    if [ -n "$cand" ]; then PLUGIN_DST="$cand"; break; fi
  done
fi
[ -n "$PLUGIN_DST" ] || { echo "record_provenance: no installed hike.plugin found" >&2; exit 1; }

TREE="$(cd "$(git rev-parse --show-toplevel)" && pwd)"
GIT_DESC=$(git -C "$TREE" describe --always --dirty 2>/dev/null || echo unknown)
SRC_HASH=$(find "$TREE/src" -name '*.ml' -o -name '*.mli' -o -name 'dune' | sort | xargs sha256sum 2>/dev/null | sha256sum | cut -c1-16)
BUNDLE_HASH=$(sha256sum "$PLUGIN_DST" | cut -c1-16)

cat > "${PLUGIN_DST}.provenance" <<EOF
# hike.plugin provenance — written by src/record_provenance.sh at install time.
# battery.sh verifies these fields BEFORE running the gates; a mismatch
# means the installed plugin is NOT this tree's build — rebuild (make hike).
tree: $TREE
git: $GIT_DESC
src_sha16: $SRC_HASH
bundle_sha16: $BUNDLE_HASH
EOF

echo "record_provenance: wrote ${PLUGIN_DST}.provenance (git=$GIT_DESC src=$SRC_HASH bundle=$BUNDLE_HASH)"
