#!/usr/bin/env bash
# Writes the build identity next to the installed dune plugin, so the
# gates verify the tested plugin was built from this tree (by content,
# not mtime). Records the plugin object hash, git identity, and tree
# path; a mismatch means rebuild and reinstall.

set -euo pipefail

PLUGIN_DST="${HIKE_PLUGIN_DST:-}"
if [ -z "$PLUGIN_DST" ]; then
  # The plugin's dynlinked object is <switch>/lib/hike/hike.cmxs; the
  # bap-common/plugins/hike/META stub only requires the hike package.
  # Locate the object via the active switch.
  for base in "${OPAM_SWITCH_PREFIX:-}" "$(opam switch show --safe 2>/dev/null | sed "s|^|$HOME/.opam/|")" "$HOME/.opam"; do
    [ -n "$base" ] || continue
    cand=$(find "$base/lib/hike" -maxdepth 1 -name 'hike.cmxs' 2>/dev/null | head -1)
    if [ -n "$cand" ]; then PLUGIN_DST="$cand"; break; fi
  done
fi
[ -n "$PLUGIN_DST" ] || { echo "record_provenance: no installed hike.cmxs found (did you run 'dune build @install && dune install'?)" >&2; exit 1; }

TREE="$(cd "$(git rev-parse --show-toplevel)" && pwd)"
GIT_DESC=$(git -C "$TREE" describe --always --dirty 2>/dev/null || echo unknown)
SRC_HASH=$({ find "$TREE/src" \( -name '*.ml' -o -name '*.mli' -o -name 'dune' -o -name '*.sh' \) -print \
              | sort | xargs sha256sum 2>/dev/null; \
            sha256sum "$TREE/dune-project" 2>/dev/null; } \
          | sha256sum | cut -c1-16)
# The plugin SET: the top-level object plus the sub-library objects bap
# loads with it (the analysis code lives in hike/cbat_vsa/*.cmxs).
PLUGIN_DIR=$(dirname "$PLUGIN_DST")
BUNDLE_HASH=$( (cd "$PLUGIN_DIR" && find . -name '*.cmxs' | sort | xargs sha256sum) | sha256sum | cut -c1-16)

cat > "${PLUGIN_DST}.provenance" <<EOF
# hike plugin provenance — written by src/record_provenance.sh at install time.
# The gates verify these fields BEFORE running; a mismatch means the
# installed plugin is NOT this tree's build — rebuild and reinstall.
tree: $TREE
git: $GIT_DESC
src_sha16: $SRC_HASH
bundle_sha16: $BUNDLE_HASH
EOF

echo "record_provenance: wrote ${PLUGIN_DST}.provenance (git=$GIT_DESC src=$SRC_HASH bundle=$BUNDLE_HASH)"
