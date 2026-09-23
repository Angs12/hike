#!/usr/bin/env bash
# Attribution census driver.
#
# Builds the vsa-debug plugin into its own build dir and points findlib at
# it for the bap process ONLY (the installed plugin slot is never touched;
# a background lane owns it).  Runs the production pass chain per binary;
# the VSA_DEBUG attribution counters dump on exit.
#
# Usage: attribution_census.sh [binary ...]     (default: /tmp/corpus/*)
#
# Output: a `### <name> rc=<n>` header per binary followed by
# `key=count` lines.

set -uo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
debug="$root/_build-debug"

if ! command -v bap >/dev/null 2>&1; then
  eval "$(opam env 2>/dev/null)" || true
fi

echo "attribution_census: building vsa-debug plugin in $debug" >&2
dune build --build-dir "$debug" --profile vsa-debug -j 2 @install >&2 || exit 1

export OCAMLPATH="$debug/install/default/lib:${OCAMLPATH:-}"

bins=("$@")
if [ ${#bins[@]} -eq 0 ]; then
  bins=(/tmp/corpus/*)
fi

emit=/tmp/attr_census_emit
mkdir -p "$emit"

for b in "${bins[@]}"; do
  name="$(basename "$b")"
  err="$(mktemp)"
  bap "$b" --pass=hike-convlir --hike-output-file="$emit/$name.ll" \
    >/dev/null 2>"$err"
  rc=$?
  printf '### %s rc=%d\n' "$name" "$rc"
  grep 'hike-attr-census:' "$err" | sed 's/^hike-attr-census: //'
  if ! grep -q 'hike-attr-census:' "$err"; then
    echo "  (NO CENSUS DUMP — debug plugin not loaded?)"
  fi
  rm -f "$err"
done
