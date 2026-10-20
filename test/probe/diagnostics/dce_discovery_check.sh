#!/usr/bin/env bash
# Probe check: the narrow DCE may not remove a def that feeds a
# materialised code word, and the materialised-word set must not change.
# Usage: dce_discovery_check.sh <binary> [<binary> ...]
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/../../.." && pwd)"
EXE=(dune exec --root "$ROOT" test/probe/diagnostics/dce_lift.exe --)
status=0
for bin in "$@"; do
  out="$("${EXE[@]}" "$bin" census 2>/dev/null)"
  census="$(printf '%s\n' "$out" | sed -n 's/^CENSUS\t//p')"
  disc="$(printf '%s\n' "$out" | sed -n 's/^DISCOVERY\t[^\t]*\t//p')"
  word_defs="$(printf '%s\n' "$disc" | sed -n 's/.*word_defs=\([0-9]*\).*/\1/p')"
  base_words="$(printf '%s\n' "$disc" | sed -n 's/.*words_base=\([0-9]*\).*/\1/p')"
  dce_words="$(printf '%s\n' "$disc" | sed -n 's/.*words_dce=\([0-9]*\).*/\1/p')"
  base_hash="$(printf '%s\n' "$disc" | sed -n 's/.*hash_base=\(-*[0-9]*\).*/\1/p')"
  dce_hash="$(printf '%s\n' "$disc" | sed -n 's/.*hash_dce=\(-*[0-9]*\).*/\1/p')"
  if [ -z "$census" ] || [ -z "$disc" ]; then
    echo "FAIL $(basename "$bin"): no census report" >&2
    status=1
  elif [ "${word_defs:-1}" -ne 0 ]; then
    echo "FAIL $(basename "$bin"): $word_defs removed def(s) feed a materialised word" >&2
    status=1
  elif [ "${base_words:-x}" != "${dce_words:-y}" ] \
       || [ "${base_hash:-x}" != "${dce_hash:-y}" ]; then
    echo "FAIL $(basename "$bin"): materialised words changed ($base_words/$base_hash -> $dce_words/$dce_hash)" >&2
    status=1
  else
    echo "PASS $(basename "$bin"): word_defs=0 words=$base_words hash=$base_hash"
  fi
done
exit "$status"
