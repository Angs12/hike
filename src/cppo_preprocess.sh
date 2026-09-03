#!/usr/bin/env bash
# Profile-keyed debug-conditional preprocessor, chained BEFORE ppx-jane.
# $1 = %{profile}, $2 = %{input-file} (.ml or .mli).
# vsa-debug passes -D VSA_DEBUG; other profiles plain cppo. #ifdef blocks
# vanish from non-vsa-debug builds.
# Debug builds keep their own dir so neither build evicts the other:
#   dune build --build-dir _build-debug --profile vsa-debug

set -euo pipefail
profile="$1"
input="$2"

# .mli files must be parsed as interfaces
kind="-impl"
case "$input" in
  *.mli) kind="-intf" ;;
esac

if [ "$profile" = "vsa-debug" ]; then
  cppo -D VSA_DEBUG "$input"
else
  cppo "$input"
fi | ppx-jane "$kind" -
