#!/usr/bin/env bash
# cppo_preprocess.sh — the profile-keyed debug-conditional preprocessor,
# chained BEFORE the ppx_bap driver (the full Jane Street rewriter set
# that regenerates the [@@deriving equal] functions — equal_vsa_kind et
# al. — so it must stay in the chain).
#
# Principle #6 (2026-09-02 restatement): instrumentation is NOT COMPILED
# INTO the production binary. Every debug print lives behind cppo's
#     #ifdef VSA_DEBUG ... #endif
# in the .ml source; this wrapper decides which text reaches the compiler:
#
#   $1 = %{profile}   (dune passes it)
#   $2 = %{input-file} (.ml or .mli — dune preprocesses both)
#
#   vsa-debug  ->  cppo -D VSA_DEBUG | ppx-jane -impl|-intf -
#   anything   ->  cppo                | ppx-jane -impl|-intf -
#
# (the #ifdef blocks VANISH from every non-vsa-debug build)
#
# The debug build is opt-in and keeps its own build directory so neither
# build evicts the other (measured 2026-09-02: without this, every profile
# switch is a full 10-22s rebuild in BOTH directions):
#
#   dune build --build-dir _build-debug --profile vsa-debug
#
# (run a probe with the instrumentation live:
#   dune exec --build-dir _build-debug --profile vsa-debug <probe>.exe -- <bin>)

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
