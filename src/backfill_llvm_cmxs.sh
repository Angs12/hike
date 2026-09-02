#!/usr/bin/env bash
# backfill_llvm_cmxs.sh — make the [llvm] package dynlinkable.
#
# The [llvm] opam package ships llvm.cma/cmxa + C archives but NO
# llvm.cmxs and NO findlib META — so a dune-built plugin that (libraries
# llvm) cannot dynlink (hike.cmxs: undefined symbol llvm_int64_of_const).
# bapbuild hid this by building llvm.cmxs INSIDE the bundle at pack time;
# with the plugin built by dune (2026-09-03) the workspace builds the
# identical object instead — the recipe is byte-for-byte bapbundle's own
# (ocamlopt -shared -linkall llvm.cmxa libllvm_*.a).
#
# Idempotent: re-runs only rebuild the cmxs when the cmxa/C archives are
# newer. Errors are LOUD (no silent skip — a plugin that dynlinks against
# a stale llvm is yesterday's poison-phi class).
set -euo pipefail

LLVM_DIR="$(ocamlfind query llvm 2>/dev/null || true)"
if [ -z "$LLVM_DIR" ]; then
  echo "backfill_llvm_cmxs: the [llvm] package is not installed" >&2
  exit 1
fi

# find the toolchain
OCAMLOPT="${OCAMLOPT:-ocamlopt.opt}"
if ! command -v "$OCAMLOPT" >/dev/null 2>&1; then OCAMLOPT=ocamlopt; fi

cd "$LLVM_DIR"
if [ llvm.cmxs -nt llvm.cmxa ] 2>/dev/null; then
  exit 0   # fresh — nothing to do
fi

echo "backfill_llvm_cmxs: building $LLVM_DIR/llvm.cmxs (bapbundle's recipe)" >&2
"$OCAMLOPT" -shared -linkall -I "$LLVM_DIR" \
  -o "$LLVM_DIR/llvm.cmxs" \
  "$LLVM_DIR/llvm.cmxa" \
  $(ls "$LLVM_DIR"/libllvm_*.a)

# the missing findlib META (backfilled; upstream ships none)
if [ ! -f "$LLVM_DIR/META" ]; then
  cat > "$LLVM_DIR/META" <<'METAEOF'
version = "backfill"
description = "OCaml bindings for LLVM (META + plugin(native) backfilled by hike)"
archive(byte) = "llvm.cma"
archive(native) = "llvm.cmxa"
plugin(byte) = "llvm.cma"
plugin(native) = "llvm.cmxs"
METAEOF
  echo "backfill_llvm_cmxs: wrote $LLVM_DIR/META" >&2
fi
echo "backfill_llvm_cmxs: done" >&2
