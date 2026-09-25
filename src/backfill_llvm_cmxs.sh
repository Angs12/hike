#!/usr/bin/env bash
# Makes the [llvm] package dynlinkable (it ships no llvm.cmxs/META).
# Builds llvm.cmxs with bapbundle's own recipe. Idempotent: rebuilds
# only when the cmxa/C archives are newer; errors are loud.
set -euo pipefail

LLVM_DIR="$(ocamlfind query llvm 2>/dev/null || true)"
if [ -z "$LLVM_DIR" ]; then
  echo "backfill_llvm_cmxs: the [llvm] package is not installed" >&2
  exit 1
fi

# Toolchain lookup.
OCAMLOPT="${OCAMLOPT:-ocamlopt.opt}"
if ! command -v "$OCAMLOPT" >/dev/null 2>&1; then OCAMLOPT=ocamlopt; fi

cd "$LLVM_DIR"
# Fresh only when the cmxs is newer than every input and META exists: a
# stale cmxa/libllvm_*.a must rebuild, and the missing-META backfill must
# still run.
needs=0
[ -f llvm.cmxs ] || needs=1
[ -f META ] || needs=1
for f in llvm.cmxa libllvm_*.a; do
  [ -e "$f" ] || continue
  if [ "$needs" -eq 0 ] && [ "$f" -nt llvm.cmxs ]; then needs=1; fi
done
if [ "$needs" -eq 0 ]; then
  exit 0   # fresh — nothing to do
fi

echo "backfill_llvm_cmxs: building $LLVM_DIR/llvm.cmxs (bapbundle's recipe)" >&2
"$OCAMLOPT" -shared -linkall -I "$LLVM_DIR" \
  -o "$LLVM_DIR/llvm.cmxs" \
  "$LLVM_DIR/llvm.cmxa" \
  $(ls "$LLVM_DIR"/libllvm_*.a)

# Upstream ships no META; backfill it.
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
