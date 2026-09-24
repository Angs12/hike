#!/usr/bin/env bash
# The gate tier's shared pipeline: ONE copy of the render / link / run /
# compare recipe and the provenance check.  Sourced, never executed.

# Rename the harness-colliding symbols so the lifted module links with
# harness.c: @main becomes @hike_main, and the crt1-compiled
# @_dl_relocate_static_pie is suffixed.
hike_rename() {
  sed -e 's/@main/@hike_main/g' \
      -e 's/@_dl_relocate_static_pie/@_dl_relocate_static_pie_lifted/g' \
      "$1" >"$2"
}

# llc a module to an object; no flags means -O0.
hike_llc() {
  local ll="$1" obj="$2"; shift 2
  if [ "$#" -eq 0 ]; then set -- -O0; fi
  llc "$@" -filetype=obj "$ll" -o "$obj"
}

# Link a lifted object with harness.c, plus setjmp_stub.S when the module
# uses setjmp/longjmp.  Extra linker flags come after the module argument.
# The link stays -no-pie: a linker constraint of the harness artifact
# (baked absolute constants + extern_weak refs reject DT_TEXTREL).
hike_link() {
  local obj="$1" ll="$2" bin="$3" here="$4"; shift 4
  local stub=""
  if grep -q '@_setjmp\|@longjmp' "$ll"; then stub="$here/setjmp_stub.S"; fi
  gcc -O0 -no-pie -o "$bin" "$obj" "$here/harness.c" $stub "$@"
}

# The run timeout every gate shares (a corpus binary must finish in
# seconds; 15 s is the generous ceiling).
HIKE_RUN_TIMEOUT="${HIKE_RUN_TIMEOUT:-15}"

# Run lifted vs native with identical argv[0] (glibc prints it in usage
# messages) and the shared timeout; compare both rc and stdout bytes.
# The fifth argument names the lifted output stem (default
# <base>_lifted).  Prints the verdict; returns non-zero on any
# failure, timeout included.
hike_run_cmp() {
  local lifted="$1" native="$2" out="$3" base="$4" lbase="${5:-${base}_lifted}"
  timeout "$HIKE_RUN_TIMEOUT" bash -c 'exec -a "$1" "$2"' _ prog "$lifted" >"$out/${lbase}.out" 2>&1
  local lrc=$?
  timeout "$HIKE_RUN_TIMEOUT" bash -c 'exec -a "$1" "$2"' _ prog "$native" >"$out/${base}_native.out" 2>&1
  local nrc=$?
  if [ "$lrc" -eq 124 ] || [ "$nrc" -eq 124 ]; then
    echo "FAIL $base (timeout: lifted rc=$lrc native rc=$nrc)"
    return 1
  fi
  if [ "$lrc" -ne "$nrc" ] || ! cmp -s "$out/${lbase}.out" "$out/${base}_native.out"; then
    echo "FAIL $base (native rc=$nrc vs lifted rc=$lrc)"
    diff "$out/${base}_native.out" "$out/${lbase}.out" | head -3 | sed 's/^/    /'
    return 1
  fi
  return 0
}

# The provenance gate: the installed plugin must have been built from the
# given tree.  The shared switch can hold another session's build, so a
# mismatch is a hard stop, never a warning.
provenance_ok() {
  local tree="$1" prov rec
  prov="$(opam var lib 2>/dev/null)/hike/hike.cmxs.provenance"
  if [ ! -f "$prov" ]; then
    echo "FATAL: no installed plugin provenance at $prov — run src/record_provenance.sh" >&2
    return 2
  fi
  rec="$(sed -n 's/^tree: //p' "$prov")"
  if [ "$rec" != "$tree" ]; then
    echo "FATAL: installed plugin was built from '$rec', not '$tree'" >&2
    echo "       rebuild+reinstall from this tree, then re-run src/record_provenance.sh" >&2
    return 3
  fi
  return 0
}
