#!/usr/bin/env bash
# The gate tier's shared pipeline: ONE copy of the render / link / run /
# compare recipe.  Sourced, never executed.

# The renderer: the llc on PATH, overridable for a pinned toolchain.
LLC="${HIKE_LLC:-llc}"

# llc a module to an object; no flags means -O0.
hike_llc() {
  local ll="$1" obj="$2"; shift 2
  if [ "$#" -eq 0 ]; then set -- -O0; fi
  command -v "$LLC" >/dev/null 2>&1 || {
    echo "FATAL: $LLC not found on PATH (set HIKE_LLC to pin one)" >&2
    return 127
  }
  "$LLC" "$@" -filetype=obj "$ll" -o "$obj"
}

# The lift entry every gate runs: the installed hike executable
# (Hike.Drive, ADR 0032).
hike_exe() {
  printf '%s/hike' "$(opam var bin 2>/dev/null)"
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
