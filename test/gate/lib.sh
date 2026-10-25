#!/usr/bin/env bash
# The gate tier's shared pipeline: ONE copy of the render / link / run /
# compare recipe.  Sourced, never executed.

# The renderer: pinned to the LLVM release the project targets.
LLC="${HIKE_LLC:-llc-19}"

# llc a module to an object; no flags means -O0.
hike_llc() {
  local ll="$1" obj="$2"; shift 2
  if [ "$#" -eq 0 ]; then set -- -O0; fi
  command -v "$LLC" >/dev/null 2>&1 || {
    echo "FATAL: $LLC not found on PATH (set HIKE_LLC to another llc)" >&2
    return 127
  }
  "$LLC" "$@" -filetype=obj "$ll" -o "$obj"
}

# The lift entry every gate runs: the installed hike executable
# (Hike.Drive, ADR 0032).
# The signatures every lift runs under: without them the lift cannot tell
# which imports never return.  Override with HIKE_SIGNATURES.
HIKE_SIGNATURES="${HIKE_SIGNATURES:-$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)/data/glibc.sexp}"
export HIKE_SIGNATURES

# The installed executable: an explicit HIKE_EXE wins (a bare name is
# resolved on PATH), else `hike` on PATH.
hike_exe() {
  local exe="${HIKE_EXE:-}"
  [ -n "$exe" ] || exe="$(type -P -- hike 2>/dev/null || true)"
  case "$exe" in
    */*) ;;
    *) exe="$(type -P -- "$exe" 2>/dev/null || true)" ;;
  esac
  if [ -z "$exe" ]; then
    echo "FATAL: no hike executable: install it, put it on PATH, or set HIKE_EXE" >&2
    return 1
  fi
  printf '%s' "$exe"
}

# The BAP library root the toolchain stamp covers: an explicit HIKE_LIBDIR
# wins; else the root the hike wrapper exports (BAP_PLUGIN_PATH is
# <root>/bap-common/plugins); else the parent of findlib's bap package.
bap_libdir() {
  local first
  if [ -n "${HIKE_LIBDIR:-}" ]; then
    printf '%s' "$HIKE_LIBDIR"
    return 0
  fi
  first="${BAP_PLUGIN_PATH%%:*}"
  case "$first" in
    */bap-common/plugins)
      printf '%s' "${first%/bap-common/plugins}"
      return 0 ;;
  esac
  first="$(ocamlfind query bap 2>/dev/null || true)"
  if [ -n "$first" ] && [ -d "$first" ]; then
    printf '%s' "$(dirname "$first")"
    return 0
  fi
  return 1
}

# The run timeout every gate shares (a corpus binary must finish in
# seconds; 15 s is the generous ceiling).
HIKE_RUN_TIMEOUT="${HIKE_RUN_TIMEOUT:-15}"

# Known unresolved indirect-tail-call reds.  The lift and matrix gates
# skip these by name; a red here is a known limitation, not a regression.
EXPECTED_LIFT_REDS="enum_field_switch enum_field_guarded_switch"

is_expected_lift_red() {
  case " $EXPECTED_LIFT_REDS " in
    *" $1 "*) return 0 ;;
    *) return 1 ;;
  esac
}

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
