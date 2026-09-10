#!/usr/bin/env bash
# Structural asserts over emitted .ll modules.
# Usage: check_allocas.sh <out_dir> (holds out_<name>.ll; exit 0 iff all pass).
#   (a) any %stack_rN reference implies >= 1 stack_rN alloca.
#   (b) no GEP into a stack_rN alloca takes an sp-derived index
#       (dynamic loop-counter indexes are fine).
#   (c) no @stack global reference.
#   (d) each memory-touching define has exactly one frame alloca shape
#       (precise = stack_r-only, degraded = frame-only; stack-free exempt).
#   (e) no entry-edge poison phis.
# INFO: per-module inttoptr-derived load count (visibility only).

set -u

OUT_DIR="${1:-/tmp/heritage_p5}"
FAIL=0
PASS=0

for ll in "$OUT_DIR"/out_*.ll; do
  name="$(basename "$ll" .ll)"

  # (a) any %stack_rN reference implies >= 1 `alloca [`.
  n_refs="$(grep -c '%stack_r[0-9]' "$ll")"
  n_allocas="$(grep -c 'alloca \[' "$ll")"
  if [ "$n_refs" -gt 0 ] && [ "$n_allocas" -lt 1 ]; then
    echo "FAIL $name: (a) $n_refs stack_rN reference(s) but no stack_rN alloca"
    FAIL=$((FAIL + 1))
  else
    echo "PASS $name: (a) $n_allocas stack_rN alloca(s) for $n_refs stack_rN ref(s)"
    PASS=$((PASS + 1))
  fi

  # (b) no stack_rN GEP takes an sp-derived index.
  #     Dynamic loop-counter indexes pass; sp roots are the SP Slot
  #     (entry anchor store/load, T4), the anchor ptrtoint, and the
  #     Caller-Window Parameter (%hike_window — the window base, not SP).
  #     Blind spot: CHAIN skips non-anchor sub shapes, so other
  #     sub-routed sp values evade this tripwire.
  bad="$(awk '
    function chain(v) { return index(" " CHAIN " ", " " v " ") > 0 }
    function add(v)  { if (v != "" && !chain(v)) CHAIN = CHAIN " " v }
    # sp roots (T4 grammar): the SP Slot alloca load, the entry anchor
    # ptrtoint, and the Caller-Window Parameter. %hike_stack is GONE.
    /ptrtoint.*to i64/ {
      if (match($0, /%[A-Za-z0-9_.]+ = ptrtoint/)) {
        if (match($0, /^  %[^ ]+ = ptrtoint/)) { v = substr($0, 3, index(substr($0,3), " ")-1); add(v) }
      }
    }
    /load i64, ptr %sp_slot/ {
      if (match($0, /^  %[^ ]+ = load/)) { v = substr($0, 3, index(substr($0,3), " ")-1); add(v) }
    }
    /%hike_window/ {
      if (match($0, /%hike_window/)) add("%hike_window")
    }
    /%anchor_i64/ {
      if (match($0, /%anchor_i64/)) add("%anchor_i64")
      if (match($0, /%[0-9]+ = phi i64.*%anchor_i64/)) {
        if (match($0, /^  %[0-9]+ = phi/)) { lhs = substr($0, 3, index(substr($0,3), " ")-1); add(lhs) }
      }
    }
    # Arithmetic propagation, except the anchor-sub offset pattern
    # (`sub %addr, %anchor_i64` yields a clean index, not sp-derived).
    /^  %[^ ]+ = (sub|add|mul|and|or|xor|shl|lshr|ashr) i64 %/ {
      if (match($0, /^  %[^ ]+/)) { lhs = substr($0, 3, index(substr($0,3), " ")-1) }
      # anchor-sub cancellation: the result is the offset, not sp-derived
      if (match($0, /sub i64/) && index($0, "%anchor_i64") > 0) { next }
      # find any %var after i64
      n = split($0, parts, "i64 ")
      for (i=2; i<=n; i++) {
        if (match(parts[i], /%[A-Za-z0-9_.]+/)) {
          rhs = substr(parts[i], RSTART, RLENGTH)
          if (chain(rhs)) { add(lhs); break }
        }
      }
    }
    # phi merges mentioning a chain value propagate too
    /phi i64/ {
      if (match($0, /^  %[^ ]+ = phi/)) {
        lhs = substr($0, 3, index(substr($0,3), " ")-1)
        # mark lhs when the line holds a chain token
        tmp = $0
        while (match(tmp, /%[A-Za-z0-9_.]+/)) {
          tok = substr(tmp, RSTART, RLENGTH)
          if (chain(tok)) { add(lhs); break }
          tmp = substr(tmp, RSTART+RLENGTH)
        }
      }
    }
    # violation: GEP into stack_r with a chain index
    /getelementptr.*%stack_r[0-9]+/ {
      # index operand follows "i64": const or %var
      line = $0
      # strip through the stack_r base (sub takes regex first)
      sub(/.*%stack_r[0-9]+, /, "", line)
      if (match(line, /i64 %[A-Za-z0-9_.]+/)) {
        idx = substr(line, RSTART+4, RLENGTH-4)
        if (chain(idx)) print "sp-derived GEP index into stack_r: " idx " in: " $0
      }
    }
  ' "$ll" | head -5)"
  if [ -n "$bad" ]; then
    echo "FAIL $name: (b) sp-derived GEP index into stack_r alloca:"
    echo "$bad" | sed 's/^/    /'
    FAIL=$((FAIL + 1))
  else
    echo "PASS $name: (b) no sp-derived GEP index into stack_r"
    PASS=$((PASS + 1))
  fi

  # (c) no @stack global reference.
  n_stack="$(grep -c '@stack' "$ll")"
  if [ "$n_stack" -ne 0 ]; then
    echo "FAIL $name: (c) module references the legacy @stack global $n_stack time(s)"
    FAIL=$((FAIL + 1))
  else
    echo "PASS $name: (c) no @stack global references"
    PASS=$((PASS + 1))
  fi

  # (d) per-function model-storage shape (T3 vocabulary): a define may
  #     carry ONE model storage — the fallback %frame (degraded), the
  #     stack_rN allocas (precise) — or none at all: the caller lane
  #     (hike_stack-parameterized) and the foreign/untagged exception
  #     lane (inttoptr real addresses) legitimately own no model
  #     storage.  Violations: MIXING frame+stack_r, or referencing
  #     model storage the define does not own.
  n_bad="$(awk '
    BEGIN { in_define=0; bad=0 }
    function check() {
      if (n_frame_a > 0 && n_stackr_a > 0) { bad++; return }
      if (n_frame_a == 0 && n_stackr_a == 0 && (n_frame_ref > 0 || n_stackr_ref > 0)) { bad++ }
    }
    /^define / {
      if (in_define) { check() }
      in_define=1; n_frame_a=0; n_stackr_a=0; n_frame_ref=0; n_stackr_ref=0
      next
    }
    /^declare / { next }
    in_define {
      if ($0 ~ /%frame = alloca/) n_frame_a++
      if ($0 ~ /%stack_r[0-9]+ = alloca/) n_stackr_a++
      if ($0 ~ /%frame/) n_frame_ref++
      if ($0 ~ /%stack_r[0-9]+/) n_stackr_ref++
    }
    END { if (in_define) { check() } ; print bad }
  ' "$ll")"
  if [ "$n_bad" -ne 0 ]; then
    echo "FAIL $name: (d) $n_bad define(s) violate model-storage shape (mixing frame+stack_r, or phantom model-storage references)"
    FAIL=$((FAIL + 1))
  else
    echo "PASS $name: (d) model-storage shape ok (frame, stack_r, caller-lane, or foreign-only)"
    PASS=$((PASS + 1))
  fi

  # (e) no entry-edge poison phis (UB that folds under opt).
  n_poison_entry="$(grep -c 'phi .*\[ poison, %entry' "$ll")"
  if [ "$n_poison_entry" -gt 0 ]; then
    echo "FAIL $name: (e) $n_poison_entry entry-edge poison phi(s) — UB folds under opt"
    FAIL=$((FAIL + 1))
  else
    echo "PASS $name: (e) 0 entry-edge poison phis"
    PASS=$((PASS + 1))
  fi

  # INFO (non-failing): per-module inttoptr-derived load count.
  n_itop_loads="$(awk '
    /^  %[0-9]+ = inttoptr / {
      line = $0; sub(/^  /, "", line); split(line, a, " "); defs[a[1]] = 1
    }
    / = load / {
      if (match($0, /ptr %[0-9]+/)) {
        v = substr($0, RSTART + 4, RLENGTH - 4)
        if (v in defs) n++
      }
    }
    END { print n + 0 }
  ' "$ll")"
  echo "INFO $name: $n_itop_loads inttoptr-derived load(s)"
done

echo
echo "check_allocas: $PASS passed, $FAIL failed"
[ "$FAIL" -eq 0 ]
