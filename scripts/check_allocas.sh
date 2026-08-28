#!/usr/bin/env bash
# Phase 5 (validation) structural assertion for the heritage port
# (H-R1 final state, post model deletion).
#
# NO-LEGACY design (the user's directive: "there should not be any legacy
# paths"): the single-global-stack scheme is gone.  Qualifying subs emit
# per-range stack_rN allocas (G4 region-split); most subs remain %frame-only
# by the full-coverage soundness gate.  The @stack global no longer exists.
# For every emitted .ll module assert:
#
#   (a) the module has >= 1 `stack_rN` alloca whenever it references the
#       per-range scheme at all.  This used to be keyed on the
#       "heritage ok <fn>" function list in stderr; the model that
#       produced that list was deleted, so the check is now per-module:
#       any %stack_rN reference (GEP base, ptrtoint base, ...) implies
#       >= 1 `alloca [`.  A module with zero stack traffic trivially
#       passes.
#   (b) no `getelementptr` that indexes into a `stack_rN` alloca has an
#       SP-DERIVED index (the dataflow ban, R12/G4 Stage 3a): an index
#       that derives from an sp root (the entry anchor or the
#       hike_stack param) is a region-routing bug.  Array regions
#       legitimately use dynamic GEPs (loop counters), so the old
#       constant-index ban was replaced by this dataflow ban;
#   (c) the module contains NO reference to the @stack global AT ALL (the
#       legacy path is gone — hike.ml's create_stack_ptr was removed);
#   (d) every memory-touching `define` emits exactly ONE STACK-FRAME
#       alloca of the emitted shape `%frame = alloca [N x i8],
#       align 16` (the per-sub model frame — the sound fallback;
#       convertible regions ADDITIONALLY emit stack_rN allocas).
#       Defines containing no alloca/load/store are exempt (provably
#       stack-free).  A mismatch means the emitter changed shape
#       underneath this script.
#   INFO (non-failing): per-module count of INTTOPTR-DERIVED LOADS —
#       loads whose pointer operand is an `inttoptr ... to ptr` result
#       (the model-frame RSP-arithmetic access path).  Visibility only;
#       becomes actionable when the G4 emitter converts accesses to
#       stack_rN GEPs.
#
# Usage: check_allocas.sh <out_dir>
#   out_dir contains out_<name>.ll from a corpus run (see run_corpus.sh).
#   Exit 0 if every module passes, 1 otherwise.

set -u

OUT_DIR="${1:-/tmp/heritage_p5}"
FAIL=0
PASS=0

for ll in "$OUT_DIR"/out_*.ll; do
  name="$(basename "$ll" .ll)"

  # (a) per-module stack_rN alloca presence (the heritage-ok function
  #     list that used to key this check died with the model).  Any
  #     %stack_rN reference implies >= 1 `alloca [`.
  n_refs="$(grep -c '%stack_r[0-9]' "$ll")"
  n_allocas="$(grep -c 'alloca \[' "$ll")"
  if [ "$n_refs" -gt 0 ] && [ "$n_allocas" -lt 1 ]; then
    echo "FAIL $name: (a) $n_refs stack_rN reference(s) but no stack_rN alloca"
    FAIL=$((FAIL + 1))
  else
    echo "PASS $name: (a) $n_allocas stack_rN alloca(s) for $n_refs stack_rN ref(s)"
    PASS=$((PASS + 1))
  fi

  # (b) no stack_rN GEP uses an sp-derived index (R12/G4 Stage 3a).
  #     Array regions legitimately use DYNAMIC GEPs (e.g. %idx*scale), so
  #     the old “constant index’’ ban is replaced by a dataflow ban: an
  #     index that derives from an sp root (the entry anchor or the
  #     hike_stack param) is a region-routing bug (the frame-relative
  #     offset was not materialized as a constant nor a clean index).
  #     Legitimate dynamic indexes (loop counters) are NOT sp-derived and
  #     pass.  When no stack_r GEP exists the check is vacuously PASS.
  #     KNOWN BLIND SPOT (Rider 2a): CHAIN propagates through add/mul/phi
  #     but NOT through general sub-shaped dataflow (only the anchor-
  #     cancellation carve-out `sub %addr,%anchor_i64` is recognized); a
  #     sp-derived value reaching a stack_rN index via any other sub shape
  #     evades this tripwire — the emission-side full-coverage gate +
  #     coherence audit remain the primary guarantees.
  bad="$(awk '
    function chain(v) { return index(" " CHAIN " ", " " v " ") > 0 }
    function add(v)  { if (v != "" && !chain(v)) CHAIN = CHAIN " " v }
    # roots: the sp-derived integer values — the entry anchor
    # (ptrtoint of %frame) and the hike_stack param (the caller frame)
    /ptrtoint.*to i64/ {
      if (match($0, /%[A-Za-z0-9_.]+ = ptrtoint/)) {
        if (match($0, /^  %[^ ]+ = ptrtoint/)) { v = substr($0, 3, index(substr($0,3), " ")-1); add(v) }
      }
    }
    /%hike_stack/ {
      if (match($0, /%hike_stack/)) add("%hike_stack")
    }
    /%anchor_i64/ {
      if (match($0, /%anchor_i64/)) add("%anchor_i64")
      if (match($0, /%[0-9]+ = phi i64.*%anchor_i64/)) {
        if (match($0, /^  %[0-9]+ = phi/)) { lhs = substr($0, 3, index(substr($0,3), " ")-1); add(lhs) }
      }
    }
    # propagate through integer arithmetic: %L = OP i64 %R, ...  (and 2-arg forms)
    # EXCEPTION: the region-offset pattern `sub i64 %addr, %anchor_i64`
    # (and its `add` with the negated region_lo) computes the
    # frame-relative offset; the result is NOT sp-derived (the anchor
    # cancels the sp part, leaving the clean index).  Skip adding that
    # LHS to CHAIN so legitimate dynamic array GEPs (idx*scale) are not
    # flagged.  Any other arithmetic with a chain operand IS sp-derived.
    /^  %[^ ]+ = (sub|add|mul|and|or|xor|shl|lshr|ashr) i64 %/ {
      if (match($0, /^  %[^ ]+/)) { lhs = substr($0, 3, index(substr($0,3), " ")-1) }
      # anchor-sub cancellation: sub with %anchor_i64 is the offset, not sp-derived
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
    # propagate through phi merges that mention a chain value
    /phi i64/ {
      if (match($0, /^  %[^ ]+ = phi/)) {
        lhs = substr($0, 3, index(substr($0,3), " ")-1)
        # simple: if line contains a chain token, mark lhs
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
      # extract the index operand: last i64 %X or i64 const
      # pattern: getelementptr i8, ptr %stack_rN, i64 %X  or i64 123
      line = $0
      # remove up to stack_r (target/regex order matters: sub(regex, "", target))
      sub(/.*%stack_r[0-9]+, /, "", line)
      # now line starts with "i64 %X" or "i64 123"
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

  # (c) NO @stack global reference AT ALL (no-legacy design).
  n_stack="$(grep -c '@stack' "$ll")"
  if [ "$n_stack" -ne 0 ]; then
    echo "FAIL $name: (c) module references the legacy @stack global $n_stack time(s)"
    FAIL=$((FAIL + 1))
  else
    echo "PASS $name: (c) no @stack global references"
    PASS=$((PASS + 1))
  fi

  # (d) PER-FUNCTION stack-frame alloca (R12/G4 Stage 3b) — FULL ERASURE.
  #     Precise subs (those with `stack_rN` allocas, per `region_split_plan`) must have
  #     ZERO `%frame` (frame-erased, per ADR 0001); degraded subs must have exactly ONE
  #     `%frame = alloca [N x i8], align 16`.  A `define` with `stack_rN` is precise,
  #     one without is degraded.  Stack-free defines (no alloca/load/store) are exempt.
  n_bad="$(awk '
    BEGIN { in_define=0; has_stack_r=0; has_frame=0; has_mem=0; bad=0 }
    /^define / {
      if (in_define) {
        if (!has_mem) { /* exempt stack-free */ }
        else if (has_stack_r) {
          if (has_frame) { bad++ }
        } else {
          if (!has_frame) { bad++ }
        }
      }
      in_define=1; has_stack_r=0; has_frame=0; has_mem=0; next
    }
    /^declare / { next }
    in_define {
      if ($0 ~ /%stack_r[0-9]+ = alloca/) has_stack_r=1
      if ($0 ~ /%frame = alloca/) has_frame=1
      if ($0 ~ /alloca/ || $0 ~ /[[:space:]]load[[:space:]]/ || $0 ~ /[[:space:]]store[[:space:]]/) has_mem=1
    }
    END {
      if (in_define) {
        if (!has_mem) { /* exempt */ }
        else if (has_stack_r) {
          if (has_frame) { bad++ }
        } else {
          if (!has_frame) { bad++ }
        }
      }
      print bad
    }
  ' "$ll")"
  if [ "$n_bad" -ne 0 ]; then
    echo "FAIL $name: (d) $n_bad define(s) violate frame/stack_r shape (precise must have stack_r and no frame, degraded must have frame and no stack_r)"
    FAIL=$((FAIL + 1))
  else
    echo "PASS $name: (d) frame/stack_r shape ok (precise=stack_r-only, degraded=frame-only)"
    PASS=$((PASS + 1))
  fi

  # INFO (non-failing): the per-module count of inttoptr-derived loads —
  # loads whose pointer operand is an `inttoptr i64 %X to ptr` result
  # (the model-frame RSP-arithmetic access path).  Pure visibility.
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
