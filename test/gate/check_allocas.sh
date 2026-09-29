#!/usr/bin/env bash
# Structural asserts over emitted .ll modules — derived from the
# section-range architecture's invariants (ADR 0010 / the v6 delta),
# not from any rendering.
# Usage: check_allocas.sh <out_dir> (holds out_<name>.ll; exit 0 iff all pass).
#   (a) every region/window reference implies its storage exists
#       (a stack_rN alloca; the window parameter for window mems).
#   (b) a region GEP's index must be an integer (never a ptrtoint of an
#       address value — the index is a model offset).
#   (c) no @stack global reference.
#   (d) residue discipline: no legacy %frame alloca (the residue is
#       stack_r0); at most one residue alloca per define; references
#       imply their alloca.
#   (e) no entry-edge poison phis.
#   (f) every section component/residue global is internal.
#   (g) the integer world escapes (D4b): no ptrtoint of a GEP into a
#       stack_rN alloca — GEP-derived pointers never become integers.
#   (h) window mems imply the window parameter: a define referencing
#       %hike_window_mem carries %hike_window.
#   INFO (non-failing): per-module inttoptr-derived load count.

set -u

OUT_DIR="${1:?usage: check_allocas.sh <out_dir>}"
FAIL=0
PASS=0

if ! compgen -G "$OUT_DIR/out_*.ll" >/dev/null; then
  echo "FATAL: no emitted IR under $OUT_DIR (run the lift gate first)" >&2
  exit 2
fi

for ll in "$OUT_DIR"/out_*.ll; do
  name="$(basename "$ll" .ll)"

  # The count rules (a/c/e/f/g) read one awk pass over the module;
  # the state-machine rules (b/d/INFO) keep their own passes.
  eval "$(awk '
    { line = $0
      if (match(line, /%stack_r[0-9]+ = alloca/)) {
        id = substr(line, RSTART, RLENGTH)
        sub(/ = alloca/, "", id)
        defined_sr[id] = 1
      }
      if (line ~ /%stack_r[0-9]/) n_sr_ref++
      if (line ~ /%stack_r[0-9]+ = alloca/) n_sr_alloca++
      if (line ~ /@stack/) n_stack++
      if (line ~ /phi .*\[ poison, %entry/) n_poison++
      if (line ~ /^@sec_comp_[0-9]+ =/) n_comp++
      if (line ~ /^@sec_res_[0-9]+ =/) n_res++
      if (line ~ /^@sec_(comp|res)_[0-9]+ =/ && line !~ /internal/) n_ext++
      if (line ~ /ptrtoint ptr getelementptr i8, ptr %stack_r[0-9]/) n_esc++
      if (line ~ /%hike_window_mem/) n_wm_ref++
      if (line ~ /%hike_window\)/) n_wp++
      # every referenced region id must have its own alloca
      rest = line
      while (match(rest, /%stack_r[0-9]+/)) {
        id = substr(rest, RSTART, RLENGTH)
        if (!(id in defined_sr)) missing_sr[id] = 1
        rest = substr(rest, RSTART + RLENGTH)
      }
    }
    END {
      m = 0
      for (id in missing_sr) m++
      printf "n_sr_ref=%d n_sr_alloca=%d n_sr_missing=%d n_stack=%d n_poison=%d n_comp=%d n_res=%d n_ext=%d n_esc=%d n_wm_ref=%d n_wp=%d", n_sr_ref, n_sr_alloca, m, n_stack, n_poison, n_comp, n_res, n_ext, n_esc, n_wm_ref, n_wp
    }
  ' "$ll")"
  # (a) references imply storage: every referenced stack_rN id needs its
  #     own alloca; a hike_window_mem reference requires the parameter.
  if [ "$n_sr_missing" -gt 0 ] || { [ "$n_sr_ref" -gt 0 ] && [ "$n_sr_alloca" -lt 1 ]; }; then
    echo "FAIL $name: (a) $n_sr_ref stack_rN reference(s), $n_sr_alloca alloca(s), $n_sr_missing undefined id(s)"
    FAIL=$((FAIL + 1))
  else
    echo "PASS $name: (a) $n_sr_alloca region alloca(s) for $n_sr_ref ref(s)"
    PASS=$((PASS + 1))
  fi
  if [ "$n_wm_ref" -gt 0 ] && [ "$n_wp" -lt 1 ]; then
    echo "FAIL $name: (a) window mem reference(s) but no %hike_window parameter"
    FAIL=$((FAIL + 1))
  else
    echo "PASS $name: (a) window mems ($n_wm_ref) vs the window parameter ($n_wp)"
    PASS=$((PASS + 1))
  fi

  # (b) a region GEP's index must be an integer: never the result of a
  #     ptrtoint of an address value (the index is a model offset).
  bad="$(awk '
    / = ptrtoint / {
      if (match($0, /^  %[A-Za-z0-9_.]+ = ptrtoint /)) {
        v = substr($0, 3, index(substr($0,3), " ")-1); itop[v] = 1
      }
    }
    /getelementptr.*%stack_r[0-9]+/ {
      line = $0
      while (match(line, /i64 %[A-Za-z0-9_.]+/)) {
        idx = substr(line, RSTART+4, RLENGTH-4)
        if (idx in itop)
          print "ptrtoint index into stack_r: " idx " in: " $0
        line = substr(line, RSTART+RLENGTH)
      }
    }
  ' "$ll" | head -5)"
  if [ -n "$bad" ]; then
    echo "FAIL $name: (b) region GEP index is a ptrtoint-derived address:"
    echo "$bad" | sed 's/^/    /'
    FAIL=$((FAIL + 1))
  else
    echo "PASS $name: (b) every region GEP index is an integer"
    PASS=$((PASS + 1))
  fi

  # (c) no @stack global reference.
  if [ "$n_stack" -ne 0 ]; then
    echo "FAIL $name: (c) module references the legacy @stack global $n_stack time(s)"
    FAIL=$((FAIL + 1))
  else
    echo "PASS $name: (c) no @stack global references"
    PASS=$((PASS + 1))
  fi

  # (d) residue discipline: the legacy %frame is gone; the residue is
  #     stack_r0 and a define carries at most one.
  n_frame="$(grep -c '%frame = alloca' "$ll")"
  n_multi="$(awk '
    /^define / { if (in_d && n_r0 > 1) bad++; in_d = 1; n_r0 = 0 }
    /%stack_r0 = alloca/ { n_r0++ }
    END { if (in_d && n_r0 > 1) bad++; print bad + 0 }
  ' "$ll")"
  if [ "$n_frame" -ne 0 ] || [ "$n_multi" -ne 0 ]; then
    echo "FAIL $name: (d) legacy %frame alloca(s)=$n_frame, multi-residue define(s)=$n_multi"
    FAIL=$((FAIL + 1))
  else
    echo "PASS $name: (d) residue discipline ok (no %frame; at most one stack_r0 per define)"
    PASS=$((PASS + 1))
  fi

  # (e) no entry-edge poison phis (UB that folds under opt).
  n_poison_entry="$n_poison"
  if [ "$n_poison_entry" -gt 0 ]; then
    echo "FAIL $name: (e) $n_poison_entry entry-edge poison phi(s) — UB folds under opt"
    FAIL=$((FAIL + 1))
  else
    echo "PASS $name: (e) 0 entry-edge poison phis"
    PASS=$((PASS + 1))
  fi

  # (f) every section component/residue global is internal — external
  # linkage would fork the address world and block the consumer's
  # constant propagation.
  if [ "$n_comp" -gt 0 ] || [ "$n_res" -gt 0 ]; then
    if [ "$n_ext" -gt 0 ]; then
      echo "FAIL $name: (f) $n_ext non-internal sec_comp/sec_res global(s)"
      FAIL=$((FAIL + 1))
    else
      echo "PASS $name: (f) sec globals internal ($n_comp comp(s), $n_res run(s))"
      PASS=$((PASS + 1))
    fi
  else
    echo "PASS $name: (f) unsplit (no section components)"
    PASS=$((PASS + 1))
  fi

  # (g) the integer world escapes (D4b): no ptrtoint of a GEP into a
  #     stack_rN alloca — GEP-derived pointers never become integers
  #     (their integer is the alloca's base, a different world).
  if [ "$n_esc" -ne 0 ]; then
    echo "FAIL $name: (g) $n_esc GEP-derived stack pointer(s) escape as integers"
    FAIL=$((FAIL + 1))
  else
    echo "PASS $name: (g) no GEP-derived stack pointer escapes as an integer"
    PASS=$((PASS + 1))
  fi

  # INFO (non-failing): per-module inttoptr-derived load count.
  n_itop_loads="$(awk '
    / = inttoptr / {
      if (match($0, /^  %[A-Za-z0-9_.]+ = inttoptr /)) {
        line = $0; sub(/^  /, "", line); split(line, a, " "); defs[a[1]] = 1
      }
    }
    / = load / {
      if (match($0, /ptr %[A-Za-z0-9_.]+/)) {
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
