#!/usr/bin/env bash
# The convergence report: for every source, run the consumer's optimizer
# (opt-21 -O2) on BOTH lifts (-O0 input and -O2 input), execute the
# results, and classify convergence SEMANTICALLY (rc + stdout vs the
# native -O0 program), with instruction counts as the quality dimension.
# The native -O2 binary's text size is the input-complexity reference.
#
# Usage: convergence_report.sh <corpus_o0> <corpus_o2> <lift_o0> <lift_o2> [workdir]
set -u
C0="$1"; C2="$2"; L0="$3"; L2="$4"
W="${5:-/tmp/conv_work}"; mkdir -p "$W"
HARNESS="$HOME/Documents/hike/scripts/semantic/harness.c"

insns() { grep -cE '^[ ]*%[a-z0-9]+ = |^[ ]+(ret|br|store|call|load) ' "$1" 2>/dev/null; }
textsz() { size "$1" 2>/dev/null | awk 'NR==2 {print $1}'; }

# Builds and executes an opt'd lift; sets RUN_rc/RUN_out on success,
# returns non-zero on build failure.
run_model() { # ll tag native_out
  local ll="$1" tag="$2" native_out="$3"
  sed -e 's/@main/@hike_main/g' \
      -e 's/@_dl_relocate_static_pie/@_dl_relocate_static_pie_lifted/g' \
      "$ll" > "$W/$tag.renamed.ll" || return 1
  llc -O0 -filetype=obj "$W/$tag.renamed.ll" -o "$W/$tag.o" 2>/dev/null || return 1
  gcc -O0 -no-pie -o "$W/$tag" "$W/$tag.o" "$HARNESS" 2>/dev/null || return 1
  timeout 15 "$W/$tag" > "$W/$tag.out" 2>&1
  RUN_rc=$?
  RUN_out="$W/$tag.out"
  return 0
}

printf "%-20s %-8s %-8s %-9s %s\n" source o0model o2model "i0/i2" native_o2
for b in $(ls "$C0"); do
  [ -x "$C0/$b" ] || continue
  f0="$L0/out_$b.ll"; f2="$L2/out_$b.ll"
  [ -f "$f0" ] && [ -f "$f2" ] || continue
  native_out="$W/$b.native"
  timeout 15 "$C0/$b" > "$native_out" 2>&1; nrc=$?
  cls0="crash"; cls2="crash"; i0="-"; i2="-"
  if [ -f "$f0" ] && opt-21 -O2 -S "$f0" -o "$W/m0.ll" 2>/dev/null \
     && run_model "$W/m0.ll" o0 "$native_out"; then
    i0=$(insns "$W/m0.ll")
    if [ "$RUN_rc" -eq "$nrc" ] && cmp -s "$RUN_out" "$native_out"; then cls0="SAME"
    else cls0="DIFF"; fi
  fi
  if [ -f "$f2" ] && opt-21 -O2 -S "$f2" -o "$W/m2.ll" 2>/dev/null \
     && run_model "$W/m2.ll" o2 "$native_out"; then
    i2=$(insns "$W/m2.ll")
    if [ "$RUN_rc" -eq "$nrc" ] && cmp -s "$RUN_out" "$native_out"; then cls2="SAME"
    else cls2="DIFF"; fi
  fi
  nt=$(textsz "$C2/$b")
  printf "%-20s %-8s %-8s %-9s %s\n" "$b" "$cls0" "$cls2" "$i0/$i2" "$nt"
done
