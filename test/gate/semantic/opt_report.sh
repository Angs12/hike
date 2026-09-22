#!/usr/bin/env bash
# The typed-frame prototype's opt report: for each binary, compare the
# offset model vs the typed model — pre/post opt-21 -O2 instruction,
# alloca, and inttoptr/ptrtoint counts.  Usage: opt_report.sh <bin>...
set -u
CUR=/tmp/emit_l1_o0
TYP=/tmp/typed_proto
printf "%-16s %8s %8s %8s %8s\n" binary/model "insns" "alloca" "i2p/pt" "post-i"
for b in "$@"; do
  for m in cur typ; do
    f="$([ "$m" = cur ] && echo "$CUR" || echo "$TYP")/out_$b.ll"
    [ -f "$f" ] || continue
    opt-21 -O2 -S "$f" -o /tmp/opt_rep.ll 2>/dev/null
    pre_i=$(grep -cE '^[ ]*%[a-z0-9]+ = |^[ ]+(ret|br|store|call|load) ' "$f")
    pre_a=$(grep -c alloca "$f")
    pre_p=$(grep -c 'inttoptr\|ptrtoint' "$f")
    post_i=$(grep -cE '^[ ]*%[a-z0-9]+ = |^[ ]+(ret|br|store|call|load) ' /tmp/opt_rep.ll)
    post_a=$(grep -c alloca /tmp/opt_rep.ll)
    post_p=$(grep -c 'inttoptr\|ptrtoint' /tmp/opt_rep.ll)
    printf "%-16s %8s %8s %8s   post-opt: %s insns, %s alloca, %s i2p/pt\n" \
      "$b/$m" "$pre_i" "$pre_a" "$pre_p" "$post_i" "$post_a" "$post_p"
  done
done
