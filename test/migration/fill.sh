#!/usr/bin/env bash
# Emit migration-inventory rows for one old-source -> new-target pair.
#
#   fill.sh <old-source.ml> <new-target.ml> <prefix>
#
# Old check sites and new pins are matched positionally (the migration rule
# required one pin per check site in source order).  The script reports a
# mismatch rather than guessing; a mismatch is reviewed by hand.
set -u

SRC="$1"; TGT="$2"; PFX="$3"

old_labels() {
  grep -nE '\bcheck(_bound)?[[:space:]]+"' "$SRC" \
    | sed -E 's#^([0-9]+):.*check(_bound)?[[:space:]]+"([^"]*)".*#\1\t\3#'
}

new_ids() {
  grep -nE "pin[[:space:]]+\"$PFX-" "$TGT" \
    | sed -E "s#^([0-9]+):.*pin[[:space:]]+\"($PFX-[0-9]+)\".*#\1\t\2#"
}

mapfile -t OLD < <(old_labels)
mapfile -t NEW < <(new_ids)

rc=0
if [ "${#OLD[@]}" -ne "${#NEW[@]}" ]; then
  printf 'MISMATCH %s -> %s: %d old sites, %d pins\n' "$SRC" "$TGT" "${#OLD[@]}" "${#NEW[@]}" >&2
  rc=1
fi

n=${#OLD[@]}
[ "${#NEW[@]}" -lt "$n" ] && n=${#NEW[@]}
for ((i = 0; i < n; i++)); do
  ol="${OLD[$i]#*$'\t'}"; nl="${NEW[$i]#*$'\t'}"
  printf '| %s | %s | CARRIED | %s |\n' "${SRC}:$i" "$ol" "$nl"
done

exit "$rc"
