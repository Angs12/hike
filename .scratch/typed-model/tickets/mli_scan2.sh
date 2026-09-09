#!/bin/bash
# Over-exposure scan: for each name exported in an .mli, count references
# in .ml files OUTSIDE the defining module. Zero -> the export is unneeded
# (the value may still be alive internally; remove only the export line).
G=/usr/bin/grep
cd /home/tovpr/hike-t2
mli="$1"
base=$(basename "$mli" .mli)
dir=$(dirname "$mli")
def="$dir/$base.ml"
$G -nE '^(let|val) (rec )?(['"'"']?[a-z_][A-Za-z0-9_'"'"']*)' "$mli" \
 | sed -E 's/^([0-9]+):(let|val) (rec )?(['"'"']?[a-z_][A-Za-z0-9_'"'"']*).*/\1 \4/' \
 | while read -r line name; do
    [ -z "$name" ] && continue
    name=${name//\'/}
    ext=$($G -rn --include='*.ml' -w "$name" src test_cbat zz_scratch_probe 2>/dev/null \
      | awk -F: -v d="$def" '$1 !~ /_build/ && $1!=d' | wc -l)
    if [ "$ext" -eq 0 ]; then
      int=$($G -n -w "$name" "$def" 2>/dev/null | /usr/bin/grep -cvE "^[0-9]+:\s*;")
      echo "OVER-EXPOSED $name ($mli:$line) internal-refs=$int"
    fi
 done
