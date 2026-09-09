#!/bin/bash
# For each value name exported in a cbat_vsa .mli, count references in .ml
# files (any, including the defining one minus its def line) and in OTHER
# .mli files. An export whose only reference is its own .mli line (and its
# own def) is a dead export.
G=/usr/bin/grep
cd /home/tovpr/hike-t2
mli="$1"
dir=$(dirname "$mli")
base=$(basename "$mli" .mli)
# exported names: let <name>, val <name>, and type declarations are skipped here
$G -nE '^(let|val) (rec )?(['"'"']?[a-z_][A-Za-z0-9_'"'"']*)' "$mli" \
 | sed -E 's/^([0-9]+):(let|val) (rec )?(['"'"']?[a-z_][A-Za-z0-9_'"'"']*).*/\1 \4/' \
 | while read -r line name; do
    [ -z "$name" ] && continue
    name=${name//\'/}
    # references in all .ml files, excluding def line in the defining .ml
    ml=$($G -rn --include='*.ml' -w "$name" src test_cbat zz_scratch_probe 2>/dev/null \
      | awk -F: -v d="$dir/$base.ml" -v ln="$line" '$1 !~ /_build/ && !($1==d && $2==ln)' \
      | wc -l)
    # references in other mli files (cross-module use via signatures is rare but count it)
    omli=$($G -rn --include='*.mli' -w "$name" src 2>/dev/null \
      | awk -F: -v d="$mli" -v ln="$line" '$1 !~ /_build/ && $1!=d' | wc -l)
    if [ "$ml" -eq 0 ] && [ "$omli" -eq 0 ]; then
      echo "DEAD-EXPORT $name ($mli:$line)"
    fi
 done
