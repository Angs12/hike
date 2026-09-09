#!/bin/bash
# T2 dead-binding scan: for each top-level `let <name>` in a given file,
# count references across src/ test_cbat/ zz_scratch_probe/.
# Usage: bash deadscan.sh <file.ml>
# NOTE: _build exclusion is done on the PATH field (awk -F: '$1 !~ /_build/'),
# never on the whole line — lines whose CONTENT contains "_build"
# (e.g. "llvm_builder") would be wrongly dropped.
G=/usr/bin/grep
cd /home/tovpr/hike-t2
f="$1"
$G -nE '^let (['"'"']?[a-z_][A-Za-z0-9_'"'"']*)' "$f" \
  | sed -E 's/^([0-9]+):let (['"'"']?[a-z_][A-Za-z0-9_'"'"']*)[^A-Za-z0-9_'"'"']?.*/\1 \2/' \
  | while read -r line name; do
      [ -z "$name" ] && continue
      name=${name//\'/}
      n=$($G -rn --include='*.ml' --include='*.mli' -w "$name" src test_cbat zz_scratch_probe 2>/dev/null \
        | awk -F: '$1 !~ /_build/' \
        | $G -vE "^[^:]+:${line}:" \
        | $G -c -E "^[0-9]*[^;]")
      echo "$n $name:$line"
    done | sort -n
