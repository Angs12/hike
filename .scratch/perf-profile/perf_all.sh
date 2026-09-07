#!/usr/bin/env bash
# Perf-profiles the hike lift of every coreutils binary, aggregates
# phases per binary, keeps only small artifacts (phases.txt, flat_top.txt,
# bap.log, out.ll), and emits summary.tsv + phases_rollup.tsv.
# Usage: perf_all.sh <bins_dir> <out_dir>
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
BINS="${1:?bins dir}"; OUT="${2:?out dir}"

mkdir -p "$OUT"
: > "$OUT/summary.tsv"
: > "$OUT/phases_rollup.tsv"   # name phase samples

for b in "$BINS"/*; do
    name="$(basename "$b")"
    [ -f "$b" ] || continue
    d="$OUT/$name"; mkdir -p "$d"
    ll="$d/out_$name.ll"

    t0=$(date +%s.%N)
    perf record -F 1000 --call-graph dwarf -o "$d/perf.data" -- \
        bap "$b" --no-cache --pass=hike-convlir \
        --hike-output-file="$ll" > "$d/bap.log" 2>&1
    rc=$?
    t1=$(date +%s.%N)

    perf script -i "$d/perf.data" > "$d/perf.script" 2>/dev/null
    python3 "$HERE/agg.py" "$d/perf.script" > "$d/phases.txt" 2>/dev/null
    awk -v n="$name" -F'\t' '$1=="PHASE"{print n"\t"$2"\t"$3}' \
        "$d/phases.txt" >> "$OUT/phases_rollup.tsv"

    perf report -i "$d/perf.data" --no-children --stdio 2>/dev/null \
        | grep -E "^ +[0-9]+\.[0-9]+%" | head -15 > "$d/flat_top.txt"

    ns=$(grep -m1 "^samples" "$d/phases.txt" | cut -f2)
    [ -z "$ns" ] && ns=0
    nw=$(grep -c "^hike:" "$d/bap.log" || true)
    llsz=$(stat -c%s "$ll" 2>/dev/null || echo 0)
    awk -v n="$name" -v a="$t0" -v b="$t1" -v r="$rc" -v s="$ns" -v w="$nw" -v z="$llsz" \
        'BEGIN{printf "%s\t%.2f\t%s\t%s\t%s\t%s\n", n, b-a, r, s, w, z}' >> "$OUT/summary.tsv"
    rm -f "$d/perf.data" "$d/perf.script"
    printf '  %s wall=%.1fs rc=%s samples=%s warns=%s ll=%sB\n' "$name" \
        "$(echo "$t1-$t0" | bc)" "$rc" "$ns" "$nw" "$llsz" >&2
done

# global rollup from per-binary PHASE counts
awk -F'\t' '{p[$2]+=$3; t+=$3} END{for (k in p) printf "%s\t%d\t%.1f%%\n", k, p[k], 100*p[k]/t}' \
    "$OUT/phases_rollup.tsv" | sort -t$'\t' -k2,2nr > "$OUT/phases_all.txt"
echo "DONE $(wc -l < "$OUT/summary.tsv") binaries" >&2
