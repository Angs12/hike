#!/usr/bin/env bash
# End-to-end coreutils pipeline: clone -> build -> collect ELFs -> lift ->
# recompile -> native-vs-lifted success-rate table.
# Resumable: each stage skips existing work (delete $WORK/ir to re-emit).
# Usage: coreutils_pipeline.sh [workdir] [stage]
#   stage: all|clone|build|collect|lift|test|summary (default all)
#   workdir default /tmp/opencode/coreutils-test
# Needs a fresh plugin, plus git, autoconf/automake, make, bap, llc, gcc.
set -u

HERE="$(cd "$(dirname "$0")" && pwd)"
SEM="$HERE/semantic"
REPO_ROOT="$(cd "$HERE/.." && pwd)"

WORK="${1:-/tmp/opencode/coreutils-test}"
STAGE="${2:-all}"
JOBS="$(nproc 2>/dev/null || echo 4)"
URL="https://github.com/coreutils/coreutils"
CORE="$WORK/coreutils"
BINS="$WORK/binaries"
IR="$WORK/ir"
OUT="$WORK/out"
LIFT_LOG="$WORK/lift.log"
TEST_LOG="$WORK/test.log"

mkdir -p "$WORK" "$BINS" "$IR" "$OUT"

note() { printf '[cu-pipe] %s\n' "$*"; }

# ---------------------------------------------------------------- clone ----
do_clone() {
    if [ -d "$CORE/.git" ]; then note "clone: SKIP (already cloned -> $CORE)"; return 0; fi
    note "clone: $URL (shallow)"
    git clone --depth=1 "$URL" "$CORE" || return 1
}

# ---------------------------------------------------------------- build ----
# Release tarball ships pre-generated ./configure, so it builds without
# bootstrap tools; used when the git-checkout bootstrap fails.
TARBALL_URL="https://ftp.gnu.org/gnu/coreutils/coreutils-9.5.tar.xz"

# Plain gcc defaults = PIE executables.
CFLAGS_BUILD="-O0 -fno-stack-protector"

build_configure_make() {   # $1 = source dir
    local src="$1"
    note "build: configure CFLAGS='-O0 $CFLAGS_BUILD' (PIE only, no fallback)"
    (cd "$src" \
     && CFLAGS="$CFLAGS_BUILD" LDFLAGS="" \
        ./configure --disable-gcc-warnings >> "$WORK/configure.log" 2>&1) || {
        note "build: CONFIGURE FAILED (see $WORK/configure.log)"; return 1; }
    note "build: make -k -j$JOBS (the slow part; -k skips unbuildable extras)"
    local rc=0
    (cd "$src" && make -k -j"$JOBS" >> "$WORK/make.log" 2>&1) || rc=$?
    local n; n=$(find "$src/src" -maxdepth 1 -type f -executable 2>/dev/null | wc -l)
    if [ "$n" -lt 40 ]; then
        note "build: MAKE produced too few binaries ($n) - see $WORK/make.log"; return 1
    fi
    if [ "$rc" -ne 0 ]; then
        note "build: make exited nonzero but $n executables built - continuing without them"
    fi
    return 0
}

do_build() {
    if [ -x "$CORE/src/ls" ] && [ -x "$CORE/src/cat" ]; then
        note "build: SKIP (already built -> $CORE/src)"; return 0; fi

    # primary path: GitHub checkout via gnulib bootstrap
    if [ -d "$CORE/.git" ] || do_clone; then
        note "build: trying ./bootstrap (fetches gnulib; one-time)"
        if (cd "$CORE" && ./bootstrap --copy) >> "$WORK/bootstrap.log" 2>&1; then
            build_configure_make "$CORE" && return 0
        else
            note "build: bootstrap failed (missing gperf/texinfo?) - falling back to the release tarball (pre-generated configure, no bootstrap tools needed); see $WORK/bootstrap.log"
        fi
    fi

    # fallback path: release tarball
    local tb="$WORK/coreutils-9.5.tar.xz"
    if [ ! -d "$WORK/coreutils-9.5" ]; then
        note "build: downloading $TARBALL_URL"
        curl -fL --retry 3 -o "$tb" "$TARBALL_URL" >> "$WORK/download.log" 2>&1 || {
            note "build: DOWNLOAD FAILED (see $WORK/download.log)"; return 1; }
        tar -C "$WORK" -xf "$tb" || return 1
    fi
    rm -rf "$CORE"
    mv "$WORK/coreutils-9.5" "$CORE"
    build_configure_make "$CORE"
}

# -------------------------------------------------------------- collect ----
do_collect() {
    do_build || return 1
    local existing; existing=$(ls -A "$BINS" 2>/dev/null | wc -l)
    if [ "$existing" -gt 0 ]; then
        note "collect: SKIP ($existing binaries already in $BINS)"; return 0
    fi
    note "collect: copying x86-64 ELF executables from $CORE/src"
    local n=0
    while IFS= read -r f; do
        local base; base="$(basename "$f")"
        file -b "$f" | grep -q 'ELF 64-bit.*executable' || continue
        case "$base" in *.so|*.so.*) continue ;; esac
        cp -f "$f" "$BINS/$base"; n=$((n+1))
    done < <(find "$CORE/src" -maxdepth 1 -type f)
    note "collect: $n binaries -> $BINS"
}

# ----------------------------------------------------------------- lift ----
# Lift wall-seconds land in $WORK/lift_times.tsv; RETIME=1 re-emits
# already-lifted binaries purely to time them.
do_lift() {
    # 64MB minor heap: fixpoint churn otherwise spends ~11% in major GC.
    export OCAMLRUNPARAM="${OCAMLRUNPARAM:-s=8M}"
    [ -d "$BINS" ] && [ "$(ls -A "$BINS" 2>/dev/null)" ] || { do_collect; } || return 1
    : > "$LIFT_LOG"
    local TIMES="$WORK/lift_times.tsv"
    [ "${RETIME:-0}" = "1" ] && : > "$TIMES"
    touch "$TIMES"
    local total=0 ok=0
    # Serial only: parallel lifts OOM the box (one big lift peaks ~1 GB).
    [ -d "$IR" ] || mkdir -p "$IR"
    local pending=()
    for b in "$BINS"/*; do
        local name; name="$(basename "$b")"
        local ll="$IR/out_$name.ll"
        total=$((total+1))
        if [ -s "$ll" ] && [ "${RETIME:-0}" != "1" ]; then
            ok=$((ok+1)); continue   # resume support (untimed)
        fi
        pending+=("$name")
    done
    note "lift: $ok/$total already emitted; lifting ${#pending[@]} remaining SERIALLY (one at a time — parallel lifts OOM)"
    if [ "${#pending[@]}" -gt 0 ]; then
        local name
        for name in "${pending[@]}"; do
            "$HERE/lift_one.sh" "$name" "$BINS" "$IR" "$OUT" "$TIMES" "$LIFT_LOG"
        done
        ok=$(( $(grep -c '^OK' "$LIFT_LOG") ))
    fi
    note "lift: $ok/$total emitted OK (details: $LIFT_LOG; timings: $TIMES)"
    [ "$ok" -eq "$total" ]
}

# Aggregates the timings TSV: total, mean, p50/p90, top-10.
do_lift_report() {
    local tsv="$WORK/lift_times.tsv"
    [ -s "$tsv" ] || { note "lift-report: no timings ($tsv) - run RETIME=1 ... lift"; return 0; }
    awk -F'\t' '{n++; s+=$2; a[n]=$2}
        END{
          asort(a);
          printf "binaries timed : %d\n", n;
          printf "total lift     : %.1f s\n", s;
          printf "mean / median  : %.2f s / %.2f s\n", s/n, a[int((n+1)/2)];
          printf "p90 / max      : %.2f s / %.2f s\n", a[int(n*0.9)], a[n];
        }' "$tsv"
      echo '---- slowest 10 ----'
      sort -t "$(printf '\t')" -k2,2nr "$tsv" | head -10 \
        | awk -F'\t' '{printf "  %6.2fs  %s\n", $2, $1}'
}

# ----------------------------------------------------------------- test ----
do_test() {
    : > "$TEST_LOG"
    local pass=0 fail=0 skip=0
    for ll in "$IR"/out_*.ll; do
        [ -e "$ll" ] || { note "test: no IR found under $IR"; return 1; }
        local name; name="$(basename "$ll")"; name="${name#out_}"; name="${name%.ll}"
        local native="$BINS/$name"
        [ -x "$native" ] || { echo "SKIP $name (no native)" >> "$TEST_LOG"; skip=$((skip+1)); continue; }

        sed -e 's/@main/@hike_main/g' \
            -e 's/@_dl_relocate_static_pie/@_dl_relocate_static_pie_lifted/g' \
            "$ll" > "$OUT/${name}_lifted.ll" 2>/dev/null \
          || { echo "FAIL $name (rename)" >> "$TEST_LOG"; fail=$((fail+1)); continue; }
        llc -O0 -filetype=obj "$OUT/${name}_lifted.ll" -o "$OUT/${name}_lifted.o" 2>>"$OUT/$name.llc.log" \
          || { echo "FAIL $name (llc)" >> "$TEST_LOG"; fail=$((fail+1)); continue; }

        local STUB="" GMP="" CRYPTO=""
        grep -q '@_setjmp\|@longjmp' "$ll" && STUB="$SEM/setjmp_stub.S"
        # gnulib/GMP users need -lgmp, like the native link
        grep -q '@__gmp' "$ll" && GMP="-lgmp"
        # gnulib hashing can route through libcrypto
        grep -qE '@(MD5_|SHA1_|SHA224_|SHA256_|SHA384_|SHA512_|EVP_)' "$ll" \
          && CRYPTO="-lcrypto"
        # --allow-multiple-definition: gnulib modules defining their own
        # malloc/free must not collide with the harness wrappers
        if ! gcc -O0 -no-pie -o "$OUT/${name}_lifted" \
                 -Wl,--allow-multiple-definition \
                 "$OUT/${name}_lifted.o" "$SEM/harness.c" $STUB $GMP $CRYPTO 2>>"$OUT/$name.gcc.log"; then
            echo "FAIL $name (link)" >> "$TEST_LOG"; fail=$((fail+1)); continue
        fi
        rm -f "$OUT/${name}_lifted.o"
        command -v strip >/dev/null && strip "$OUT/${name}_lifted" 2>/dev/null

        # Cap captures: yes-class utilities write forever.
        # Truncate only shrinks: -s 1M on a smaller file would NUL-pad it.
        caprun() { local o="$1" d="$2" n="$3"; local r=0
                   (cd "$d" && timeout 20 "./$n" > "$o.tmp" 2>&1); r=$?
                   local sz; sz=$(stat -c%s "$o.tmp" 2>/dev/null || echo 0)
                   [ "$sz" -gt 1048576 ] && truncate -s 1M "$o.tmp" 2>/dev/null
                   mv "$o.tmp" "$o"; return $r; }

        # Normalize nondeterministic tokens before diffing (raw captures stay).
        # mktemp suffixes are per-run random; dd elapsed/rate legitimately
        # differ per run (the rate UNIT stays visible, so a real unit bug
        # still fails).
        norm() { sed -E \
                   -e 's/tmp\.[A-Za-z0-9]{6,}/tmp.RANDOM/g' \
                   -e 's/(, )[0-9][0-9.eE+-]*( s, )[0-9][0-9.]*( [A-Za-z]*B\/s)$/\1ELAPSED\2RATE\3/' \
                   "$1" 2>/dev/null; }

        mkdir -p "$OUT/run/both"
        # One shared dir keeps argv[0] and PWD identical on both sides.

        cp -f "$native" "$OUT/run/both/$name"
        caprun "$OUT/${name}_native.stdout" "$OUT/run/both" "$name"; local nrc=$?
        cp -f "$OUT/${name}_lifted" "$OUT/run/both/$name"
        caprun "$OUT/${name}_lifted.stdout" "$OUT/run/both" "$name"; local lrc=$?

        if [ "$nrc" -eq "$lrc" ] \
           && diff -q <(norm "$OUT/${name}_native.stdout") \
                      <(norm "$OUT/${name}_lifted.stdout") >/dev/null 2>&1; then
            echo "PASS $name" >> "$TEST_LOG"; pass=$((pass+1))
        else
            echo "FAIL $name (rc $nrc vs $lrc)" >> "$TEST_LOG"; fail=$((fail+1))
        fi
    done
    note "test: PASS=$pass FAIL=$fail SKIP=$skip (details: $TEST_LOG)"
}

# Coreutils' own suite (make check), three-way: native baseline, lifted,
# and the delta (lifted-minus-native failures = hike-caused breakage).
# Usage: coreutils_pipeline.sh <work> suite (SUITE_FRESH=1 redoes baseline).
do_suite() {
    [ -x "$CORE/src/ls" ] || { note "suite: build first"; return 1; }
    local suite_log="$WORK/suite"
    mkdir -p "$suite_log"

    run_check() { # $1 = tag for log names
        # Stub doc tools: regenerating man/info would execute the swapped-in
        # binaries before the real tests run.
        note "suite[$1]: make -k check (doc tools stubbed; this takes a while)"
        (cd "$CORE" && timeout 5400 make -k check V=0 \
            HELP2MAN=true MAKEINFO=true TEXI2PDF=true TEXI2DVI=true) \
            > "$suite_log/$1.check.out" 2>&1
        local log
        log=$(find "$CORE" -name test-suite.log -newer "$suite_log/.stamp.$$" 2>/dev/null | head -1)
        [ -z "$log" ] && log=$(find "$CORE" -name test-suite.log | head -1)
        cp -f "$log" "$suite_log/$1.test-suite.log" 2>/dev/null || {
            note "suite[$1]: no test-suite.log produced"; return 1; }
        # Guard: the log must hold real shell tests, not gnulib-only coverage.
        local own
        own=$(grep -cE '^([A-Z]+): .*(tests/|/[a-z0-9_-]+\.sh)' "$suite_log/$1.test-suite.log")
        note "suite[$1]: coreutils-shell-test results in log: $own"
        if [ "$own" -lt 50 ]; then
            note "suite[$1]: WARNING - looks like gnulib-only coverage; NOT a valid comparison"
        fi
        grep -E '^# (TOTAL|PASS|FAIL|SKIP|ERROR|XFAIL|XPASS):' \
            "$suite_log/$1.test-suite.log" | tr -s ' '
    }

    # ---- baseline (cached unless SUITE_FRESH=1) ----
    if [ "${SUITE_FRESH:-0}" = "1" ] || [ ! -s "$suite_log/native.test-suite.log" ]; then
        touch "$suite_log/.stamp.$$"
        echo "== native baseline ==" > "$suite_log/native.counts"
        run_check native >> "$suite_log/native.counts" 2>&1 || true
        rm -f "$suite_log/.stamp.$$"
    fi

    # ---- swap in the lifted binaries ----
    local swapped=0
    mkdir -p "$suite_log/src_orig"
    for ll in "$IR"/out_*.ll; do
        [ -e "$ll" ] || continue
        local name; name="$(basename "$ll")"; name="${name#out_}"; name="${name%.ll}"
        [ -x "$CORE/src/$name" ] || continue
        [ -f "$suite_log/src_orig/$name" ] \
            || cp -f "$CORE/src/$name" "$suite_log/src_orig/$name"
        if [ -x "$OUT/run/both/$name" ]; then
            cp -f "$OUT/run/both/$name" "$CORE/src/$name"
            swapped=$((swapped+1))
        fi
    done
    note "suite: swapped $swapped lifted binaries into $CORE/src"

    # ---- lifted run ----
    touch "$suite_log/.stamp.$$"
    echo "== lifted ==" > "$suite_log/lifted.counts"
    run_check lifted >> "$suite_log/lifted.counts" 2>&1 || true

    # ---- restore ----
    for f in "$suite_log/src_orig"/*; do
        [ -e "$f" ] || continue
        cp -f "$f" "$CORE/src/$(basename "$f")"
    done
    note "suite: original binaries restored"

    # ---- delta ----
    echo "==================== SUITE COMPARISON ===================="
    paste <(grep -E '^# ' "$suite_log/native.counts") \
          <(grep -E '^# ' "$suite_log/lifted.counts") 2>/dev/null \
      | awk '{printf "%-12s native=%-6s lifted=%-6s\n", $1" "$2, $3, $6}'
    echo "(delta FAIL+ERROR lifted-minus-native = the hike-caused breakage)"
    echo "logs: $suite_log/{native,lifted}.test-suite.log"
}

# -------------------------------------------------------------- summary ----
do_summary() {
    local lifts tests p f s
    lifts=$(grep -c '^OK' "$LIFT_LOG" 2>/dev/null || echo 0)
    local total; total=$(ls "$BINS" 2>/dev/null | wc -l)
    p=$(grep -c '^PASS' "$TEST_LOG" 2>/dev/null || echo 0)
    f=$(grep -c '^FAIL' "$TEST_LOG" 2>/dev/null || echo 0)
    s=$(grep -c '^SKIP' "$TEST_LOG" 2>/dev/null || echo 0)
    tests=$((p+f))
    echo "==================== COREUTILS SUCCESS RATE ===================="
    echo "binaries collected : $total"
    echo "hike-lifted OK     : $lifts / $total"
    echo "recompiled+tested  : $tests (skipped $s)"
    echo "semantic PASS      : $p"
    echo "semantic FAIL      : $f"
    if [ "$total" -gt 0 ]; then
        awk -v p="$p" -v t="$total" 'BEGIN { printf "SUCCESS RATE       : %d/%d = %.1f%%\n", p, t, 100*p/t }'
    fi
    echo "================================================================"
    echo "failures:"; grep '^FAIL' "$TEST_LOG" 2>/dev/null | head -40
}

case "$STAGE" in
    clone)   do_clone ;;
    build)   do_build ;;
    collect) do_collect ;;
    lift)    do_lift ;;
    lift-report) do_lift_report ;;
    test)    do_test ;;
    suite)   do_suite ;;
    summary) do_summary ;;
    all)
        do_collect || exit 1
        do_lift     # failures recorded, not fatal - the report shows them
        do_test
        do_summary
        do_lift_report
        ;;
    *) echo "unknown stage '$STAGE'" >&2; exit 2 ;;
esac
