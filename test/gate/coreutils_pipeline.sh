#!/usr/bin/env bash
# End-to-end coreutils pipeline: clone -> build -> collect ELFs -> lift ->
# recompile -> native-vs-lifted success-rate table.
# Resumable: each stage skips existing work (delete $WORK/ir to re-emit).
# Usage: coreutils_pipeline.sh [workdir] [stage]
#   stage: all|clone|build|collect|lift|link|suite|summary (default all)
#   workdir default /tmp/opencode/coreutils-test
# Needs a fresh plugin, plus git, autoconf/automake, make, bap, llc, gcc.
set -u

HERE="$(cd "$(dirname "$0")" && pwd)"
. "$HERE/lib.sh"
SEM="$HERE/semantic"
REPO_ROOT="$(cd "$HERE/../.." && pwd)"

WORK="${1:-/tmp/opencode/coreutils-test}"
STAGE="${2:-all}"
JOBS="${JOBS:-$(nproc 2>/dev/null || echo 4)}"
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
CFLAGS_BUILD="${CFLAGS_BUILD:--O0 -fno-stack-protector}"

build_configure_make() {   # $1 = source dir
    local src="$1"
    note "build: configure CFLAGS='$CFLAGS_BUILD' (PIE only, no fallback)"
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
    if [ -z "$(ls -A "$BINS" 2>/dev/null)" ]; then do_collect || return 1; fi
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
        : > "$LIFT_LOG"
        local name
        for name in "${pending[@]}"; do
            "$HERE/lift_one.sh" "$name" "$BINS" "$IR" "$OUT" "$TIMES" "$LIFT_LOG"
        done
        ok=$((ok + $(grep -c '^OK' "$LIFT_LOG")))
    fi
    note "lift: $ok/$total emitted OK (details: $LIFT_LOG; timings: $TIMES)"
    [ "$ok" -eq "$total" ]
}

# Aggregates the timings TSV: total, mean, p50/p90, top-10.
do_lift_report() {
    local tsv="$WORK/lift_times.tsv"
    [ -s "$tsv" ] || { note "lift-report: no timings ($tsv) - run RETIME=1 ... lift"; return 0; }
    if ! command -v gawk >/dev/null 2>&1; then
        note "lift-report: the percentile awk needs gawk; report skipped"
        return 0
    fi
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
do_link() {
    : > "$TEST_LOG"
    local ok=0 fail=0
    for ll in "$IR"/out_*.ll; do
        [ -e "$ll" ] || { note "link: no IR found under $IR"; return 1; }
        local name; name="$(basename "$ll")"; name="${name#out_}"; name="${name%.ll}"

        local GMP="" CRYPTO=""
        # gnulib/GMP users need -lgmp, like the native link
        grep -q '@__gmp' "$ll" && GMP="-lgmp"
        # gnulib hashing can route through libcrypto
        grep -qE '@(MD5_|SHA1_|SHA224_|SHA256_|SHA384_|SHA512_|EVP_)' "$ll" \
          && CRYPTO="-lcrypto"
        # The lifted code is memory-heavy; at -O0 it runs far slower than
        # the native originals the suite was timed against.  LLC_OPT=-O2
        # both lets the suite finish and exercises the optimized module.
        hike_llc "$ll" "$OUT/${name}_lifted.o" "${LLC_OPT:--O0}" -relocation-model=pic 2>>"$OUT/$name.llc.log" \
          || { echo "FAIL $name (llc)" >> "$TEST_LOG"; fail=$((fail+1)); continue; }
        if ! gcc -O0 -pie -o "$OUT/${name}_lifted" "$OUT/${name}_lifted.o" \
                 $GMP $CRYPTO 2>>"$OUT/$name.gcc.log"; then
            echo "FAIL $name (link)" >> "$TEST_LOG"; fail=$((fail+1)); continue
        fi
        rm -f "$OUT/${name}_lifted.o"
        command -v strip >/dev/null && strip "$OUT/${name}_lifted" 2>/dev/null
        mkdir -p "$OUT/run/both"
        cp -f "$OUT/${name}_lifted" "$OUT/run/both/$name"
        echo "OK $name" >> "$TEST_LOG"; ok=$((ok+1))
    done
    note "link: OK=$ok FAIL=$fail (details: $TEST_LOG)"
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
        # binaries before the real tests run.  The Makefile reaches help2man
        # through the `run_help2man' variable, not HELP2MAN, so the variable
        # is the one that must be overridden -- coreutils ships `dummy-man'
        # (it copies the distributed pages without running the binary).
        note "suite[$1]: make -k check (doc tools stubbed; this takes a while)"
        (cd "$CORE" && timeout 5400 make -k check V=0 \
            run_help2man="sh $CORE/man/dummy-man" \
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

    # ---- clean the test state ----
    # A killed run leaves tests/*.log behind, and make then reuses them: the
    # re-run "finishes" in seconds reporting FAIL 0 from stale results.
    find "$CORE/tests" -name '*.log' -delete 2>/dev/null || true
    find "$CORE" -name 'test-suite.log' -delete 2>/dev/null || true

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
    local lifts
    lifts=$(grep -c '^OK' "$LIFT_LOG" 2>/dev/null) || true
    lifts=${lifts:-0}
    if [ "$lifts" -eq 0 ]; then
        # A resumed run's log may hold only the new lifts; the emitted
        # IR is the ground truth.
        lifts=$(ls "$IR"/out_*.ll 2>/dev/null | wc -l)
    fi
    local total; total=$(ls "$BINS" 2>/dev/null | wc -l)
    local relinked
    relinked=$(grep -c '^OK' "$TEST_LOG" 2>/dev/null) || true
    relinked=${relinked:-0}
    echo "==================== COREUTILS SUCCESS RATE ===================="
    echo "binaries collected : $total"
    echo "hike-lifted OK     : $lifts / $total"
    echo "recompiled (link)  : $relinked"
    local slog="$WORK/suite"
    if [ -s "$slog/native.test-suite.log" ] && [ -s "$slog/lifted.test-suite.log" ]; then
        echo "--- the upstream suite (make check): native vs lifted ---"
        grep -E '^# (TOTAL|PASS|FAIL|SKIP|ERROR|XFAIL|XPASS):' \
            "$slog/native.test-suite.log" | tr -s ' ' | sed 's/^/native /'
        grep -E '^# (TOTAL|PASS|FAIL|SKIP|ERROR|XFAIL|XPASS):' \
            "$slog/lifted.test-suite.log" | tr -s ' ' | sed 's/^/lifted /'
        echo "--- new lifted failures (in lifted, not in native) ---"
        comm -13 <(grep '^FAIL: ' "$slog/native.test-suite.log" | sort -u) \
                 <(grep '^FAIL: ' "$slog/lifted.test-suite.log" | sort -u) | head -40
    else
        echo "suite: not run yet (stage: suite)"
    fi
    echo "================================================================"
}

case "$STAGE" in
    clone)   do_clone ;;
    build)   do_build ;;
    collect) do_collect ;;
    lift)    do_lift ;;
    lift-report) do_lift_report ;;
    link)    do_link ;;
    suite)   do_suite ;;
    summary) do_summary ;;
    all)
        do_collect || exit 1
        do_lift     # failures recorded, not fatal - the report shows them
        do_link
        do_suite    # the upstream suite IS the semantic oracle
        do_summary
        do_lift_report
        ;;
    *) echo "unknown stage '$STAGE'" >&2; exit 2 ;;
esac
