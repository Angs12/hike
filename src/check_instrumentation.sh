#!/usr/bin/env bash
# check_instrumentation.sh — the build-time blocker for principle #6
# (AGENTS.md: "Debug instrumentation lives in the debug build ONLY",
# restated 2026-09-02: instrumentation is NOT COMPILED INTO the
# production binary).
#
# Usage: check_instrumentation.sh <dir> [<dir>...]
#
# Two rules, both zero-exemption, both COMMENT-AWARE (OCaml comments are
# stripped before matching — doc text that mentions the banned names is
# fine, code that uses them is not):
#
#  1. NO environment reads. [Sys.getenv]/[Sys.getenv_opt] anywhere in
#     production sources is a violation: any runtime-variable behavior is
#     debug, and env-gated instrumentation is precisely what #6 bans.
#     No allowlist — an operator-facing control belongs in a BAP pass
#     parameter (the --hike-output-file mechanism), never an env var.
#
#  2. NO direct output outside the sanctioned channels. The permanent
#     production family (the [hike:] warnings run_corpus.sh greps) goes
#     through [Hike_diag] (src/) or BAP's [Event.Log] (the vendored
#     cbat_vsa library); direct [eprintf]/[print_endline]/[Printf.printf]/
#     [Format.printf] callsites elsewhere are violations. [sprintf]/
#     [asprintf] are fine (string builders, not output). Lines inside a
#     cppo [ #ifdef VSA_DEBUG ] block are skipped — that IS the sanctioned
#     debug mechanism. [hike_diag.ml] is exempt by definition (it IS the
#     channel).
#
# Exits 1 with the offending sites on violation, 0 when clean.

set -u
rc=0

python3 - "$@" <<'PYEOF'
import re, sys, os

dirs = sys.argv[1:] or ["src"]

# --- OCaml comment stripper (handles nesting) -------------------------------
def strip_comments(text):
    out = []
    i, depth, n = 0, 0, len(text)
    while i < n:
        if depth == 0 and text.startswith("(*", i):
            depth = 1; i += 2; out.append(" " * 2)
        elif depth > 0 and text.startswith("(*", i):
            depth += 1; i += 2; out.append(" " * 2)
        elif depth > 0 and text.startswith("*)", i):
            depth -= 1; i += 2; out.append(" " * 2)
        elif depth > 0 and text[i] == '"':
            # string inside comment: irrelevant, skip
            i += 1; out.append(" ")
        else:
            out.append(text[i] if depth == 0 else
                       ("\n" if text[i] == "\n" else " "))
            i += 1
    return "".join(out)

ENV_RE = re.compile(r"Sys\.getenv|getenv_opt|Unix\.getenv")
PRINT_RE = re.compile(r"eprintf|print_endline|Printf\.printf|Format\.printf")
OK_RE = re.compile(r"sprintf|ksprintf|failwith|invalid_arg|Location\.raise_errorf")

files = []
for d in dirs:
    for root, _, names in os.walk(d):
        for name in names:
            if name.endswith(".ml") or name.endswith(".mli"):
                files.append(os.path.join(root, name))

violations = []
for f in sorted(set(files)):
    if f.endswith("hike_diag.ml"):
        continue  # the channel itself
    try:
        lines = open(f, encoding="utf-8").read().split("\n")
    except Exception as e:
        violations.append(f"{f}: READ ERROR {e}")
        continue
    stripped = strip_comments("\n".join(lines)).split("\n")
    indebug = False
    for no, (raw, code) in enumerate(zip(lines, stripped), start=1):
        s = raw.strip()
        if s.startswith("#ifdef VSA_DEBUG"):
            indebug = True; continue
        if s.startswith("#endif"):
            indebug = False; continue
        if indebug:
            continue
        if ENV_RE.search(code):
            violations.append(f"RULE 1 (env read): {f}:{no}: {s}")
        if PRINT_RE.search(code) and not OK_RE.search(code):
            violations.append(f"RULE 2 (direct print): {f}:{no}: {s}")

if violations:
    print("check_instrumentation: VIOLATION(S) — principle #6 "
          "(instrumentation is not compiled into the production binary):",
          file=sys.stderr)
    for v in violations:
        print("  " + v, file=sys.stderr)
    sys.exit(1)
sys.exit(0)
PYEOF

rc=$?
if [ $rc -ne 0 ]; then
  echo "check_instrumentation: fix the sites above: debug output goes behind" >&2
  echo "  #ifdef VSA_DEBUG (cppo), production warnings go through Hike_diag.warn." >&2
fi
exit $rc
