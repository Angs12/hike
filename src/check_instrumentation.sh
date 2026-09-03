#!/usr/bin/env bash
# Build-time blocker: debug instrumentation must not reach production.
# Usage: check_instrumentation.sh <dir> [<dir>...]
# Two zero-exemption, comment-aware rules (OCaml comments strip first):
#   1. No env reads (Sys.getenv etc.): runtime-variable behavior is debug;
#      operator controls belong in BAP pass parameters, never env vars.
#   2. No direct output outside Hike_diag (src/) or Event.Log (cbat_vsa);
#      sprintf/asprintf are fine; lines inside #ifdef VSA_DEBUG skip;
#      hike_diag.ml is exempt (it is the channel).
# Exits 1 with offending sites, 0 when clean.

set -u
rc=0

python3 - "$@" <<'PYEOF'
import re, sys, os

dirs = sys.argv[1:] or ["src"]

# OCaml comment stripper (handles nesting)
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
            # strings inside comments need no handling
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
