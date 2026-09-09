#!/bin/bash
# Trace OCaml comment depth + paren depth per line, ignoring strings/chars
# (approximation fine for these test files). Reports depth at each line start.
/usr/bin/env python3 - "$@" <<'EOF'
import sys
path = sys.argv[1]
src = open(path).read()
i = 0
n = len(src)
line = 1
depth = 0   # comment depth
paren = 0   # paren depth outside comments
events = []
in_str = False
while i < n:
    c = src[i]
    if c == '\n':
        line += 1
        i += 1
        continue
    if in_str:
        if c == '\\' and i+1 < n:
            i += 2
            continue
        if c == '"':
            in_str = False
        i += 1
        continue
    if depth > 0:
        if src.startswith('(*', i):
            depth += 1; i += 2; continue
        if src.startswith('*)', i):
            depth -= 1; i += 2; continue
        i += 1
        continue
    if src.startswith('(*', i):
        depth += 1; i += 2; continue
    if c == '"':
        in_str = True; i += 1; continue
    if c == '(':
        paren += 1
        events.append((line, 'open', paren))
        i += 1; continue
    if c == ')':
        events.append((line, 'close', paren))
        paren -= 1
        i += 1; continue
    i += 1
print(f"final comment depth: {depth}, final paren depth: {paren}")
# print paren open events where paren goes 0->1 (top-level block starts)
prev = 0
for (ln, kind, p) in events:
    if kind == 'open' and p == 1:
        print(f"line {ln}: top-level ( opens")
EOF
