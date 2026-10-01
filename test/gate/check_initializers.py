#!/usr/bin/env python3
"""The initializer rule's structural check: every word-sized element a
section initializer remaps must be named by a relocation (readelf -r).

Usage: check_initializers.py <emit_dir> <corpus_dir>

Per emitted module with a native counterpart: parse readelf -SW (the
built sections' spans) and readelf -rW (the relocated words), then walk
the word-typed const-array initializers whose global names an ELF
section.  A non-literal element must sit at a relocated address.  The
tiled globals (sec_comp_N / sec_res_N) are counted for conservation but
their addresses are the tiler's, so only the whole-section arrays are
address-checked.
"""

import re
import subprocess
import sys
from pathlib import Path

# The emitter's LLVM global name for a section -> its ELF section name.
SECTIONS = {
    "data": ".data",
    "rodata": ".rodata",
    "got": ".got",
    "gotplt": ".got.plt",
    "datarelro": ".data.rel.ro",
    "text": ".text",
}

WORD = 8


def readelf_sections(binary):
    """ELF section name -> (vaddr, size)."""
    out = subprocess.run(["readelf", "-SW", binary], capture_output=True,
                         text=True, check=True).stdout
    secs = {}
    for m in re.finditer(
            r"\[\s*\d+\]\s+(\S+)\s+\S+\s+([0-9a-f]+)\s+([0-9a-f]+)\s+([0-9a-f]+)",
            out):
        name, addr, off, size = m.groups()
        if size != "0":
            secs[name] = (int(addr, 16), int(size, 16))
    return secs


def readelf_relocs(binary):
    """(set of relocated offsets, dict RELATIVE offset -> addend)."""
    out = subprocess.run(["readelf", "-rW", binary], capture_output=True,
                         text=True, check=True).stdout
    sites = set()
    relative = {}
    for line in out.splitlines():
        f = line.split()
        if len(f) < 3 or not re.fullmatch(r"[0-9a-f]+", f[0]):
            continue
        off = int(f[0], 16)
        sites.add(off)
        if len(f) >= 4 and f[2] == "R_X86_64_RELATIVE":
            relative[off] = int(f[3], 16)
    return sites, relative


# One const-array initializer: @name = [constant|global] [N x iT] [...].
ARRAY_RE = re.compile(
    r"^@([\w.]+) = (?:constant|global) \[(\d+) x (i\d+)\] \[", re.M)

def initializer_elements(ll_text, start):
    """The top-level comma-separated elements of the array whose opening
    bracket just ended at `start` (depth begins inside the array)."""
    depth = 1
    parens = 0
    elems = []
    cur = []
    i = start
    while i < len(ll_text):
        c = ll_text[i]
        if c == "[":
            depth += 1
            cur.append(c)
        elif c == "]":
            depth -= 1
            if depth == 0:
                elems.append("".join(cur).strip())
                return elems, i
            cur.append(c)
        elif c == "(":
            parens += 1
            cur.append(c)
        elif c == ")":
            parens -= 1
            cur.append(c)
        elif c == "," and depth == 1 and parens == 0:
            elems.append("".join(cur).strip())
            cur = []
        else:
            cur.append(c)
        i += 1
    raise ValueError("unterminated initializer")


LITERAL_RE = re.compile(r"^i\d+\s+-?(0x[0-9a-f]+|\d+)\s*$")


def check_module(ll_path, binary):
    """Returns (remapped_total, violations, tiled_remaps)."""
    ll_text = ll_path.read_text()
    secs = readelf_sections(binary)
    sites, _ = readelf_relocs(binary)
    remapped = 0
    violations = []
    tiled = 0
    for m in ARRAY_RE.finditer(ll_text):
        gname, n, ty = m.groups()
        if ty != "i64":
            continue
        elems, _ = initializer_elements(ll_text, m.end())
        assert len(elems) == int(n), f"{ll_path.name}: {gname}"
        if gname in SECTIONS and SECTIONS[gname] in secs:
            vaddr, size = secs[SECTIONS[gname]]
            for i, e in enumerate(elems):
                if LITERAL_RE.match(e):
                    continue
                remapped += 1
                addr = vaddr + i * WORD
                if addr not in sites:
                    violations.append((gname, i, hex(addr), e[:60]))
        elif re.fullmatch(r"sec_(comp|res)_\d+", gname):
            tiled += sum(1 for e in elems if not LITERAL_RE.match(e))
    return remapped, violations, tiled


def main():
    emit, corpus = Path(sys.argv[1]), Path(sys.argv[2])
    total_remapped = total_violations = total_tiled = 0
    for ll in sorted(emit.glob("out_*.ll")):
        name = ll.name[4:-3]
        native = corpus / name
        if not native.exists():
            continue
        remapped, violations, tiled = check_module(ll, native)
        total_remapped += remapped
        total_tiled += tiled
        for gname, idx, addr, elem in violations:
            print(f"FAIL {name}: @{gname}[{idx}] at {addr} is remapped "
                  f"but no relocation names it: {elem}")
        total_violations += len(violations)
    print(f"check_initializers: {total_remapped} remapped word(s), "
          f"{total_violations} violation(s), {total_tiled} tiled remap(s)")
    return 1 if total_violations else 0


if __name__ == "__main__":
    sys.exit(main())
