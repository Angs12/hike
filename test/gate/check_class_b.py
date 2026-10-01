#!/usr/bin/env python3
"""The class-(b) fixture's build-time coverage assertion.

Usage: check_class_b.py <binary>

Fails unless the binary still carries the fixture's class-(b) word:
  1. the probe word 0x10000 sits at table+24 in .rodata (the file
     bytes hold the little-endian pattern),
  2. no relocation names that word (readelf -rW),
  3. the word's value is inside the built .text span, so the old
     initializer rule would have remapped it.
A toolchain or layout change that moves the word out of any of these
conditions fails loudly here instead of the fixture going quietly green.
"""

import re
import struct
import subprocess
import sys

PROBE_VALUE = 0x10000
TABLE_INDEX = 3
WORD = 8


def die(msg):
    print(f"FAIL class_b_word: {msg}")
    sys.exit(1)


def main():
    binary = sys.argv[1]
    # 1. The symbol's word holds the probe value.
    nm = subprocess.run(["nm", binary], capture_output=True, text=True)
    m = re.search(r"([0-9a-f]+) [RrDd] table", nm.stdout)
    if not m:
        die("no `table` symbol (stripped too early?)")
    table_vaddr = int(m.group(1), 16)
    word_vaddr = table_vaddr + TABLE_INDEX * WORD

    secs = {}
    for line in subprocess.run(["readelf", "-SW", binary],
                               capture_output=True, text=True,
                               check=True).stdout.splitlines():
        m = re.match(
            r"\s*\[\s*\d+\]\s+(\S+)\s+\S+\s+([0-9a-f]+)\s+([0-9a-f]+)"
            r"\s+([0-9a-f]+)", line)
        if m:
            name, addr, off, size = m.groups()
            secs[name] = (int(addr, 16), int(off, 16), int(size, 16))
    if ".rodata" not in secs:
        die("no .rodata")
    vaddr, off, size = secs[".rodata"]
    foff = off + (word_vaddr - vaddr)
    with open(binary, "rb") as f:
        f.seek(foff)
        raw = f.read(WORD)
    (value,) = struct.unpack("<Q", raw)
    if value != PROBE_VALUE:
        die(f"the word at table+{TABLE_INDEX * WORD} is {value:#x}, "
            f"expected {PROBE_VALUE:#x}")

    # 2. No relocation names the word.
    rel = subprocess.run(["readelf", "-rW", binary], capture_output=True,
                         text=True, check=True).stdout
    for line in rel.splitlines():
        f = line.split()
        if f and re.fullmatch(r"[0-9a-f]+", f[0]):
            if int(f[0], 16) == word_vaddr:
                die(f"a relocation names the probe word: {line.strip()}")

    # 3. The probe value is inside the built .text span.
    if ".text" not in secs:
        die("no .text")
    taddr, _, tsize = secs[".text"]
    if not (taddr <= PROBE_VALUE <= taddr + tsize):
        die(f".text span [{taddr:#x}, {taddr + tsize:#x}] does not cover "
            f"the probe value {PROBE_VALUE:#x}")
    print(f"PASS class_b_word: word at {word_vaddr:#x} holds {value:#x}, "
          f"unrelocated, inside .text [{taddr:#x}, {taddr + tsize:#x}]")


if __name__ == "__main__":
    main()
