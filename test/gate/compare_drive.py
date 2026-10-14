"""Compares one binary's drive emission and diagnostics with the plugin's.

Usage: compare_drive.py <plugin_dir> <drive_dir> <name>

KB object numbers (the %XXXXXXXX block labels) are renamed by first
appearance in each file; any other difference prints and exits 1.
"""
import difflib
import re
import sys
from pathlib import Path

LABEL = re.compile(r"%[0-9a-f]{8}\b")


def normalized(path):
    seen = {}
    return LABEL.sub(lambda m: "%%L%d" % seen.setdefault(m.group(0), len(seen)),
                     path.read_text()).splitlines()


def main():
    plugin, drive, name = Path(sys.argv[1]), Path(sys.argv[2]), sys.argv[3]
    same = True
    for stem in (f"out_{name}.ll", f"err_{name}.txt"):
        a, b = plugin / stem, drive / stem
        if not a.exists() or not b.exists():
            print(f"DIFF {name}: {stem} missing")
            same = False
            continue
        x, y = normalized(a), normalized(b)
        if x != y:
            same = False
            print(f"DIFF {name}: {stem}")
            for line in list(difflib.unified_diff(x, y, "plugin", "drive", n=0, lineterm=""))[:8]:
                print("    " + line)
    return 0 if same else 1


if __name__ == "__main__":
    raise SystemExit(main())
