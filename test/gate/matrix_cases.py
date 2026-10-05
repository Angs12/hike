#!/usr/bin/env python3
"""Native configurations shared by correctness and performance matrix gates."""
import argparse


def cells(stage=None):
    for stripped in (False, True):
        if stage not in (None, "strip" if stripped else "opts"):
            continue
        for level in ("O0", "O1", "O2", "O3", "Os", "Oz"):
            yield f"gcc-{level}-nosp-{'strip' if stripped else 'nostrip'}", "gcc", level, False, stripped
    for compiler, protected in (("clang", False), ("gcc", True)):
        for level in ("O0", "O2"):
            for stripped in ((False, True) if protected else (False,)):
                owner = ("protector-strip" if stripped else "protector") if protected else "compilers"
                if stage not in (None, owner):
                    continue
                mode = "fstackprotectorall" if protected else "compilers-nosp"
                yield f"{compiler}-{level}-{mode}-{'strip' if stripped else 'nostrip'}", compiler, level, protected, stripped


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("stage", choices=["opts", "strip", "compilers", "protector", "protector-strip"])
    args = parser.parse_args()
    for tag, compiler, level, protected, stripped in cells(args.stage):
        print("\t".join([tag, compiler, f"-{level}",
                         "-fstack-protector-all" if protected else "-fno-stack-protector",
                         "strip" if stripped else "nostrip"]))
