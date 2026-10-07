#!/usr/bin/env python3
"""Native configurations shared by correctness and performance matrix gates."""
import argparse


LEVELS = ("O0", "O1", "O2", "O3", "Os", "Oz")
MODELS = ("local-exec", "initial-exec", "global-dynamic", "local-dynamic")


def cells(stage=None):
    for compiler in ("gcc", "clang"):
        for level in LEVELS:
            for protected in (False, True):
                for stripped in (False, True):
                    if protected:
                        owner = "protector-strip" if stripped else "protector"
                    elif stripped:
                        owner = "strip"
                    else:
                        owner = "opts" if compiler == "gcc" else "compilers"
                    if stage not in (None, owner, "tls"):
                        continue
                    mode = "fstackprotectorall" if protected else "nosp"
                    yield f"{compiler}-{level}-{mode}-{'strip' if stripped else 'nostrip'}", compiler, level, protected, stripped


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("stage", choices=["opts", "strip", "compilers", "protector", "protector-strip", "tls", "tls-models"])
    args = parser.parse_args()
    configurations = cells("tls" if args.stage == "tls-models" else args.stage)
    for tag, compiler, level, protected, stripped in configurations:
        models = MODELS if args.stage == "tls-models" else (None,)
        if args.stage == "tls-models" and (not stripped or level not in ("O0", "O2")):
            continue
        for model in models:
            row = [tag + ("-" + model if model else ""), compiler, f"-{level}",
                   "-fstack-protector-all" if protected else "-fno-stack-protector",
                   "strip" if stripped else "nostrip"]
            if model:
                row.append(f"-ftls-model={model}")
            print("\t".join(row))
