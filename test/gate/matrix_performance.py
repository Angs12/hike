#!/usr/bin/env python3
"""Compare every native matrix cell through the production performance gate."""

import argparse
import json
import math
import os
from pathlib import Path
import subprocess
import sys

import performance
from matrix_cases import cells



def run(command, stem, timeout):
    """Capture stdout separately: semantic comparisons exclude diagnostics."""
    with Path(f"{stem}.out").open("wb") as out, Path(f"{stem}.err").open("wb") as err:
        try:
            rc = subprocess.run(command, stdout=out, stderr=err, timeout=timeout).returncode
        except subprocess.TimeoutExpired:
            rc = 124
    return {"rc": rc, "stdout": str(Path(f"{stem}.out")), "command": command}


def check_lift(binary, row, stem, timeout, level=None):
    samples = row["samples"]
    if samples[0]["rc"]:
        return {"stage": "lift", "rc": samples[0]["rc"]}
    command = samples[0]["command"]
    ir = Path(command[command.index("-o") + 1])
    if level is not None:
        optimized = Path(f"{stem}.ll")
        step = run([os.environ.get("HIKE_OPT", "opt-21"), f"-O{level}",
                    str(ir), "-S", "-o", str(optimized)], f"{stem}-opt", timeout)
        if step["rc"]:
            return {"stage": "opt", **step}
        ir = optimized
    obj, exe = Path(f"{stem}.o"), Path(f"{stem}.bin")
    commands = [("llc", [os.environ.get("HIKE_LLC", "llc-21"), "-O0",
                         "-relocation-model=pic", "-filetype=obj", str(ir), "-o", str(obj)]),
                ("link", ["gcc", "-pie", str(obj), "-o", str(exe), "-lpthread"])]
    for stage, command in commands:
        step = run(command, f"{stem}-{stage}", timeout)
        if step["rc"]:
            return {"stage": stage, **step}
    result = run([str(exe)], stem, timeout)
    native = run([str(binary)], f"{stem}-native", timeout)
    same = (result["rc"] == native["rc"]
            and Path(result["stdout"]).read_bytes() == Path(native["stdout"]).read_bytes())
    return {"stage": "pass" if same and result["rc"] != 124 else "semantic",
            "lifted": result, "native": native}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--reference", required=True, type=Path,
                        help="a saved build: its hike executable and hike.cmxs.provenance")
    parser.add_argument("--cpu", type=int)
    parser.add_argument("--repeats", type=int, default=3)
    parser.add_argument("--timeout", type=float, default=120)
    parser.add_argument("--max-ratio", type=float, default=1.15)
    args = parser.parse_args()
    if args.repeats < 1 or any(not math.isfinite(n) or n <= 0
                             for n in (args.timeout, args.max_ratio)):
        parser.error("repeats and time/ratio limits must be finite and positive")
    if args.cpu is not None and args.cpu not in os.sched_getaffinity(0):
        parser.error("CPU is outside the available affinity set")
    if not ((args.reference / "hike").is_file()
            and (args.reference / "hike.cmxs.provenance").is_file()):
        parser.error("reference must contain hike and hike.cmxs.provenance")
    args.output = args.output.resolve()
    args.output.mkdir(parents=True, exist_ok=True)
    source = Path(__file__).resolve().parents[2] / "src" / "progs"
    sources = sorted(source.glob("*.c")) + sorted((source / "synth").glob("*.c"))
    sources = [path for path in sources if path.stem != "list"]
    records, binaries = [], []
    for tag, compiler, level, protected, stripped in cells():
        directory = args.output / "native" / tag
        directory.mkdir(parents=True, exist_ok=True)
        for path in sources:
            binary = directory / path.stem
            command = [compiler, f"-{level}", "-fstack-protector-all" if protected
                       else "-fno-stack-protector", "-o", str(binary), str(path), "-lpthread"]
            result = run(command, f"{binary}-compile", args.timeout)
            record = {"cell": tag, "binary": str(binary), "source_sha256": performance.sha256(path),
                      "compile": result}
            if result["rc"] == 0 and stripped:
                record["strip"] = run(["objcopy", "--strip-all", str(binary)],
                                      f"{binary}-strip", args.timeout)
                result = record["strip"]
            records.append(record)
            if result["rc"] == 0:
                binaries.append(str(binary))
        print(f"COMPILED {tag}: {len(sources)} sources", flush=True)
    (args.output / "compilation.json").write_text(json.dumps(records, indent=2) + "\n")
    timing_output = args.output / "lifts"
    command = [sys.executable, str(Path(__file__).with_name("performance.py")),
               "--output", str(timing_output), "--reference", str(args.reference.resolve()),
               "--repeats", str(args.repeats), "--timeout", str(args.timeout),
               "--max-ratio", str(args.max_ratio)]
    if args.cpu is not None:
        command.extend(["--cpu", str(args.cpu)])
    subprocess.run([*command, *binaries], check=False)
    timing = json.loads((timing_output / "timings.json").read_text())
    regressions, improvements, reds, runtime_reds = [], [], [], []
    semantic_dir = args.output / "semantics"
    semantic_dir.mkdir(exist_ok=True)
    for record in records:
        binary = Path(record["binary"])
        if record["compile"]["rc"] or record.get("strip", {}).get("rc", 0):
            regressions.append(f"{record['cell']}/{binary.name}: compile")
            continue
        row = timing["binaries"][str(binary)]
        if row["ratio"] > args.max_ratio or any(s["rc"] == 124 for s in row["samples"]):
            runtime_reds.append(f"{record['cell']}/{binary.name}: ratio {row['ratio']:.3f}")
        results = {}
        levels = [None, "0", "1", "2", "3", "s"] if record["cell"] == "gcc-O2-nosp-strip" else [None]
        for level in levels:
            key = "llc-O0" if level is None else f"opt-O{level}"
            results[key] = {}
            for label, samples in (("reference", row["reference"]), ("current", row)):
                stem = semantic_dir / f"{record['cell']}-{binary.name}-{label}-{key}"
                results[key][label] = check_lift(binary, samples, stem, 10, level)
            before, after = (results[key][label]["stage"] for label in ("reference", "current"))
            case = f"{record['cell']}/{binary.name}/{key}"
            if before == "pass" and after != "pass":
                regressions.append(f"{case}: {after}")
            elif before != "pass" and after == "pass":
                improvements.append(case)
            elif after != "pass":
                reds.append(f"{case}: {before} -> {after}")
        record["semantics"] = results
        print(f"CHECKED {record['cell']}/{binary.name}: "
              f"{results['llc-O0']['reference']['stage']} -> {results['llc-O0']['current']['stage']}", flush=True)
        (args.output / "results.json").write_text(json.dumps(records, indent=2) + "\n")
    verdict = {"binaries": len(binaries), "native_cells": 18, "repeats": args.repeats,
               "timing_regressions": runtime_reds, "correctness_regressions": regressions,
               "improvements": improvements, "existing_reds": reds}
    (args.output / "verdict.json").write_text(json.dumps(verdict, indent=2) + "\n")
    lines = ["# Full matrix comparison", "",
             f"{len(binaries)} binaries across 18 native cells, {args.repeats} interleaved runs per build.",
             "Consumer optimization sweep: O0/O1/O2/O3/Os on the entire GCC O2 stripped cell.", "",
             "| Cell | Median runtime ratio | Current / reference semantic passes |", "|---|---:|---:|"]
    for tag, *_ in cells():
        members = [r for r in records if r["cell"] == tag and "semantics" in r]
        ratios = [timing["binaries"][r["binary"]]["ratio"] for r in members]
        ratio = math.exp(sum(math.log(r) for r in ratios) / len(ratios)) if ratios else float("nan")
        count = lambda label: sum(r["semantics"]["llc-O0"][label]["stage"] == "pass" for r in members)
        lines.append(f"| {tag} | {ratio:.3f} (geometric mean) | {count('current')} / {count('reference')} of {len(members)} |")
    for title, cases in (("Runtime regressions", runtime_reds), ("Correctness regressions", regressions),
                         ("Improvements", improvements), ("Existing reds", reds)):
        lines.extend(["", f"## {title}", "", *([f"- {case}" for case in cases] or ["None."])])
    (args.output / "verdict.md").write_text("\n".join(lines) + "\n")
    print(json.dumps(verdict), flush=True)
    return int(bool(regressions or runtime_reds))


if __name__ == "__main__":
    raise SystemExit(main())
