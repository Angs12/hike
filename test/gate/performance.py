#!/usr/bin/env python3
"""Measure fresh production lifts; compare runtime independently of known lift reds."""

import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import shutil
import signal
import statistics
import subprocess
import threading
import time


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def lift_command(binary, stem, arguments):
    return ["bap", str(binary), "--pass=hike-convlir", "--no-cache",
            f"--hike-output-file={stem}.ll", *arguments]


def summarize(binary_hash, samples):
    return {"sha256": binary_hash, "samples": samples,
            "median_wall_s": statistics.median(s["wall_s"] for s in samples),
            "median_cpu_s": statistics.median(s["cpu_s"] for s in samples),
            "median_peak_rss_kib": statistics.median(s["peak_rss_kib"] for s in samples)}


def measure(command, log, timeout, env):
    """wait4 gives this child's CPU and peak RSS, without cumulative-process peaks."""
    expired = threading.Event()
    started = time.monotonic()
    with log.open("wb") as stream:
        with subprocess.Popen(command, stdout=stream, stderr=stream, env=env,
                              start_new_session=True) as child:
            def terminate():
                try:
                    os.killpg(child.pid, signal.SIGKILL)
                    expired.set()
                except ProcessLookupError:
                    pass

            timer = threading.Timer(timeout, terminate)
            timer.daemon = True
            timer.start()
            try:
                _, status, usage = os.wait4(child.pid, 0)
                child.returncode = os.waitstatus_to_exitcode(status)
            finally:
                timer.cancel()
                timer.join()
    return {"wall_s": time.monotonic() - started,
            "cpu_s": usage.ru_utime + usage.ru_stime,
            "peak_rss_kib": usage.ru_maxrss,
            "rc": 124 if expired.is_set() else child.returncode,
            "command": command}


def profile(binary, stem, args):
    command = ["perf", "stat", "-e", "task-clock,cycles,instructions",
               "-o", f"{stem}.stat", "--", "perf", "record", "-F", "99",
               "-e", "cpu-clock", "--call-graph", "dwarf,8192",
               "-o", f"{stem}.perf.data", "--",
               *lift_command(binary, stem, args.bap_arg)]
    result = measure(command, Path(f"{stem}.log"), args.timeout, os.environ.copy())
    if Path(f"{stem}.perf.data").exists():
        with Path(f"{stem}.report.txt").open("wb") as report:
            try:
                result["report_rc"] = subprocess.run(
                    ["perf", "report", "--stdio", "--children", "-g", "none",
                     "--percent-limit", "0.5", "-i", f"{stem}.perf.data"],
                    stdout=report, stderr=subprocess.STDOUT,
                    timeout=args.timeout).returncode
            except subprocess.TimeoutExpired:
                result["report_rc"] = 124
    result["data"] = str(Path(f"{stem}.perf.data").resolve())
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binaries", nargs="*", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--baseline", type=Path)
    parser.add_argument("--reference-lib", type=Path,
                        help="interleave a saved opam lib directory with the current plugin")
    parser.add_argument("--cpu", type=int, help="pin both builds to the same CPU")
    parser.add_argument("--profile", action="store_true",
                        help="capture perf once per binary after all timing runs")
    parser.add_argument("--repeats", type=int, default=3)
    parser.add_argument("--timeout", type=float, default=120)
    parser.add_argument("--budget", type=float)
    parser.add_argument("--max-ratio", type=float, default=1.15)
    parser.add_argument("--bap-arg", action="append", default=[])
    args = parser.parse_args()
    if not args.binaries:
        corpus = Path(os.environ.get("HIKE_CORPUS", "/tmp/corpus-o2"))
        args.binaries = [corpus / name for name in ("factorial", "fptr_table", "landmark_loop_1000")]
    limits = [args.timeout, args.max_ratio]
    if args.budget is not None:
        limits.append(args.budget)
    if args.repeats < 1 or any(not math.isfinite(n) or n <= 0 for n in limits):
        parser.error("repeats and time/ratio limits must be finite and positive")
    if args.baseline and args.reference_lib:
        parser.error("use either a recorded baseline or an interleaved reference")
    if args.profile and not shutil.which("perf"):
        parser.error("--profile requires perf on PATH")
    if args.cpu is not None:
        os.sched_setaffinity(0, {args.cpu})
    args.output.mkdir(parents=True, exist_ok=True)
    baseline = {}
    if args.baseline:
        recorded = json.loads(args.baseline.read_text())
        if recorded["arguments"] != args.bap_arg:
            parser.error("baseline BAP arguments differ")
        baseline = recorded["binaries"]
    lib = Path(subprocess.check_output(["ocamlfind", "query", "hike"], text=True).strip())
    provenance = lib / "hike.cmxs.provenance"
    manifest = {"arguments": args.bap_arg,
                "affinity": sorted(os.sched_getaffinity(0)),
                "plugin_provenance": provenance.read_text() if provenance.exists() else None,
                "binaries": {}}
    if args.reference_lib:
        provenance = args.reference_lib / "hike" / "hike.cmxs.provenance"
        if not provenance.exists():
            parser.error("reference lib must contain hike/hike.cmxs.provenance")
        manifest["reference_provenance"] = provenance.read_text()
    failed = False
    for index, binary in enumerate(args.binaries):
        binary = binary.resolve(strict=True)
        key = str(binary)
        samples = []
        reference = []
        for run in range(args.repeats):
            labels = ["reference", "current"] if args.reference_lib else ["current"]
            if run % 2:
                labels.reverse()
            for label in labels:
                stem = args.output / f"{index}-{binary.name}-{run}-{label}"
                env = os.environ.copy()
                if label == "reference":
                    env["OCAMLPATH"] = str(args.reference_lib.resolve()) + (
                        os.pathsep + env["OCAMLPATH"] if env.get("OCAMLPATH") else "")
                sample = measure(lift_command(binary, stem, args.bap_arg),
                                 Path(f"{stem}.log"), args.timeout, env)
                target = reference if label == "reference" else samples
                target.append(sample)
                print(f"RUN {binary.name} {label} {run + 1}/{args.repeats}: "
                      f"{sample['wall_s']:.3f}s rc={sample['rc']}", flush=True)
        row = summarize(sha256(binary), samples)
        manifest["binaries"][key] = row
        reasons = []
        if any(s["rc"] == 124 for s in samples):
            reasons.append("timeout")
        if args.budget is not None and row["median_wall_s"] > args.budget:
            reasons.append(f"exceeds {args.budget:.3f}s budget")
        if reference:
            row["reference"] = summarize(row["sha256"], reference)
        if args.baseline or reference:
            before = row.get("reference", baseline.get(key))
            if before is None or before["sha256"] != row["sha256"]:
                reasons.append("missing baseline for these binary bytes")
            else:
                ratio = row["median_wall_s"] / before["median_wall_s"]
                row["ratio"] = ratio
                if ratio > args.max_ratio:
                    reasons.append(f"runtime ratio {ratio:.3f} > {args.max_ratio}")
                if {s["rc"] for s in samples} - {s["rc"] for s in before["samples"]}:
                    reasons.append("new lift exit status")
        failed |= bool(reasons)
        print(f"{'FAIL' if reasons else 'PASS'} {binary.name}: "
              f"wall {row['median_wall_s']:.3f}s cpu {row['median_cpu_s']:.3f}s "
              f"RSS {row['median_peak_rss_kib'] / 1024:.1f}MiB "
              + (f"ratio {row['ratio']:.3f} " if "ratio" in row else "")
              + ("; ".join(reasons) if reasons else ""), flush=True)
        (args.output / "timings.json").write_text(json.dumps(manifest, indent=2) + "\n")
    if args.profile:
        for index, (binary, row) in enumerate(manifest["binaries"].items()):
            stem = args.output / f"{index}-{Path(binary).name}-profile"
            print(f"PROFILE {binary}", flush=True)
            row["profile"] = profile(binary, stem, args)
            if row["profile"]["rc"] not in {s["rc"] for s in row["samples"]} or row["profile"].get("report_rc") != 0:
                failed = True
                print(f"FAIL profiling {binary}; inspect {stem}.log", flush=True)
            (args.output / "timings.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"Results: {(args.output / 'timings.json').resolve()}")
    return int(failed)


if __name__ == "__main__":
    raise SystemExit(main())
