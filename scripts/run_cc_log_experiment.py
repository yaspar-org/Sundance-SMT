#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0
"""
Run Sundance with --cc-log over every .smt2 file in a benchmark tree to
collect pure congruence-closure benchmarks.

Resumable: progress is recorded in `<output-dir>/progress.json`. On
re-invocation, benchmarks already marked done are skipped, and benchmarks
that previously timed out / errored are also skipped unless --retry-failed
is given. SIGINT/SIGTERM stops cleanly: in-flight workers are allowed to
finish (or are killed by the per-benchmark timeout) and the partial
progress.json is flushed.

Layout under --output-dir:
  progress.json              - resume state (atomically updated)
  log.txt                    - one TSV line per processed benchmark
  benchmarks/<rel_path>/     - one folder per source benchmark, holding
                               the `*_cc_<N>.smt2` files dumped on each
                               CC conflict for that source benchmark.

Per-benchmark statuses recorded in progress.json:
  ok       - solver exited normally
  timeout  - hit --timeout (the partial dumps are still kept)
  error    - python-side exception or non-zero exit before timeout
"""

import argparse
import concurrent.futures as futures
import json
import os
import shlex
import signal
import subprocess
import time
from pathlib import Path

DEFAULT_TIMEOUT = 120  # seconds per benchmark (large; pure CC dumps are useful even on slow inputs)
DEFAULT_JOBS = max(1, (os.cpu_count() or 4) // 2)


def find_smt_files(input_dir: Path):
    return sorted(p for p in input_dir.rglob("*.smt2") if p.is_file())


def load_progress(progress_path: Path):
    if not progress_path.exists():
        return {"done": {}, "failed": {}}
    try:
        with progress_path.open() as fh:
            data = json.load(fh)
    except json.JSONDecodeError:
        print(f"warning: {progress_path} is malformed, starting fresh", flush=True)
        return {"done": {}, "failed": {}}
    data.setdefault("done", {})
    data.setdefault("failed", {})
    return data


def save_progress(progress_path: Path, progress):
    tmp = progress_path.with_suffix(".json.tmp")
    with tmp.open("w") as fh:
        json.dump(progress, fh, indent=2, sort_keys=True)
    tmp.replace(progress_path)


def run_one(job):
    """Worker: solve one benchmark. Returns a dict with the outcome.

    `job` is a dict so it pickles cleanly across the process pool.
    """
    smt_file = Path(job["smt_file"])
    solver = Path(job["solver"])
    cc_log_subdir = Path(job["cc_log_subdir"])
    timeout = job["timeout"]
    extra_args = job["extra_args"]
    key = job["key"]

    cc_log_subdir.mkdir(parents=True, exist_ok=True)
    cmd = [
        str(solver),
        "--cc-log",
        str(cc_log_subdir),
        *extra_args,
        str(smt_file),
    ]
    start = time.time()
    try:
        proc = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        elapsed = time.time() - start
        last_stdout = proc.stdout.strip().splitlines()[-1] if proc.stdout.strip() else ""
        if proc.returncode == 0:
            outcome = {"status": "ok", "result": last_stdout}
        else:
            outcome = {
                "status": "error",
                "result": last_stdout,
                "returncode": proc.returncode,
                "stderr_tail": (
                    proc.stderr.strip().splitlines()[-1]
                    if proc.stderr.strip()
                    else ""
                ),
            }
    except subprocess.TimeoutExpired:
        elapsed = time.time() - start
        outcome = {"status": "timeout", "result": ""}
    except Exception as exc:
        elapsed = time.time() - start
        outcome = {"status": "error", "result": "", "error": str(exc)}

    n_dumped = len(list(cc_log_subdir.glob("*.smt2"))) if cc_log_subdir.exists() else 0
    outcome.update(
        {
            "key": key,
            "elapsed": elapsed,
            "n_dumped": n_dumped,
        }
    )
    return outcome


def main():
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    ap.add_argument(
        "--input-dir",
        type=Path,
        required=True,
        help="root directory of source SMT2 benchmarks (recursively scanned for *.smt2)",
    )
    ap.add_argument(
        "--output-dir",
        type=Path,
        required=True,
        help="directory to write progress.json, log.txt, and benchmarks/",
    )
    ap.add_argument(
        "--solver",
        type=Path,
        default=Path("./target/release/sundance-smt"),
        help="path to the sundance-smt binary (default: ./target/release/sundance-smt)",
    )
    ap.add_argument(
        "--timeout",
        type=int,
        default=DEFAULT_TIMEOUT,
        help=f"per-benchmark timeout in seconds (default {DEFAULT_TIMEOUT})",
    )
    ap.add_argument(
        "-j",
        "--jobs",
        type=int,
        default=DEFAULT_JOBS,
        help=f"number of parallel worker processes (default {DEFAULT_JOBS}, ~half of CPU count)",
    )
    ap.add_argument(
        "--retry-failed",
        action="store_true",
        help="re-run benchmarks previously marked failed/timeout",
    )
    ap.add_argument(
        "--limit",
        type=int,
        default=0,
        help="dispatch at most this many *new* benchmarks this invocation (0 = no limit)",
    )
    ap.add_argument(
        "--solver-args",
        default="",
        help="extra arguments to pass to the solver (a single shell-quoted string)",
    )
    ap.add_argument(
        "--save-every",
        type=int,
        default=20,
        help="flush progress.json after this many completions (default 20)",
    )
    args = ap.parse_args()

    if not args.input_dir.is_dir():
        ap.error(f"input directory does not exist: {args.input_dir}")
    if not args.solver.exists():
        ap.error(
            f"solver binary not found: {args.solver}\n"
            f"build it first: cargo build --release"
        )

    args.output_dir.mkdir(parents=True, exist_ok=True)
    benchmarks_root = args.output_dir / "benchmarks"
    benchmarks_root.mkdir(exist_ok=True)
    progress_path = args.output_dir / "progress.json"
    log_path = args.output_dir / "log.txt"

    extra_args = shlex.split(args.solver_args) if args.solver_args else []
    progress = load_progress(progress_path)

    smt_files = find_smt_files(args.input_dir)
    print(f"found {len(smt_files)} smt2 files under {args.input_dir}", flush=True)

    # Build the work queue.
    pending = []
    skipped = 0
    for smt_file in smt_files:
        rel = smt_file.relative_to(args.input_dir)
        key = str(rel)
        if key in progress["done"]:
            skipped += 1
            continue
        if key in progress["failed"] and not args.retry_failed:
            skipped += 1
            continue
        pending.append((smt_file, rel, key))
        if args.limit and len(pending) >= args.limit:
            break

    print(
        f"queueing {len(pending)} benchmarks "
        f"(skipping {skipped} already in progress.json), "
        f"jobs={args.jobs}, timeout={args.timeout}s",
        flush=True,
    )

    interrupted = {"flag": False}

    def _signal_handler(signum, frame):
        if interrupted["flag"]:
            print("\n[signal] second signal received, exiting hard", flush=True)
            os._exit(130)
        interrupted["flag"] = True
        print(
            f"\n[signal {signum}] no longer dispatching new jobs; "
            "in-flight workers will finish or hit --timeout. ctrl-c again to abort.",
            flush=True,
        )

    signal.signal(signal.SIGINT, _signal_handler)
    signal.signal(signal.SIGTERM, _signal_handler)

    completed = 0
    new_done = 0
    new_failed = 0

    log_fh = log_path.open("a")
    log_fh.write(
        f"# run started at {time.strftime('%Y-%m-%d %H:%M:%S')} "
        f"timeout={args.timeout}s jobs={args.jobs}\n"
    )
    log_fh.flush()

    try:
        with futures.ProcessPoolExecutor(max_workers=args.jobs) as pool:
            in_flight = {}
            it = iter(pending)

            def submit_more():
                while not interrupted["flag"] and len(in_flight) < args.jobs:
                    try:
                        smt_file, rel, key = next(it)
                    except StopIteration:
                        return
                    cc_log_subdir = benchmarks_root / rel.with_suffix("")
                    job = {
                        "smt_file": str(smt_file),
                        "solver": str(args.solver),
                        "cc_log_subdir": str(cc_log_subdir),
                        "timeout": args.timeout,
                        "extra_args": extra_args,
                        "key": key,
                    }
                    fut = pool.submit(run_one, job)
                    in_flight[fut] = key

            submit_more()

            while in_flight:
                done, _ = futures.wait(
                    in_flight.keys(), return_when=futures.FIRST_COMPLETED
                )
                for fut in done:
                    key = in_flight.pop(fut)
                    try:
                        outcome = fut.result()
                    except Exception as exc:
                        outcome = {
                            "status": "error",
                            "key": key,
                            "elapsed": 0.0,
                            "n_dumped": 0,
                            "result": "",
                            "error": f"future failed: {exc}",
                        }

                    completed += 1
                    line = (
                        f"{outcome['status']}\t"
                        f"elapsed={outcome['elapsed']:.2f}s\t"
                        f"dumped={outcome['n_dumped']}\t"
                        f"{outcome['key']}"
                    )
                    print(line, flush=True)
                    log_fh.write(line + "\n")
                    log_fh.flush()

                    entry = {
                        "elapsed": outcome["elapsed"],
                        "n_dumped": outcome["n_dumped"],
                        "result": outcome.get("result", ""),
                        "status": outcome["status"],
                    }
                    if "error" in outcome:
                        entry["error"] = outcome["error"]
                    if "stderr_tail" in outcome:
                        entry["stderr_tail"] = outcome["stderr_tail"]
                    if "returncode" in outcome:
                        entry["returncode"] = outcome["returncode"]

                    if outcome["status"] == "ok":
                        progress["done"][outcome["key"]] = entry
                        progress["failed"].pop(outcome["key"], None)
                        new_done += 1
                    else:
                        progress["failed"][outcome["key"]] = entry
                        new_failed += 1

                    if completed % args.save_every == 0:
                        save_progress(progress_path, progress)

                submit_more()
    finally:
        save_progress(progress_path, progress)
        log_fh.write(
            f"# run ended at {time.strftime('%Y-%m-%d %H:%M:%S')} "
            f"completed={completed} new_done={new_done} new_failed={new_failed}\n"
        )
        log_fh.close()

    n_done = len(progress["done"])
    n_failed = len(progress["failed"])
    n_timeout = sum(
        1 for e in progress["failed"].values() if e.get("status") == "timeout"
    )
    n_error = sum(
        1 for e in progress["failed"].values() if e.get("status") == "error"
    )
    print(
        f"summary: completed_this_run={completed} new_done={new_done} "
        f"new_failed={new_failed} skipped={skipped} "
        f"total_done={n_done} total_failed={n_failed} "
        f"(timeout={n_timeout}, error={n_error})",
        flush=True,
    )


if __name__ == "__main__":
    main()
