#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0
"""
Run Sundance with --cc-log over every .smt2 file in a benchmark tree to
collect pure congruence-closure benchmarks.

Resumable: progress is recorded in a state file (`progress.json`). On
re-invocation, benchmarks already marked done are skipped. Sending
SIGINT (Ctrl-C) stops cleanly after the current file finishes; partial
progress is preserved.

Layout under --output-dir:
  progress.json              - resume state
  log.txt                    - one line per processed benchmark
  benchmarks/<rel_path>/     - one folder per source benchmark, holding
                               the `*_cc_<N>.smt2` files dumped on each
                               CC conflict for that source benchmark.
"""

import argparse
import json
import os
import shlex
import signal
import subprocess
import sys
import time
from pathlib import Path

DEFAULT_TIMEOUT = 30  # seconds per benchmark


def find_smt_files(input_dir: Path):
    return sorted(p for p in input_dir.rglob("*.smt2") if p.is_file())


def load_progress(progress_path: Path):
    if not progress_path.exists():
        return {"done": {}, "failed": {}}
    try:
        with progress_path.open() as fh:
            data = json.load(fh)
    except json.JSONDecodeError:
        print(f"warning: {progress_path} is malformed, starting fresh")
        return {"done": {}, "failed": {}}
    data.setdefault("done", {})
    data.setdefault("failed", {})
    return data


def save_progress(progress_path: Path, progress):
    tmp = progress_path.with_suffix(".json.tmp")
    with tmp.open("w") as fh:
        json.dump(progress, fh, indent=2, sort_keys=True)
    tmp.replace(progress_path)


def run_one(
    smt_file: Path,
    solver: Path,
    cc_log_subdir: Path,
    timeout: int,
    extra_args,
):
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
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        elapsed = time.time() - start
        return {
            "status": "ok",
            "returncode": result.returncode,
            "stdout": result.stdout.strip().splitlines()[-1] if result.stdout.strip() else "",
            "stderr_tail": result.stderr.strip().splitlines()[-1] if result.stderr.strip() else "",
            "elapsed": elapsed,
        }
    except subprocess.TimeoutExpired:
        return {"status": "timeout", "elapsed": time.time() - start}
    except Exception as exc:  # pragma: no cover
        return {"status": "error", "error": str(exc), "elapsed": time.time() - start}


_INTERRUPTED = False


def _handle_sigint(signum, frame):
    global _INTERRUPTED
    if _INTERRUPTED:
        # second Ctrl-C: hard exit
        sys.exit(130)
    _INTERRUPTED = True
    print("\n[ctrl-c] finishing current benchmark, then stopping...", flush=True)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--input-dir", type=Path, default=Path("../single_query/QF_UF"),
                    help="root directory of source SMT2 benchmarks (default: ../single_query/QF_UF)")
    ap.add_argument("--output-dir", type=Path, required=True,
                    help="directory to write progress.json, log.txt, and benchmarks/")
    ap.add_argument("--solver", type=Path, default=Path("./target/release/sundance-smt"),
                    help="path to the sundance-smt binary")
    ap.add_argument("--timeout", type=int, default=DEFAULT_TIMEOUT,
                    help=f"per-benchmark timeout in seconds (default {DEFAULT_TIMEOUT})")
    ap.add_argument("--retry-failed", action="store_true",
                    help="re-run benchmarks previously marked failed/timeout")
    ap.add_argument("--limit", type=int, default=0,
                    help="process at most this many *new* benchmarks (0 = no limit)")
    ap.add_argument("--solver-args", default="",
                    help="extra arguments to pass to the solver (a single shell-quoted string)")
    args = ap.parse_args()

    if not args.input_dir.is_dir():
        ap.error(f"input directory does not exist: {args.input_dir}")
    if not args.solver.exists():
        ap.error(f"solver binary not found: {args.solver}\n"
                 f"build it first: cargo build --release")

    args.output_dir.mkdir(parents=True, exist_ok=True)
    benchmarks_root = args.output_dir / "benchmarks"
    benchmarks_root.mkdir(exist_ok=True)
    progress_path = args.output_dir / "progress.json"
    log_path = args.output_dir / "log.txt"

    extra_args = shlex.split(args.solver_args) if args.solver_args else []
    progress = load_progress(progress_path)

    signal.signal(signal.SIGINT, _handle_sigint)

    smt_files = find_smt_files(args.input_dir)
    print(f"found {len(smt_files)} smt2 files under {args.input_dir}")

    processed = 0
    skipped = 0
    new_done = 0
    new_failed = 0

    log_fh = log_path.open("a")
    try:
        for smt_file in smt_files:
            if _INTERRUPTED:
                break
            rel = smt_file.relative_to(args.input_dir)
            key = str(rel)

            if key in progress["done"]:
                skipped += 1
                continue
            if key in progress["failed"] and not args.retry_failed:
                skipped += 1
                continue

            cc_log_subdir = benchmarks_root / rel.with_suffix("")

            result = run_one(
                smt_file, args.solver, cc_log_subdir, args.timeout, extra_args
            )
            processed += 1

            n_dumped = len(list(cc_log_subdir.glob("*.smt2"))) if cc_log_subdir.exists() else 0
            line = (
                f"{result['status']}\t"
                f"elapsed={result['elapsed']:.2f}s\t"
                f"dumped={n_dumped}\t"
                f"{key}"
            )
            print(line, flush=True)
            log_fh.write(line + "\n")
            log_fh.flush()

            entry = {
                "elapsed": result["elapsed"],
                "n_dumped": n_dumped,
                "result": result.get("stdout", ""),
                "status": result["status"],
            }
            if result["status"] == "ok":
                progress["done"][key] = entry
                new_done += 1
                progress["failed"].pop(key, None)
            else:
                progress["failed"][key] = entry
                new_failed += 1

            # save progress every 10 processed and at the end
            if processed % 10 == 0:
                save_progress(progress_path, progress)

            if args.limit and processed >= args.limit:
                print(f"[limit] reached --limit={args.limit}, stopping", flush=True)
                break
    finally:
        save_progress(progress_path, progress)
        log_fh.close()

    total_done = len(progress["done"])
    total_failed = len(progress["failed"])
    print(
        f"summary: processed={processed} new_done={new_done} new_failed={new_failed} "
        f"skipped={skipped} total_done={total_done} total_failed={total_failed}",
        flush=True,
    )


if __name__ == "__main__":
    main()
