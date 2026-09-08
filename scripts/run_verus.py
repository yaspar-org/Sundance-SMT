# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0
"""
Script to run a solver command on each .smt2 file in a folder
and count the number of unsat, unknown, and other results.
Supports parallel processing for improved performance.
"""
import os
import shlex
import subprocess
import sys
from pathlib import Path
import argparse
from typing import Dict, List, Tuple, Optional
import multiprocessing as mp
import time
import re

DEFAULT_TIMEOUT = 10  # seconds timeout per file


def run_cargo_on_file(filepath: Path, solver_command: str, timeout: int = DEFAULT_TIMEOUT) -> Tuple[str, str, float]:
    """
    Run cargo command on a single file and return the output and execution time.
    Args:
        filepath: Path to the file to process
        solver_command: command to run on the SMT `filepath`
    Returns:
        Tuple of (stdout, stderr, time_taken) from the cargo command
    """
    start_time = time.time()
    try:
        command = shlex.split(solver_command) + [str(filepath)]
        result = subprocess.run(
            command, capture_output=True, text=True, timeout=timeout
        )
        end_time = time.time()
        return result.stdout, result.stderr, end_time - start_time
    except subprocess.TimeoutExpired:
        end_time = time.time()
        return "", "TIMEOUT", end_time - start_time
    except Exception as e:
        end_time = time.time()
        return "", f"ERROR: {str(e)}", end_time - start_time


def process_single_file_wrapper(
    args: Tuple[Path, Path, bool, str, int],
) -> Tuple[Path, str, float, str, str]:
    """
    Wrapper function to process a single file for multiprocessing.
    Args:
        args: Tuple of (filepath, base_folder_path, verbose, solver_command, timeout)
    Returns:
        Tuple of (filepath, category, time_taken, stdout, stderr)
    """
    filepath, _, _, solver_command, timeout = args

    # Run solver on the file
    stdout, stderr, time_taken = run_cargo_on_file(filepath, solver_command, timeout)

    # Categorize the result
    category = categorize_result(stdout, stderr)

    return filepath, category, time_taken, stdout, stderr


def categorize_result(stdout: str, stderr: str) -> str:
    """
    Categorize the result based on output content.
    Args:
        stdout: Standard output from cargo command
        stderr: Standard error from cargo command
    Returns:
        Category: 'unsat', 'unknown', or 'other'
    """
    # Combine output for checking
    combined_output = stdout.strip()
    # Check for unsat result
    if combined_output.endswith("unsat"):
        return "unsat"
    # Check for unknown result
    if combined_output.endswith("unknown"):
        return "unknown"
    # Check for timeout
    if "TIMEOUT" in stderr:
        return "timeout"
    # Check for errors: this script's own ERROR sentinel (see run_cargo_on_file), a solver
    # panic, or the solver refusing to answer -- `main` reports the latter as `Error: "..."`
    # on stderr, e.g. when an assertion uses an unsupported theory such as bitvectors.
    if "ERROR" in stderr or "Error:" in stderr or "panicked at" in stderr:
        return "error"
    # Otherwise categorize as other
    return "other"


def parse_previous_results(results_file: Path, _base_folder: Path) -> Dict[str, str]:
    """
    Parse a previous results file and return a mapping of file paths to their results.
    Args:
        results_file: Path to the results file to parse
        base_folder: Base folder path for relativizing file paths
    Returns:
        Dictionary mapping relative file paths to their result categories
    """
    file_results = {}

    if not results_file.exists():
        print(f"Warning: Results file '{results_file}' does not exist")
        return file_results

    # Pattern to match lines like: [1/3763] verismo/tspec_e__array__array_e.6.smt2 -> UNKNOWN [2.10s]
    pattern = re.compile(r"\[\d+/\d+\]\s+(.+?)\s+->\s+(\w+)\s+\[[\d.]+s\]")

    try:
        with open(results_file, "r", encoding="utf-8") as f:
            for line in f:
                match = pattern.match(line.strip())
                if match:
                    file_path = match.group(1)
                    result = match.group(2).lower()
                    file_results[file_path] = result

        print(f"Parsed {len(file_results)} previous results from '{results_file}'")
    except Exception as e:
        print(f"Error reading results file '{results_file}': {e}")

    return file_results


def should_rerun_file(
    filepath: Path, base_folder: Path, previous_results: Dict[str, str]
) -> bool:
    """
    Determine if a file should be rerun based on previous results.
    Args:
        filepath: Path to the file
        base_folder: Base folder path for creating relative paths
        previous_results: Dictionary of previous results
    Returns:
        True if the file should be rerun, False otherwise
    """
    try:
        relative_path = filepath.relative_to(base_folder)
        relative_path_str = str(relative_path)

        # If file was not in previous results, rerun it
        if relative_path_str not in previous_results:
            return True

        # If file had "other" result in previous run, rerun it
        previous_result = previous_results[relative_path_str]
        if previous_result == "other":
            return True

        # Otherwise, skip it
        return False
    except ValueError:
        # If we can't make it relative, rerun it to be safe
        return True


def process_folder(
    folder_path: Path,
    verbose: bool = False,
    num_processes: int = 4,
    previous_results: Optional[Dict[str, str]] = None,
    solver_command: str = "echo",
    timeout: int = DEFAULT_TIMEOUT,
) -> Dict[str, List[Path]]:
    """
    Recursively process all files in a folder using parallel processing.
    Args:
        folder_path: Path to the folder to process
        verbose: If True, print detailed output for each file
        num_processes: Number of parallel processes to use
        previous_results: Optional dictionary of previous results for filtering
        solver_command: command to run on every SMT file in the folder
        timeout: seconds before killing a solver invocation
    Returns:
        Dictionary with counts and file lists for each category
    """
    results = {"unsat": [], "unknown": [], "timeout": [], "error": [], "other": []}

    # Get all files recursively
    all_files = []
    for root, _, files in os.walk(folder_path):
        for file in files:
            filepath = Path(root) / file
            # Skip hidden files and directories
            if not any(part.startswith(".") for part in filepath.parts) and str(
                filepath
            ).endswith(".smt2"):
                all_files.append(filepath)

    all_files.sort()

    # Filter files based on previous results if provided
    files_to_process = []
    if previous_results is not None:
        skipped_count = 0
        for filepath in all_files:
            if should_rerun_file(filepath, folder_path, previous_results):
                files_to_process.append(filepath)
            else:
                skipped_count += 1
        print(
            f"Found {len(all_files)} total files, filtering to {len(files_to_process)} files to process"
        )
        print(
            f"Skipping {skipped_count} files that already have UNSAT/UNKNOWN/TIMEOUT/ERROR results"
        )
    else:
        files_to_process = all_files

    total_files = len(files_to_process)
    print(f"Processing {total_files} files in '{folder_path}'")
    print(f"Using {num_processes} parallel processes")
    print("-" * 60)

    if total_files == 0:
        return results

    # Prepare arguments for multiprocessing
    process_args = [
        (filepath, folder_path, verbose, solver_command, timeout)
        for filepath in files_to_process
    ]

    # Use multiprocessing to process files in parallel
    start_time = time.time()
    completed = 0

    with mp.Pool(processes=num_processes) as pool:
        # Process files in parallel and get results as they complete
        for filepath, category, time_taken, stdout, stderr in pool.imap_unordered(
            process_single_file_wrapper, process_args
        ):
            completed += 1
            results[category].append(filepath)

            # Print progress
            relative_path = filepath.relative_to(folder_path)
            print(
                f"[{completed}/{total_files}] {relative_path} -> {category.upper()} [{time_taken:.2f}s]"
            )

            if verbose:
                print(
                    f"  Output preview: {stdout[:1000]}..." if stdout else "  No output"
                )
                if stderr and stderr not in ["TIMEOUT", "ERROR"]:
                    print(f"  Stderr preview: {stderr[-1000:]}...")
                print()

            sys.stdout.flush()

    elapsed_time = time.time() - start_time
    print(f"\nProcessing completed in {elapsed_time:.2f} seconds")

    return results


def print_summary(results: Dict[str, List[Path]], folder_path: Path):
    """
    Print a summary of the results.
    Args:
        results: Dictionary with categorized results
        folder_path: The base folder path for relative path display
    """
    print("\n" + "=" * 60)
    print("SUMMARY")
    print("=" * 60)
    total = sum(len(files) for files in results.values())
    # Print counts
    print(f"\nTotal files processed: {total}")
    print(
        f"  - UNSAT results:   {len(results['unsat']):4d} ({len(results['unsat'])*100/total if total else 0:.1f}%)"
    )
    print(
        f"  - UNKNOWN results: {len(results['unknown']):4d} ({len(results['unknown'])*100/total if total else 0:.1f}%)"
    )
    print(
        f"  - TIMEOUT results: {len(results['timeout']):4d} ({len(results['timeout'])*100/total if total else 0:.1f}%)"
    )
    print(
        f"  - ERROR results:   {len(results['error']):4d} ({len(results['error'])*100/total if total else 0:.1f}%)"
    )
    print(
        f"  - OTHER results:   {len(results['other']):4d} ({len(results['other'])*100/total if total else 0:.1f}%)"
    )
    # Neither unsat nor unknown (includes timeout, error, and other)
    neither_count = (
        len(results["timeout"]) + len(results["error"]) + len(results["other"])
    )
    print(
        f"\n  - Neither UNSAT nor UNKNOWN: {neither_count:4d} ({neither_count*100/total if total else 0:.1f}%)"
    )
    # Optionally list files in each category
    if any(len(files) > 0 and len(files) <= 10 for files in results.values()):
        print("\n" + "-" * 60)
        for category, files in results.items():
            if 0 < len(files) <= 10:
                print(f"\n{category.upper()} files:")
                for f in files:
                    print(f"  - {f.relative_to(folder_path)}")


def main():
    parser = argparse.ArgumentParser(
        description="Run a solver command on all .smt2 files in a folder and count results"
    )
    parser.add_argument(
        "folder", type=str, help="Path to the folder containing files to process"
    )
    parser.add_argument(
        "-v",
        "--verbose",
        action="store_true",
        help="Show detailed output for each file",
    )
    parser.add_argument("-o", "--output", type=str, help="Save results to a file")
    parser.add_argument(
        "-j",
        "--jobs",
        type=int,
        default=4,
        help="Number of parallel processes to use (default: 4)",
    )
    parser.add_argument(
        "--solver-command",
        type=str,
        required=True,
        help="Solver command to run on every file in the folder",
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=DEFAULT_TIMEOUT,
        help=f"Timeout in seconds per solver invocation (default: {DEFAULT_TIMEOUT})",
    )
    parser.add_argument(
        "--filter-from",
        type=str,
        help="Path to a previous results file. Only rerun benchmarks that were not in the original file or had OTHER results",
    )
    args = parser.parse_args()

    # Validate number of processes
    if args.jobs < 1:
        print("Error: Number of jobs must be at least 1")
        sys.exit(1)

    # Validate folder path
    folder_path = Path(args.folder).resolve()
    if not folder_path.exists():
        print(f"Error: Folder '{folder_path}' does not exist")
        sys.exit(1)
    if not folder_path.is_dir():
        print(f"Error: '{folder_path}' is not a directory")
        sys.exit(1)

    # Parse previous results if filtering is requested
    previous_results = None
    if args.filter_from:
        results_file_path = Path(args.filter_from).resolve()
        if not results_file_path.exists():
            print(f"Error: Results file '{results_file_path}' does not exist")
            sys.exit(1)
        previous_results = parse_previous_results(results_file_path, folder_path)

    # Process the folder
    print(f"Starting to process folder: {folder_path}")
    if previous_results:
        print(f"Filtering based on previous results from: {args.filter_from}")
    results = process_folder(
        folder_path, args.verbose, args.jobs, previous_results, args.solver_command,
        args.timeout,
    )

    # Print summary
    print_summary(results, folder_path)

    # Save results if requested
    if args.output:
        output_path = Path(args.output)
        with open(output_path, "w") as f:
            f.write(f"Results for folder: {folder_path}\n")
            if args.filter_from:
                f.write(f"Filtered based on: {args.filter_from}\n")
            f.write("=" * 60 + "\n")
            total = sum(len(files) for files in results.values())
            f.write(f"Total files processed: {total}\n")
            for category, files in results.items():
                f.write(f"\n{category.upper()} ({len(files)} files):\n")
                for filepath in files:
                    f.write(f"  {filepath.relative_to(folder_path)}\n")
        print(f"\nResults saved to: {output_path}")


if __name__ == "__main__":
    main()
