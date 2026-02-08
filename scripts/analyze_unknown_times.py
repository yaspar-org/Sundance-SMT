#!/usr/bin/env python3
"""
Script to analyze UNKNOWN results from SMT solver output files and create log scale graphs.
"""

import re
import sys
import argparse
import matplotlib.pyplot as plt
import numpy as np
from pathlib import Path
from typing import List, Tuple, Dict
import seaborn as sns

def parse_results_file(filepath: Path) -> List[Tuple[str, str, float]]:
    """
    Parse a results file and extract entries with timing information.
    
    Returns:
        List of tuples: (filename, result_status, time_in_seconds)
    """
    entries = []
    
    # Pattern to match lines like: [1/3763] filename -> RESULT [4.26s]
    pattern = r'\[\d+/\d+\]\s+(.+?)\s+->\s+(\w+)\s+\[([0-9.]+)s\]'
    
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            for line_num, line in enumerate(f, 1):
                line = line.strip()
                if not line:
                    continue
                    
                match = re.match(pattern, line)
                if match:
                    filename = match.group(1)
                    result_status = match.group(2)
                    time_seconds = float(match.group(3))
                    entries.append((filename, result_status, time_seconds))
                else:
                    # Skip summary lines and other non-result lines
                    if not line.startswith('Processing') and not line.startswith('=') and not line.startswith('SUMMARY') and not line.startswith('Total files') and not line.startswith('  -'):
                        print(f"Warning: Could not parse line {line_num}: {line}")
    
    except FileNotFoundError:
        print(f"Error: File not found: {filepath}")
        sys.exit(1)
    except Exception as e:
        print(f"Error reading {filepath}: {e}")
        sys.exit(1)
    
    return entries

def filter_by_status(entries: List[Tuple[str, str, float]], status: str) -> List[Tuple[str, str, float]]:
    """Filter entries by result status (e.g., 'UNKNOWN', 'UNSAT', etc.)"""
    return [entry for entry in entries if entry[1] == status]

def create_log_histogram(times: List[float], title: str, output_file: str = None):
    """Create a log scale histogram of times"""
    if not times:
        print(f"No times to plot for {title}")
        return
    
    plt.figure(figsize=(12, 8))
    
    # Create log-scaled bins
    min_time = min(times)
    max_time = max(times)
    
    # Use log space for bins
    log_bins = np.logspace(np.log10(max(min_time, 0.01)), np.log10(max_time), 50)
    
    plt.hist(times, bins=log_bins, alpha=0.7, edgecolor='black')
    plt.xscale('log')
    plt.xlabel('Time (seconds, log scale)')
    plt.ylabel('Count')
    plt.title(f'{title}\nTotal entries: {len(times)}')
    plt.grid(True, alpha=0.3)
    
    # Add some statistics
    mean_time = np.mean(times)
    median_time = np.median(times)
    
    plt.axvline(mean_time, color='red', linestyle='--', alpha=0.8, label=f'Mean: {mean_time:.2f}s')
    plt.axvline(median_time, color='orange', linestyle='--', alpha=0.8, label=f'Median: {median_time:.2f}s')
    plt.legend()
    
    plt.tight_layout()
    
    if output_file:
        plt.savefig(output_file, dpi=300, bbox_inches='tight')
        print(f"Saved histogram to: {output_file}")
    else:
        plt.show()

def create_scatter_plot(entries: List[Tuple[str, str, float]], title: str, output_file: str = None):
    """Create a scatter plot showing times in order of processing"""
    if not entries:
        print(f"No entries to plot for {title}")
        return
        
    times = [entry[2] for entry in entries]
    indices = list(range(len(times)))
    
    plt.figure(figsize=(12, 8))
    plt.scatter(indices, times, alpha=0.6, s=20)
    plt.yscale('log')
    plt.xlabel('Entry Index (processing order)')
    plt.ylabel('Time (seconds, log scale)')
    plt.title(f'{title} - Time Distribution\nTotal entries: {len(times)}')
    plt.grid(True, alpha=0.3)
    
    plt.tight_layout()
    
    if output_file:
        plt.savefig(output_file, dpi=300, bbox_inches='tight')
        print(f"Saved scatter plot to: {output_file}")
    else:
        plt.show()

def create_cdf_plot(times: List[float], title: str, output_file: str = None, label: str = None):
    """Create a cumulative distribution function (CDF) plot showing total counts"""
    if not times:
        print(f"No times to plot for {title}")
        return
    
    # Sort times for CDF
    sorted_times = np.sort(times)
    
    # Calculate CDF values (total count <= x)
    n = len(sorted_times)
    y = np.arange(1, n + 1)
    
    plt.plot(sorted_times, y, linewidth=2, alpha=0.8, label=label)
    return sorted_times, y

def create_multi_cdf_plot(datasets: List[Tuple[List[float], str]], title: str, output_file: str = None):
    """Create a CDF plot with multiple datasets"""
    plt.figure(figsize=(12, 8))
    
    colors = ['blue', 'red', 'green', 'orange', 'purple']
    
    for i, (times, label) in enumerate(datasets):
        if not times:
            print(f"No times for {label}")
            continue
            
        # Sort times for CDF
        sorted_times = np.sort(times)
        
        # Calculate CDF values (total count <= x)
        n = len(sorted_times)
        y = np.arange(1, n + 1)
        
        color = colors[i % len(colors)]
        plt.plot(sorted_times, y, linewidth=2, alpha=0.8, label=f'{label} (n={n})', color=color)
    
    plt.xscale('log')
    plt.xlabel('Time (seconds, log scale)')
    plt.ylabel('Total Count')
    plt.title(f'{title} - Cumulative Distribution Comparison')
    plt.grid(True, alpha=0.3)
    plt.legend()
    
    plt.tight_layout()
    
    if output_file:
        plt.savefig(output_file, dpi=300, bbox_inches='tight')
        print(f"Saved CDF comparison plot to: {output_file}")
    else:
        plt.show()

def print_statistics(entries: List[Tuple[str, str, float]], status: str):
    """Print statistics for the given entries"""
    if not entries:
        print(f"No {status} entries found.")
        return
    
    times = [entry[2] for entry in entries]
    
    print(f"\n{status} Results Statistics:")
    print(f"  Total entries: {len(entries)}")
    print(f"  Mean time: {np.mean(times):.2f}s")
    print(f"  Median time: {np.median(times):.2f}s")
    print(f"  Min time: {min(times):.2f}s")
    print(f"  Max time: {max(times):.2f}s")
    print(f"  Std deviation: {np.std(times):.2f}s")
    
    # Show some percentiles
    percentiles = [25, 75, 90, 95, 99]
    for p in percentiles:
        print(f"  {p}th percentile: {np.percentile(times, p):.2f}s")

def main():
    parser = argparse.ArgumentParser(description='Analyze SMT solver results and create log scale graphs')
    parser.add_argument('files', nargs='+', help='Results files to analyze')
    parser.add_argument('--status', default='UNKNOWN', 
                        choices=['UNKNOWN', 'UNSAT', 'TIMEOUT', 'OTHER', 'ERROR'],
                        help='Result status to analyze (default: UNKNOWN)')
    parser.add_argument('--output-dir', type=str, help='Directory to save plots (if not specified, plots are shown)')
    parser.add_argument('--histogram', action='store_true', default=True, help='Create histogram (default)')
    parser.add_argument('--scatter', action='store_true', help='Create scatter plot')
    parser.add_argument('--cdf', action='store_true', help='Create CDF plot')
    parser.add_argument('--compare', action='store_true', help='Compare multiple solvers (requires specific file names)')
    parser.add_argument('--no-histogram', action='store_true', help='Skip histogram')
    parser.add_argument('--stats-only', action='store_true', help='Only print statistics, no plots')
    
    args = parser.parse_args()
    
    # Set up matplotlib style
    plt.style.use('default')
    sns.set_palette("husl")
    
    # Check if this is a comparison mode with specific solvers
    if args.compare or len(args.files) > 1:
        datasets = []
        
        # Map file names to solver labels
        file_labels = {
            'results/results_0107_withproofs.txt': 'Sundance',
            'results/z3_1130.txt': 'Z3', 
            'results/cvc5_1130.txt': 'CVC5'
        }
        
        for file_path in args.files:
            path = Path(file_path)
            if not path.exists():
                print(f"Warning: File does not exist: {path}")
                continue
                
            print(f"Parsing {path}...")
            entries = parse_results_file(path)
            filtered_entries = filter_by_status(entries, args.status)
            times = [entry[2] for entry in filtered_entries]
            
            # Get label for this file
            label = file_labels.get(str(path), path.stem)
            
            print(f"  Found {len(entries)} total entries, {len(filtered_entries)} {args.status} entries")
            print_statistics(filtered_entries, f"{label} {args.status}")
            
            if times:
                datasets.append((times, label))
        
        if not datasets:
            print("No data found for comparison.")
            return
            
        if args.stats_only:
            return
        
        # Create comparison CDF plot
        if args.cdf:
            output_cdf = None
            if args.output_dir:
                output_dir = Path(args.output_dir)
                output_dir.mkdir(exist_ok=True)
                output_cdf = output_dir / f"{args.status.lower()}_comparison_cdf.png"
            
            create_multi_cdf_plot(datasets, f"{args.status} Results", str(output_cdf) if output_cdf else None)
        
        return
    
    # Single file mode (original functionality)
    all_entries = []
    
    # Parse all input files
    for file_path in args.files:
        path = Path(file_path)
        if not path.exists():
            print(f"Warning: File does not exist: {path}")
            continue
            
        print(f"Parsing {path}...")
        entries = parse_results_file(path)
        all_entries.extend(entries)
        print(f"  Found {len(entries)} total entries")
    
    if not all_entries:
        print("No entries found in any files.")
        return
    
    # Filter by requested status
    filtered_entries = filter_by_status(all_entries, args.status)
    
    # Print statistics
    print_statistics(filtered_entries, args.status)
    
    if args.stats_only:
        return
    
    if not filtered_entries:
        print(f"No {args.status} entries found to plot.")
        return
    
    # Prepare output file names if output directory is specified
    output_hist = None
    output_scatter = None
    output_cdf = None
    if args.output_dir:
        output_dir = Path(args.output_dir)
        output_dir.mkdir(exist_ok=True)
        output_hist = output_dir / f"{args.status.lower()}_times_histogram.png"
        output_scatter = output_dir / f"{args.status.lower()}_times_scatter.png"
        output_cdf = output_dir / f"{args.status.lower()}_times_cdf.png"
    
    # Create plots
    times = [entry[2] for entry in filtered_entries]
    
    if args.histogram and not args.no_histogram:
        title = f"{args.status} Results - Time Histogram"
        create_log_histogram(times, title, str(output_hist) if output_hist else None)
    
    if args.scatter:
        title = f"{args.status} Results"
        create_scatter_plot(filtered_entries, title, str(output_scatter) if output_scatter else None)
    
    if args.cdf:
        plt.figure(figsize=(12, 8))
        sorted_times = np.sort(times)
        n = len(sorted_times)
        y = np.arange(1, n + 1)
        
        plt.plot(sorted_times, y, linewidth=2, alpha=0.8)
        plt.xscale('log')
        plt.xlabel('Time (seconds, log scale)')
        plt.ylabel('Total Count')
        plt.title(f'{args.status} Results - Cumulative Distribution\nTotal entries: {len(times)}')
        plt.grid(True, alpha=0.3)
        
        plt.tight_layout()
        
        if output_cdf:
            plt.savefig(str(output_cdf), dpi=300, bbox_inches='tight')
            print(f"Saved CDF plot to: {output_cdf}")
        else:
            plt.show()
    
    # Print some examples of longest times
    sorted_entries = sorted(filtered_entries, key=lambda x: x[2], reverse=True)
    print(f"\nTop 10 longest {args.status} times:")
    for i, (filename, status, time) in enumerate(sorted_entries[:10], 1):
        print(f"  {i}. {filename}: {time:.2f}s")

if __name__ == "__main__":
    main()
