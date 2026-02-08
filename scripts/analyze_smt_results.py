#!/usr/bin/env python3
"""
Script to analyze SMT files and results.

Gets the length of each .smt2 file in the specified folder (including nested subfolders),
finds the line before (check-sat), and combines this data with results from the results file.
Outputs everything to a CSV file.
"""

import os
import re
import csv
import sys
from pathlib import Path

def find_line_before_check_sat(file_path):
    """Find the line content before (check-sat) in an SMT2 file."""
    try:
        with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
            lines = f.readlines()
        
        # Find the line with (check-sat)
        for i, line in enumerate(lines):
            if '(check-sat)' in line.strip():
                # Return the previous line if it exists
                if i > 0:
                    return len(lines[i-1].strip())
                else:
                    return 0
        
        # If no (check-sat) found, return empty string
        return ""
    except Exception as e:
        print(f"Error reading {file_path}: {e}")
        return ""

def get_file_length(file_path):
    """Get the file size in bytes."""
    try:
        return os.path.getsize(file_path)
    except Exception as e:
        print(f"Error getting size of {file_path}: {e}")
        return 0

def find_smt_files(folder_path):
    """Recursively find all .smt2 files in the specified folder."""
    smt_files = []
    folder_path = Path(folder_path)
    
    for file_path in folder_path.rglob("*.smt2"):
        smt_files.append(str(file_path.relative_to(folder_path)))
    
    return smt_files

def parse_results_file(results_file_path):
    """Parse the results file to extract filename, result, and time."""
    results = {}
    
    try:
        with open(results_file_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # Pattern to match lines like: [1/3763] atmosphere/define.3.smt2 -> UNSAT [0.02s]
        pattern = r'\[\d+/\d+\] (.+?\.smt2) -> (\w+) \[([0-9.]+)s\]'
        matches = re.findall(pattern, content)
        
        for file_path, result, time_str in matches:
            results[file_path] = {
                'result': result,
                'time': float(time_str)
            }
        
        print(f"Parsed {len(results)} results from results file")
        
    except Exception as e:
        print(f"Error parsing results file {results_file_path}: {e}")
    
    return results

def main():
    if len(sys.argv) != 3:
        print("Usage: python analyze_smt_results.py <smt_folder> <results_file>")
        print("Example: python analyze_smt_results.py 20241211-verus-modified11 results/results_0120proofsnelsonoppenandfasterinsertpred_long.txt")
        sys.exit(1)
    
    smt_folder = sys.argv[1]
    results_file = sys.argv[2]
    
    print(f"Analyzing SMT files in: {smt_folder}")
    print(f"Using results from: {results_file}")
    
    # Find all .smt2 files
    smt_files = find_smt_files(smt_folder)
    print(f"Found {len(smt_files)} .smt2 files")
    
    # Parse results file
    results_data = parse_results_file(results_file)
    
    # Prepare CSV data
    csv_data = []
    
    for i, rel_file_path in enumerate(smt_files, 1):
        if i % 100 == 0:
            print(f"Processing file {i}/{len(smt_files)}: {rel_file_path}")
        
        # Get full path for file operations
        full_file_path = os.path.join(smt_folder, rel_file_path)
        
        # Get file length
        file_length = get_file_length(full_file_path)
        
        # Get line before (check-sat)
        line_before_check_sat = find_line_before_check_sat(full_file_path)
        
        # Get result data if available
        result = results_data.get(rel_file_path, {}).get('result', 'NOT_FOUND')
        time_taken = results_data.get(rel_file_path, {}).get('time', -1)
        
        csv_data.append({
            'file_path': rel_file_path,
            'file_length_bytes': file_length,
            'line_before_check_sat': line_before_check_sat,
            'result': result,
            'time_seconds': time_taken
        })
    
    # Write to CSV
    output_file = 'smt_analysis_results.csv'
    
    with open(output_file, 'w', newline='', encoding='utf-8') as csvfile:
        fieldnames = ['file_path', 'file_length_bytes', 'line_before_check_sat', 'result', 'time_seconds']
        writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
        
        writer.writeheader()
        for row in csv_data:
            writer.writerow(row)
    
    print(f"\nAnalysis complete! Results written to {output_file}")
    print(f"Total files processed: {len(csv_data)}")
    
    # Print some statistics
    results_found = sum(1 for row in csv_data if row['result'] != 'NOT_FOUND')
    print(f"Files with results data: {results_found}")
    print(f"Files without results data: {len(csv_data) - results_found}")

if __name__ == "__main__":
    main()
