#!/usr/bin/env python3
"""
Script to process .edrat files with valido and extract verification results.
"""

import os
import sys
import subprocess
import re
import csv
from pathlib import Path
import argparse
import multiprocessing as mp
from functools import partial


def run_valido_command(file_path, output_dir="proof"):
    """
    Run the valido command on a given .edrat file and return the output.
    """
    cmd = [
        "valido",
        "--input-file", str(file_path),
        "--output-dir", output_dir,
        "--checker", "external",
        "--drat-trim", "../ArgAtsValido/drat-trim",
        "--solver", "z3"
    ]
    
    try:
        # print(" running ", " ".join(cmd))
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=300)
        return result.stdout + result.stderr, result.returncode
    except subprocess.TimeoutExpired:
        return "TIMEOUT", -1
    except Exception as e:
        return f"ERROR: {str(e)}", -1


def parse_verification_output(output_text):
    """
    Parse the valido output to extract verification results and metrics.
    """
    result = {
        'drat_success': False,
        'theory_verified': False,
        'parsing_time': None,
        'drat_trim_time': None,
        'theory_verification_time': None,
        'clauses_used': None,
        'clauses_total': None,
        'theory_lemmas_used': None,
        'theory_lemmas_total': None
    }
    
    # Check for success messages
    if "DRAT-Trim: SUCCESS ✅" in output_text:
        result['drat_success'] = True
    
    if "All theory lemmas were verified ✅" in output_text:
        result['theory_verified'] = True
    
    # Extract timing information
    parsing_match = re.search(r'Parsing time: ([\d.]+)s', output_text)
    if parsing_match:
        result['parsing_time'] = float(parsing_match.group(1))
    
    drat_trim_match = re.search(r'DRAT-Trim time: ([\d.]+)ms', output_text)
    if drat_trim_match:
        result['drat_trim_time'] = float(drat_trim_match.group(1))
    
    theory_time_match = re.search(r'Theory lemma verification time: ([\d.]+)ms', output_text)
    if theory_time_match:
        result['theory_verification_time'] = float(theory_time_match.group(1))
    
    # Extract unsat core information
    clauses_match = re.search(r'(\d+)/(\d+) clauses in the unsat core', output_text)
    if clauses_match:
        result['clauses_used'] = int(clauses_match.group(1))
        result['clauses_total'] = int(clauses_match.group(2))
    
    theory_lemmas_match = re.search(r'(\d+)/(\d+) theory lemmas in the unsat core', output_text)
    if theory_lemmas_match:
        result['theory_lemmas_used'] = int(theory_lemmas_match.group(1))
        result['theory_lemmas_total'] = int(theory_lemmas_match.group(2))
    
    return result


def process_single_edrat_file(file_path):
    """
    Process a single .edrat file with valido verification.
    Creates a unique output directory for each file: proof_outputs/{file_name_without_smt2}
    """
    file_path = Path(file_path)
    
    # Create unique output directory name based on file name without .smt2 extension
    # Handle cases like "filename.smt2.edrat" -> "filename" and "filename.edrat" -> "filename"
    base_name = file_path.stem  # Remove .edrat
    if base_name.endswith('.smt2'):
        base_name = base_name[:-5]  # Remove .smt2 suffix
    
    output_dir = Path("proof_outputs") / base_name
    
    # Create the output directory if it doesn't exist
    output_dir.mkdir(parents=True, exist_ok=True)
    
    print(f"Processing: {file_path.name} -> {output_dir}")
    
    # Run valido command
    output, return_code = run_valido_command(file_path, str(output_dir))
    
    if return_code == -1:
        # Error or timeout
        result_row = {
            'filename': file_path.name,
            'drat_success': False,
            'theory_verified': False,
            'overall_success': False,
            'parsing_time_s': None,
            'drat_trim_time_ms': None,
            'theory_verification_time_ms': None,
            'clauses_used': None,
            'clauses_total': None,
            'theory_lemmas_used': None,
            'theory_lemmas_total': None,
            'status': 'ERROR/TIMEOUT'
        }
    else:
        # Parse output
        parsed_result = parse_verification_output(output)
        
        overall_success = parsed_result['drat_success'] and parsed_result['theory_verified']
        
        result_row = {
            'filename': file_path.name,
            'drat_success': parsed_result['drat_success'],
            'theory_verified': parsed_result['theory_verified'],
            'overall_success': overall_success,
            'parsing_time_s': parsed_result['parsing_time'],
            'drat_trim_time_ms': parsed_result['drat_trim_time'],
            'theory_verification_time_ms': parsed_result['theory_verification_time'],
            'clauses_used': parsed_result['clauses_used'],
            'clauses_total': parsed_result['clauses_total'],
            'theory_lemmas_used': parsed_result['theory_lemmas_used'],
            'theory_lemmas_total': parsed_result['theory_lemmas_total'],
            'status': 'SUCCESS' if overall_success else 'FAILED'
        }
    
    # Print summary for this file
    if result_row['overall_success']:
        print(f"  ✅ SUCCESS - {file_path.name} - Parsing: {result_row['parsing_time_s']}s, "
              f"DRAT-Trim: {result_row['drat_trim_time_ms']}ms, "
              f"Theory: {result_row['theory_verification_time_ms']}ms")
    else:
        print(f"  ❌ FAILED - {file_path.name} - Status: {result_row['status']}")
    
    return result_row


def process_edrat_files(folder_path, output_csv="verification_results.csv", num_processes=None):
    """
    Process all .edrat files in the given folder in parallel and save results to CSV.
    """
    folder = Path(folder_path)
    
    if not folder.exists():
        print(f"Error: Folder {folder_path} does not exist")
        return
    
    # Find all .edrat files
    edrat_files = list(folder.glob("*.edrat"))
    
    if not edrat_files:
        print(f"No .edrat files found in {folder_path}")
        return
    
    print(f"Found {len(edrat_files)} .edrat files")
    
    # Determine number of processes to use
    if num_processes is None:
        num_processes = min(mp.cpu_count(), len(edrat_files))
    
    print(f"Using {num_processes} parallel processes")
    
    # CSV headers
    headers = [
        'filename',
        'drat_success',
        'theory_verified',
        'overall_success',
        'parsing_time_s',
        'drat_trim_time_ms',
        'theory_verification_time_ms',
        'clauses_used',
        'clauses_total',
        'theory_lemmas_used',
        'theory_lemmas_total',
        'status'
    ]
    
    # Create the main proof_outputs directory
    proof_outputs_dir = Path("proof_outputs")
    proof_outputs_dir.mkdir(exist_ok=True)
    
    # Process files in parallel
    print("\nProcessing files in parallel...")
    
    with mp.Pool(processes=num_processes) as pool:
        results = pool.map(process_single_edrat_file, edrat_files)
    
    # Write results to CSV
    with open(output_csv, 'w', newline='') as csvfile:
        writer = csv.DictWriter(csvfile, fieldnames=headers)
        writer.writeheader()
        writer.writerows(results)
    
    print(f"\nResults saved to {output_csv}")
    
    # Print summary statistics
    total_files = len(results)
    successful_files = sum(1 for r in results if r['overall_success'])
    
    print(f"\nSummary:")
    print(f"Total files processed: {total_files}")
    print(f"Successful verifications: {successful_files}")
    print(f"Failed verifications: {total_files - successful_files}")
    print(f"Success rate: {successful_files/total_files*100:.1f}%")


def main():
    parser = argparse.ArgumentParser(description='Process .edrat files with valido verification in parallel')
    parser.add_argument('folder', help='Path to folder containing .edrat files')
    parser.add_argument('-o', '--output', default='verification_results.csv',
                        help='Output CSV file (default: verification_results.csv)')
    parser.add_argument('-j', '--jobs', type=int, default=None,
                        help='Number of parallel processes (default: auto-detect based on CPU cores)')
    
    args = parser.parse_args()
    
    process_edrat_files(args.folder, args.output, args.jobs)


if __name__ == "__main__":
    main()
