#!/usr/bin/env python3
"""
Script to compare two SMT solver result files and identify differences.
A problem is considered "solved" if the result is UNSAT.
"""

import re
import sys
from typing import Dict, Set, Tuple
from pathlib import Path


def parse_result_file(file_path: str) -> Dict[str, str]:
    """
    Parse a result file and extract filename -> result mapping.
    
    Args:
        file_path: Path to the result file
        
    Returns:
        Dictionary mapping filename to result (UNSAT, UNKNOWN, TIMEOUT, etc.)
    """
    results = {}
    
    with open(file_path, 'r') as f:
        for line in f:
            line = line.strip()
            # Look for lines with pattern: [number/total] filename -> RESULT [optional timing]
            # Extract just the result status, ignoring any timing information
            match = re.match(r'\[\d+/\d+\] (.+?) -> ([A-Z]+)', line)
            if match:
                filepath = match.group(1)
                result = match.group(2)
                results[filepath] = result
                
    return results


def find_differences(results1: Dict[str, str], results2: Dict[str, str]) -> Tuple[Set[Tuple[str, str]], Set[Tuple[str, str]]]:
    """
    Find problems solved by one solver but not the other.
    
    Args:
        results1: Results from first solver
        results2: Results from second solver
        
    Returns:
        Tuple of (solved_by_1_not_2, solved_by_2_not_1)
    """
    # Get common files (files present in both result sets)
    common_files = set(results1.keys()) & set(results2.keys())
    
    solved_by_1_not_2 = set()
    solved_by_2_not_1 = set()
    
    for filepath in common_files:
        result1 = results1[filepath]
        result2 = results2[filepath]
        
        # A problem is "solved" if result is UNSAT
        solved_1 = (result1 == 'UNSAT')
        solved_2 = (result2 == 'UNSAT')
        
        if solved_1 and not solved_2:
            solved_by_1_not_2.add((filepath, result2))
        elif solved_2 and not solved_1:
            solved_by_2_not_1.add((filepath, result1))
    
    return solved_by_1_not_2, solved_by_2_not_1


def print_results(file1: str, file2: str, solved_by_1_not_2: Set[Tuple[str, str]], solved_by_2_not_1: Set[Tuple[str, str]]):
    """
    Print the comparison results.
    """
    print("=" * 80)
    print(f"COMPARISON RESULTS")
    print("=" * 80)
    print(f"File 1: {file1}")
    print(f"File 2: {file2}")
    print()
    
    print(f"Problems solved by File 1 but NOT by File 2: {len(solved_by_1_not_2)}")
    if solved_by_1_not_2:
        print("Files:")
        for (filepath, result2) in sorted(solved_by_1_not_2):
            print(f"  - {filepath} [{result2}]")
    print()
    
    print(f"Problems solved by File 2 but NOT by File 1: {len(solved_by_2_not_1)}")
    if solved_by_2_not_1:
        print("Files:")
        for (filepath, result1) in sorted(solved_by_2_not_1):
            print(f"  - {filepath} [{result1}]")
    print()
    
    print("SUMMARY:")
    print(f"  {Path(file1).name} unique solves: {len(solved_by_1_not_2)}")
    print(f"  {Path(file2).name} unique solves: {len(solved_by_2_not_1)}")


def main():
    """Main function to compare two result files."""
    if len(sys.argv) != 3:
        print("Usage: python compare_smt_results.py <file1> <file2>")
        print()
        print("Example:")
        print("  python compare_smt_results.py results/results_1129_3.txt results/z3_1130_noarith.txt")
        sys.exit(1)
    
    file1 = sys.argv[1]
    file2 = sys.argv[2]
    
    # Check if files exist
    if not Path(file1).exists():
        print(f"Error: File '{file1}' not found")
        sys.exit(1)
    if not Path(file2).exists():
        print(f"Error: File '{file2}' not found")
        sys.exit(1)
    
    print("Parsing result files...")
    results1 = parse_result_file(file1)
    results2 = parse_result_file(file2)
    
    print(f"File 1 ({Path(file1).name}): {len(results1)} results")
    print(f"File 2 ({Path(file2).name}): {len(results2)} results")
    
    # Find common files
    common_files = set(results1.keys()) & set(results2.keys())
    print(f"Common files: {len(common_files)}")
    
    if len(common_files) == 0:
        print("Warning: No common files found between the two result sets!")
        return
    
    # Find differences
    solved_by_1_not_2, solved_by_2_not_1 = find_differences(results1, results2)
    
    # Print results
    print_results(file1, file2, solved_by_1_not_2, solved_by_2_not_1)


if __name__ == "__main__":
    main()
