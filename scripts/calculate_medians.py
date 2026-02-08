#!/usr/bin/env python3

import pandas as pd
import numpy as np

def calculate_medians_from_csv(file_path):
    """Calculate medians of all numerical columns in the CSV file."""
    
    # Read the CSV file
    df = pd.read_csv(file_path)
    
    # Print basic info about the dataset
    print(f"Dataset shape: {df.shape}")
    print(f"Total rows: {len(df)}")
    print("\nColumn types:")
    print(df.dtypes)
    
    # Identify numerical columns
    numerical_columns = []
    
    # These are the columns that should be treated as numerical
    potential_numerical_cols = [
        'parsing_time_s',
        'drat_trim_time_ms', 
        'theory_verification_time_ms',
        'clauses_used',
        'clauses_total',
        'theory_lemmas_used',
        'theory_lemmas_total'
    ]
    
    # Check which columns exist and are numerical
    for col in potential_numerical_cols:
        if col in df.columns:
            # Convert to numeric, coercing errors to NaN
            df[col] = pd.to_numeric(df[col], errors='coerce')
            numerical_columns.append(col)
    
    print(f"\nNumerical columns found: {numerical_columns}")
    
    # Calculate medians for each numerical column
    medians = {}
    
    print("\n" + "="*60)
    print("MEDIAN VALUES FOR NUMERICAL COLUMNS")
    print("="*60)
    
    for col in numerical_columns:
        # Remove NaN values for median calculation
        non_null_values = df[col].dropna()
        
        if len(non_null_values) > 0:
            median_val = non_null_values.median()
            medians[col] = median_val
            
            print(f"{col}:")
            print(f"  Count (non-null): {len(non_null_values)}")
            print(f"  Count (null): {df[col].isna().sum()}")
            print(f"  Median: {median_val}")
            print(f"  Min: {non_null_values.min()}")
            print(f"  Max: {non_null_values.max()}")
            print()
        else:
            print(f"{col}: No valid numerical data")
            medians[col] = None
    
    return medians

if __name__ == "__main__":
    file_path = "results_proofs/0108.csv"
    medians = calculate_medians_from_csv(file_path)
    
    print("="*60)
    print("SUMMARY - MEDIAN VALUES")
    print("="*60)
    for col, median_val in medians.items():
        if median_val is not None:
            print(f"{col}: {median_val}")
        else:
            print(f"{col}: No data")
