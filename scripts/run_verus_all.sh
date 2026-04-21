# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

#
# run_verus_all.sh — Run Verus SMT benchmarks across multiple solvers.
#
# Executes the Verus benchmark suite (via scripts/run_verus.py) against four
# solver configurations in sequence:
#   1. Z3 4.15.4 (with Verus-specific tuning flags)
#   2. cvc5 1.3.3
#   3. Sundance-SMT using Z3 as the arithmetic backend
#   4. Sundance-SMT using its internal arithmetic solver
#
# Each run produces a results file (<solver>.out) and a log (<solver>.log).
# All runs use 16 parallel worker processes.
#
# Prerequisites:
#   - Z3, cvc5, and Sundance-SMT binaries built and on your system $PATH
#   - Python with scripts/run_verus.py available
#   - The benchmark directory (verus_benchmarks/) populated with .smt2 files
#

SMT_FOLDER="verus_benchmarks"
NUM_WORKERS=16
TIMEOUT=10

Z3_COMMAND="z3 auto_config=false smt.mbqi=false smt.case_split=3 smt.qi.eager_threshold=100.0 smt.delay_units=true smt.arith.solver=2 smt.arith.nl=false pi.enabled=false rewriter.sort_disjunctions=false"
CVC5_COMMAND="cvc5"
SUNDANCE_ARITH_Z3_COMMAND="sundance-smt"
SUNDANCE_ARITH_INTERNAL_COMMAND="sundance-smt --arithmetic internal"

# With proof files add to Sundance:
#
#   --proof=$CWD/proofs/filepath_basename.edrat

echo "*** Running z3"
python scripts/run_verus.py --solver-command "$Z3_COMMAND" --timeout $TIMEOUT -o z3-4.15.4.out -j $NUM_WORKERS "$SMT_FOLDER" 2>&1 | tee z3-4.15.4.log

echo "*** Running cvc5"
python scripts/run_verus.py --solver-command "$CVC5_COMMAND" --timeout $TIMEOUT -o cvc5-1.3.3.out -j $NUM_WORKERS "$SMT_FOLDER" 2>&1 | tee cvc5-1.3.3.log

echo "*** Running Sundance with z3 arithmetic"
python scripts/run_verus.py --solver-command "$SUNDANCE_ARITH_Z3_COMMAND" --timeout $TIMEOUT -o sundance-arith-z3.out -j $NUM_WORKERS "$SMT_FOLDER" 2>&1 | tee sundance-arith-z3.log

echo "*** Running Sundance with internal arithmetic"
python scripts/run_verus.py --solver-command "$SUNDANCE_ARITH_INTERNAL_COMMAND" --timeout $TIMEOUT -o sundance-arith-internal.out -j $NUM_WORKERS "$SMT_FOLDER" 2>&1 | tee sundance-arith-internal.log

