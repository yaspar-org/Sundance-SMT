# Scripts

## run_verus.py

Runs an SMT solver on every `.smt2` file in a directory (recursively) and
categorizes each result as UNSAT, UNKNOWN, TIMEOUT, ERROR, or OTHER. Supports
parallel execution and optional filtering against a previous results file to
skip already-resolved benchmarks.

### Usage

```
python scripts/run_verus.py <folder> --solver-command "<command>" [options]
```

### Options

| Flag | Description |
|---|---|
| `--solver-command` | **(required)** Solver command to invoke on each file |
| `-j`, `--jobs` | Number of parallel worker processes (default: 4) |
| `--timeout` | Per-file timeout in seconds (default: 10) |
| `-v`, `--verbose` | Print detailed stdout/stderr for each file |
| `-o`, `--output` | Write categorized results to a file |
| `--filter-from` | Path to a previous results file; only re-run files that were absent or had OTHER results |

### Example

```bash
python scripts/run_verus.py verus_benchmarks/ \
  --solver-command "/path/to/z3 auto_config=false" \
  --timeout 10 -j 16 -o results.out 2>&1 | tee results.log
```

---

## run_verus_all.sh

Convenient wrapper that runs `run_verus.py` on four solver configurations in sequence:

1. **Z3 4.15.4** with Verus-specific tuning flags
2. **cvc5 1.3.3**
3. **Sundance-SMT** (Z3 arithmetic backend)
4. **Sundance-SMT** (internal arithmetic solver)

Each run produces a `.out` results file and a `.log` file. All runs use 16 parallel workers with a 10-second timeout.

### Usage

```bash
bash scripts/run_verus_all.sh
```

> **Note:** Edit the solver paths at the top of the script to match your environment before running.

---

## plot_cdf.py

Plots solve-time CDFs from one or more `run_verus.py` log files on a single
chart: x is the time budget, y is the number of benchmarks solved within it.
Lines without `->` are ignored; each series is labeled by the log's filename
stem. Requires `matplotlib` (e.g. `python3 -m venv .venv && .venv/bin/pip install matplotlib`).

### Usage

```bash
python scripts/plot_cdf.py z3-4.15.4.log cvc5-1.3.3.log \
  sundance-arith-z3.log sundance-arith-internal.log -o cdf.png
```

### Options

| Flag | Description |
|---|---|
| `-o`, `--output` | Output image path (default: `cdf.png`) |
| `--status` | Result status to count (default: `UNSAT`) |
| `--xmax` | X-axis upper bound in seconds (default: 10) |
| `--title` | Chart title |
| `--dpi` | Output resolution (default: 200) |

At most four logs can be plotted together. Per-log counts, medians, and maxima
are printed to stderr.
