# Pure-CC benchmark collection runbook

## Background

Sundance is an SMT solver. Its propagator [src/cadical_propagator.rs](src/cadical_propagator.rs)
calls `process_assignment` (defined in
[src/egraphs/congruence_closure.rs](src/egraphs/congruence_closure.rs))
each time CaDiCaL assigns a literal. By design, when `process_assignment`
returns `Some(...)`, the cause is a congruence-closure conflict on the
current SAT trail.

A `--cc-log <DIR>` flag was added to the solver. When set, every CC
conflict triggers a dump of an SMT-LIB benchmark whose only assertions
are the equality / disequality literals on the current trail (the
solver's full sort + symbol declarations are emitted too). Any
`(distinct t1 ... tn)` literal on the trail is unfolded into the
pairwise `(not (= ti tj))` form so the dumped file uses only `=` and
`(not (=))`. Each dump is named `<benchmark_stem>_cc_<N>.smt2` where
`N` is a per-source counter.

Goal of the experiment: run the solver over a benchmark tree (here
`single_query/QF_UF/`) to harvest a large corpus of pure-CC benchmarks
suitable for stress-testing a standalone congruence-closure
implementation.

## What is in this repo

- The solver, plus the `--cc-log` plumbing.
- [scripts/run_cc_log_experiment.py](scripts/run_cc_log_experiment.py) —
  the driver script. It is **parallel** (`-j N`), **resumable** (writes
  `progress.json`), and tracks **timeouts** as a distinct status.

## What the remote agent needs to do

### 1. Locate the inputs

The corpus is **SMT-COMP single-query non-incremental QF_UF benchmarks**
(distributed via SMT-LIB / Zenodo). On the original machine it was at
`../single_query/QF_UF/`, alongside a sibling `single_query.tar.gz`
containing the unpacked SMT-COMP `.yml` + scrambled-`.smt2` pairs (the
local `rename_benchmarks.sh` script un-scrambles them back to
SMT-LIB-style paths). On the cluster the path will differ.

The folder structure mirrors SMT-LIB / SMT-COMP families:
`20170829-Rodin/`, `2018-Goel-hwbench/`, `20190906-CLEARSY/`, `NEQ/`,
`PEQ/`, `QG-classification/`, `SEQ/`, `eq_diamond/`. If the agent has
to fetch the corpus, the canonical sources are the SMT-LIB benchmark
repository (`https://smtlib.cs.uiowa.edu/`) and the SMT-COMP
single-query distributions on Zenodo. Either gives the same QF_UF
subtree.

#### Family provenance (so the agent can reason about which subset to prioritise)

- **20170829-Rodin** — Event-B / B-method proof obligations from the
  Rodin platform's SMT plug-in (Déharbe, Fontaine et al.). Set theory
  and arithmetic axiomatised over UF. Mostly unsat. Excluded from
  SMT-COMP 2018 due to `:named` term issues.
- **2018-Goel-hwbench** — Word-level IC3 / BMC queries over Verilog
  RTL from Goel & Sakallah's AVR model-checker. Wide datapath ops
  kept uninterpreted. Mix of sat / unsat.
- **20190906-CLEARSY** — Atelier B proof obligations from CLEARSY
  (French B-method company), translated via their `pptranspog`
  ppTrans encoder. Industrial SIL4 safety-critical software (e.g.
  CLEARSY Safety Platform for railway signalling). Predominantly
  unsat.
- **NEQ / PEQ / SEQ** — Randomly generated QF_UF formulas (in
  SMT-LIB since ~2005-2006), designed as equality-reasoning stress
  tests. NEQ biased toward disequalities, PEQ toward positive
  equalities, SEQ mixed. Filenames `NEQ041_size7.smt2`
  parameterise size. Mixed sat / unsat.
- **QG-classification** — 6,404 instances by Volker Sorge
  (Birmingham, Nov 2006). Each asks whether a finite quasi-group
  (Latin-square structure) of a given order with property
  `qg3`/`qg5`/etc. exists. Heavily axiomatic, one binary UF. Mix of
  sat / unsat.
- **eq_diamond** — 100 hand-crafted instances (April 2008).
  "Diamond" equality chains `x_i = a ∨ x_i = b` that look
  exponential but collapse under simple preprocessing. All unsat.
  Famous as a preprocessing-trick benchmark.

For the CC-dump experiment all of these are useful, but expect
**QG-classification** and **2018-Goel-hwbench** to dominate the
output volume (lots of equalities flowing through the trail), while
**eq_diamond** and **NEQ/PEQ/SEQ** mostly produce small dumps
quickly.

The agent should:

- ask the user / job-config for the path (e.g. `$BENCH_ROOT`), or
- search a known scratch / shared-data dir for a `QF_UF/` subtree.

The script accepts any directory; it recursively scans for `*.smt2`.

### 2. Build the solver

```bash
cargo build --release --no-default-features --features local-z3
```

The default features pull in `bundled-z3`, which builds Z3 from source
(slow, may fail in sandboxed environments). `local-z3` uses a
system-installed Z3 if present; fall back to `bundled-z3` only if no
system Z3 is available.

If the build fails on `quantifier.rs:457` with an `as_ref` error, pin
yaspar-ir to a known-good version:

```bash
cargo update -p yaspar-ir --precise 2.7.2
```

The release binary lands at `./target/release/sundance-smt`.

### 3. Run the experiment

```bash
python3 scripts/run_cc_log_experiment.py \
    --input-dir   "$BENCH_ROOT/QF_UF" \
    --output-dir  "$RESULTS/cc_log_run1" \
    --solver      ./target/release/sundance-smt \
    --timeout     120 \
    -j            16
```

Tune `-j` to roughly `cores / 2`: each worker spawns a solver process
that itself uses one core, but each can write thousands of small files,
which IO-saturates a node before it CPU-saturates. The script's default
is half of `os.cpu_count()`.

### 4. Resume after preemption / job re-queue

The cluster scheduler can SIGTERM the job at any time. The script
catches SIGINT and SIGTERM, stops dispatching new work, lets in-flight
workers finish (or hit `--timeout`), and flushes `progress.json` before
exiting.

To resume, **re-run the exact same command**. Benchmarks already in
`progress.json["done"]` or `progress.json["failed"]` are skipped.

If you suspect transient failures (e.g. a crashed node, OOM kill), pass
`--retry-failed` to re-run anything that previously timed out or
errored.

### 5. Job script template (Slurm)

```bash
#!/bin/bash
#SBATCH --job-name=sundance-cc-log
#SBATCH --time=12:00:00
#SBATCH --cpus-per-task=32
#SBATCH --mem=64G
#SBATCH --output=%x.%j.log
#SBATCH --signal=B:TERM@120     # SIGTERM 120s before time limit, so we flush

set -euo pipefail
cd "$SLURM_SUBMIT_DIR"

BENCH_ROOT=/path/to/shared/benchmarks   # FILL IN
RESULTS=/path/to/scratch/results        # FILL IN

python3 scripts/run_cc_log_experiment.py \
    --input-dir   "$BENCH_ROOT/QF_UF" \
    --output-dir  "$RESULTS/cc_log_run1" \
    --solver      ./target/release/sundance-smt \
    --timeout     120 \
    -j            16
```

The `--signal=B:TERM@120` line tells Slurm to send SIGTERM 120 seconds
before the wall-clock limit. The script's signal handler flushes
`progress.json` and lets workers finish or hit `--timeout`. To continue
the run, re-submit the same script (or use Slurm's `--requeue`); the
next invocation will skip everything already done.

### 6. Output layout

```text
$RESULTS/cc_log_run1/
├── progress.json              # source benchmark -> {status, elapsed, n_dumped, ...}
├── log.txt                    # one TSV line per processed benchmark
└── benchmarks/
    └── <relative path>/<stem>/
        ├── <stem>_cc_1.smt2
        ├── <stem>_cc_2.smt2
        └── ...                # one file per CC conflict
```

`progress.json["failed"]` entries carry `"status"` of either
`"timeout"` or `"error"`. To list only the timeouts:

```bash
python3 -c '
import json
p = json.load(open("'"$RESULTS"'/cc_log_run1/progress.json"))
for k, v in p["failed"].items():
    if v["status"] == "timeout":
        print(k, v["elapsed"], v["n_dumped"])
'
```

A timed-out benchmark is **not wasted**: any `*_cc_N.smt2` files dumped
before the timeout are kept and are usable. `n_dumped` in the progress
entry tells you how many.

### 7. Dump volume to plan for

Empirically, on `QF_UF/NEQ/NEQ004_size4.smt2` with `--timeout 3` and a
release build, ~7,900 dump files were produced in 3 seconds. With
`--timeout 120` per benchmark and ~10k benchmarks under `QF_UF/`,
**plan for tens to hundreds of millions of small files** in
`benchmarks/`. Mitigations:

- Point `--output-dir` at a fast scratch filesystem (Lustre / GPFS
  scratch, *not* a small home directory with inode quotas).
- Tar up subtrees of `benchmarks/` after the run and delete the loose
  files.
- If only a sample is needed, add an inner cap in
  [src/cadical_propagator.rs:`dump_cc_benchmark`](src/cadical_propagator.rs)
  (e.g. early-return once `cc_log_counter` exceeds some N) and
  rebuild — easy ~5-line change.
