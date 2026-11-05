# Replacing CaDiCaL with a Tableau Backend

Revision 2 incorporates an adversarial review of revision 1. Review findings
are cited as **[R#]**.

## Motivation

1. **Relevancy and SAT-level GC.** A tableau that branches only on open
   (unsatisfied) formulas leaves irrelevant atoms unassigned. Branch-scoped
   lemmas can disappear when their branch closes.
2. **Simplicity.** A native Rust backend can eventually replace the CaDiCaL C++
   build, the pinned fork and the `elevate` requirement. This needs Phase 5;
   reusing `cadical_sys` types alone does not remove the C++ build **[R9]**.
3. **Modularity (paper).** The same `CustomExternalPropagator` drives two
   search engines with different tradeoffs.

Honest scope of the claims:
- Phases 0–1 change no theory code.
- Phases 2–3 do touch quantifier and datatype code (relevance-driven term
  insertion, epoch-scoped dedup). The paper should say this **[R8, R13]**.

## Interfaces (cadical-sys rev a93337a, CaDiCaL 3.0.1)

- `ExternalPropagator`, `ProofTracer`, `Terminator` and `Status` are plain,
  object-safe Rust traits and types, so a Rust solver can drive them directly.
- The CaDiCaL methods Sundance uses:
  - `new`
  - `set("elevate", _)`
  - `connect_proof_tracer1`
  - `connect_terminator`
  - `connect_external_propagator`
  - `clause6`
  - `solve`
  - `disconnect_proof_tracer1`
  - `add_observed_var` (from the propagator)

**Observed variables [R6].** The propagator's only solver access is
`add_observed_var` at `cadical_propagator.rs:239`. It is called from
`sync_new_vars` *inside* callbacks.
- A raw `*mut` into a Rust tableau that is executing a callback would be aliasing UB.
- The tableau must not simply observe everything: notifying a variable with no
  term panics in `get_term_from_lit`.
- Fix: replace the pointer with a sink. CaDiCaL keeps the pointer; the tableau
  gets a shared queue that it drains after each callback.

**Proof tracer [R6, R11].** `SMTProofTracer` ignores ids, antecedents and
witnesses.
- The tableau must call `add_original_clause` exactly once for every clause it
  receives (input and external), because each call consumes a registration
  made by the caller.
- Derived clauses go through `add_derived_clause`.
- Never call `weaken_minus`, `finalize_clause`, assumptions or constraints;
  these panic.
- The tracer is borrowed per call, never while a propagator callback runs.

## Callback contract the tableau must reproduce [R1, R3, R10]

1. **Propagation.** After each fixpoint: notify pending observed assignments,
   call `cb_propagate`, then loop on `cb_has_external_clause`. Repeat
   whenever a clause changes the trail.
2. **Decision.** Notify pending assignments, call `notify_new_decision_level`,
   assign the decision, and notify it at the new level. `cb_decide` is
   consulted before every decision and must return an unassigned literal or 0.
3. **Root level.** Level-0 literals are notified before the first decision.
   `notify_backtrack(k)` requires k < the current level.
4. **Model check.** It runs only when every variable is assigned (including
   fresh variables from lemmas) and every clause is satisfied.
   - All model literals are notified first.
   - The model holds the observed variables in increasing index order.
   - If the call returns false, add the queued clauses.
   - A conflicting clause goes to conflict handling.
   - A clause that changes the trail or adds unassigned variables sends search back.
   - **No clause, or only clauses already satisfied: the model is accepted.**
     A false return alone never closes a branch.
5. **Out-of-order assignments (replaces `elevate`).** A lemma that is unit
   under literals at levels ≤ j is assigned at level j *without backtracking*.
   - On `notify_backtrack(m)`, literals with level ≤ m are kept.
   - Kept literals that were notified at a level > m are notified again after
     the backtrack (CaDiCaL does the same; the propagator tolerates it).
   - This avoids a restart for every root-unit QI instance.
   - Missed lower implications are allowed. They cost efficiency, not
     correctness, as long as watch invariants hold.
6. **Conflicts without learning [R4].** For a falsified clause C:
   - Let k be the maximum level in C. Backtrack to k if k is below the current level.
   - If exactly one literal of C is at level k: backtrack to the
     second-highest level j and assert that literal there, with reason C.
   - Otherwise, close the branch: let D be the decision levels the conflict
     depends on and k' = max(D). Backtrack to k'-1 and assign the negation of
     decision k' at level max(D \ {k'}), recording D \ {k'} as its
     dependencies (a "flip").
   - Termination: every conflict lexicographically increases the vector of
     per-level assignment counts.
7. **No restarts in Phase 1 [R5].** Without learning, restarts throw away the Boolean work.

## Status (branch `tableau-backend`)

- **Phase 0 done.**
  - `ObservedSink` replaces the propagator's solver pointer.
  - `--sat-backend {cadical,tableau}` selects the backend.
  - `SUNDANCE_SAT_BACKEND` sets it in the regression harness.
  - CaDiCaL results are unchanged: 433 correct / 0 incorrect / 7 timeouts.
- **Phase 1 implemented** (`src/sat_tableau.rs`).
  - Regression: 433 correct / 0 incorrect / 7 timeouts. The timeout sets
    differ: the tableau solves `inductive_disequality_no_cycle_sat` and times
    out on `eq_diamond17`.
  - Unit tests cross-check against brute force on 20k random CNFs, with
    hidden clauses revealed both lazily and eagerly.
  - Addition to the conflict rule: **dependency-directed backjumping**.
    - A flip records the decision levels its closure depends on (computed
      through the implication graph).
    - It is asserted at the highest of those levels, not at k-1.
    - Without this, `arithmetic/subtraction` thrashed: about 1M decisions,
      with no lemmas after 70 model checks.
    - This is the standard tableau technique and needs no learned clauses.
- **Slowdown diagnosis (UFDTLIA, controlled A/B on the same binary).**
  - 128 files regressed against the baseline run. The baseline came from
    another branch with QI-dedup changes, so I re-ran both backends from one
    binary. In that A/B, 81 timeouts and 4 wrong `unknown` answers were
    caused by the tableau. The fixes, in order:
  1. **Chronological asserts.** The assert rule backjumped to the
     second-highest level, often hundreds of levels down, and replayed every
     decision. Each replayed notification made Sundance re-send datatype
     axioms (more than 600k duplicate, already-satisfied clauses on one
     file). Now it backtracks only to k-1 and assigns out of order, as
     CaDiCaL's chrono mode does.
  2. **Duplicate lemmas merged** through a clause index. A resent lemma
     re-settles the existing copy, which also repairs missed implications.
  3. **Triggered-clause branching.** Branching on the first unassigned
     literal of *any* open clause expanded inactive Tseitin definitions,
     branching on atoms one at a time. It also set the leftover phase that
     produced the wrong `unknown`s, where QI was incomplete under the
     tableau's models.
     - Now only *triggered* clauses (open, with a false literal) are
       expanded, oldest first, with true phase for leftover variables.
     - Occurrence lists plus a min-heap agenda replace a full scan, which had
       taken 48% of the time.
     - The order matters: LIFO expansion was 3–10x worse.
  - Effect on eq_diamond16: 9.1s → 2.0s (CaDiCaL 2.6s).
  - Effect on the regressed set: 81 → 28 timeouts. On the slow set the
    tableau is now 1.9x CaDiCaL, with no timeouts. Regression suite:
    433/0/7, the same timeout set as CaDiCaL.
- **Full UFDTLIA A/B** (3,763 files, same binary, 60s, 96 parallel):

  | Backend | unsat | timeout | unknown |
  |---|---|---|---|
  | Tableau | 3163 | 590 | 9 |
  | CaDiCaL | 3154 | 594 | 14 |

  - On the 3,109 files both solve: total time is 1.17x CaDiCaL, median 1.07x.
  - **What remains** (the 45 files only CaDiCaL solves):
    - Instantiation and theory-conflict counts match CaDiCaL.
    - The tableau does 10–40x more backtracks. Egraph merges, `backtrack_to`
      and per-level `BTreeMap` clones dominate the profile; the tableau's
      own code is about 3%. This is the cost of no learning.
    - Nearly all resent lemmas are already satisfied (datatype axioms are
      resent on re-notification), so there are no missed implications.
  - Tried and dropped: decision nogood recording on closure. On those 45
    files it gained 6 and lost 4.
  - Remaining options:
    - cheaper egraph backtracking, which helps both backends
    - Sundance not re-sending satisfied axioms
    - resolution-based learning, as an ablation
- Proofs: the tableau reports clauses to the tracer but does not yet emit
  derived steps. `--proof` with `--sat-backend tableau` is not yet a checkable
  refutation.
- Next: Phase 2a (partial models), then proofs (Phase 4.1) so the tableau is usable with `--proof`.

## Phases

### Phase 0: Backend switch (no behavior change)
1. Replace `solver: *mut CaDiCal` with an `ObservedSink` enum (`Cadical(*mut CaDiCal)` or `Queue(Rc<RefCell<Vec<i32>>>)`).
2. Add `--sat-backend {cadical,tableau}` to `config.rs`. Thread it through `cdcl_decision_procedure`.
3. Add a `SUNDANCE_SAT_BACKEND` env var to `tests/regression_test.rs`, like `SUNDANCE_ARITHMETIC` **[R12]**.
4. **Exit:** with `cadical`, regression results are identical, including the timeout count.

### Phase 1: Clausal tableau (`src/sat_tableau.rs`; `tableau` is taken [R13])
1. Clause DB with two watched literals. The trail records per-literal levels and reasons (clause, flip or decision).
2. Branching in tableau style: pick the first unassigned literal of an open
   (unsatisfied) clause, unless `cb_decide` returns a literal. If every clause
   is satisfied, assign the remaining variables so the model is total (as the
   contract requires).
3. Implement the full callback contract above: out-of-order units, the conflict rule, the model-check loop.
4. Terminator polling. Proofs: `add_original_clause` only.
5. **Exit:**
   - Every SAT/UNSAT answer agrees with CaDiCaL on the regression suite. A
     disagreement is a bug; a timeout is recorded.
   - Report the timeout counts.

### Phase 2a: Partial models over clauses [R8]
1. Saturate when every clause is satisfied, instead of assigning everything.
2. Audit the code paths that assume total models:
   - the arithmetic model path (`check_integer_constraints_satisfiable`, Z3 incremental)
   - Nelson-Oppen probing
   - the datatype occurs check and `generate_deferred_tester_clauses` (they scan all `term_constructors`)
   - QI
   - `--trail-out`
3. Soundness requires every input and external clause to be satisfied by
   *assigned* literals. Atoms in lemmas are never treated as irrelevant.
4. Measure the effect before building anything non-clausal.

### Phase 2b: Structural input [R2]
1. `sat_interface::Formula` is CNF, so it carries no structure. Instead, emit
   an And/Or/Not **DAG** over variable ids as a side output of
   `cnf_nnf_tseitin` (`cnf.rs:278-334`). It must be a DAG because the Tseitin
   cache shares variables across assertions and instances.
2. Hand the DAG to the tableau in `cdcl.rs` before the propagator takes `&mut solver_state`.
3. Expand only the true/false subformulas on the branch. With an Or that is
   true, only one child is needed.
4. External clauses (QI bodies, theory lemmas, `boolean_dt_constraints`) stay
   CNF. Optionally, instance bodies could later be passed as DAGs.
5. **Theory-side relevancy (separate item):** relevance-driven egraph term
   insertion (`main.rs:128` currently inserts every assertion) and
   relevance-filtered datatype scans. Known pitfall: NNF destroys iff
   structure (`qi_gc_summary.md`).

### Phase 3: Lemma GC [R7]
1. `is_forgettable` in IPASIR-UP means "redundant; the solver may delete it",
   not "branch-local". Deleting without re-derivation loses completeness today:
   - `added_instantiations` is never cleared
   - `skolemized` is permanent
   - the Tseitin cache does not re-emit definitions
2. Prerequisites, on both backends:
   - scope the instantiation dedup by epoch/level
   - keep Tseitin definitions, trichotomy and tester clauses global
   - mark only the guarded instance clause as forgettable (as on the qi-gc branch)
3. Tableau: forgettable lemmas live on the branch that created them and are dropped when it closes.
4. Measure how often dropped instances are re-derived.

### Phase 4: Proofs and evaluation
1. When both children of a branch point close, emit the negation of the branch as `add_derived_clause` (RUP). Finish with the empty clause.
   - This works only if every alpha step is unit-propagation-derivable from recorded clauses **[R11]**.
   - Phase 2b alpha steps must use the Tseitin definitions that `cdcl.rs` records.
2. Check the proofs with the existing checker, on both backends.
3. Experiments:
   - Configurations: CaDiCaL / clausal tableau / plus partial models / plus structure / plus GC.
   - Benchmark split: quantifier-heavy (Verus-style) vs. Boolean-heavy.
   - Metrics: runtime, instances, theory calls, memory.
   - Modularity evidence: the actual diff, split into backend glue and theory changes.

### Phase 5: Drop the C++ dependency (optional, for motivation 2)
1. Copy `ExternalPropagator`, `ProofTracer`, `Terminator` and `Status` into a Sundance `sat_api` module.
2. Put the CaDiCaL backend behind a cargo feature.
3. The cxx panic workaround stays as long as CaDiCaL is a backend.

## Risks
- **No propositional learning.** Boolean-heavy benchmarks may time out. Report
  this as a measured tradeoff; learning can be an ablation.
- **Out-of-order trail.** Subtle invariants. Use debug assertions and a brute-force cross-check on small CNFs.
- **Clause scans.** Open-clause selection by scanning is O(#clauses) per decision. Optimize only if profiling shows it matters.
- **Proof volume.** Tree-shaped refutations can be large; check eDRAT sizes early.
