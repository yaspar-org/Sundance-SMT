# Formula-Level Tableau

Revision 2 incorporates an adversarial review of revision 1. Findings are
cited as **[B#]** (blocker), **[M#]** (major) and **[m]** (minor).

Goal: the tableau reasons over the **original** let-eliminated assertions,
not NNF and not up-front CNF. Each connective is expanded lazily, and only
for the polarity in which the branch reaches it. Clauses appear only:
- for theory lemmas
- as the record of an expansion
- after the fact, in proofs

## Design (F1)

### Formula store (`src/formula.rs`)
- `Node = Lit(i32) | And(..) | Or(..) | Not(n) | Ite(c, t, e) | Iff(a, b)`, memoized by term uid.
- The builder runs **only in formula positions** (assertion roots and connective children):
  - `Annotated` is transparent. `extract_op` panics on it, and also on `Xor` **[B3]**.
  - `Implies(ts, b)` becomes `Or(¬ts…, b)`. `Xor` is a left fold of `Not(Iff)`.
  - Bool `=` becomes `Iff`. Bool `distinct`: 0 or 1 arguments give true, 2 give `Not(Iff)`, 3 or more give false **[m]**.
  - `ite` (in a formula position it is Bool) becomes an `Ite` node.
  - Chained `<`, `<=`, `>`, `>=` are **rewritten by the builder** to an And of
    binary atoms. The arithmetic frontends silently drop atoms that don't have
    exactly 2 arguments, so skipping this rewrite is unsound **[B2]**.
  - Everything else is an atom. That includes quantifiers: their polarity
    comes from the assignment sign, not from NNF position **[m]**.
    - `insert_predecessor(atom)`, then `get_or_allocate_lit_for_term(atom)`.
    - The egraph only ever sees atoms. Connective egraph nodes carry no
      congruence **[B3]**.
  - Bool constants: `true` gets a unit clause for its literal; `false` gets a
    unit clause for its negation.

### Hooks
- `main.rs`, when `--sat-backend tableau` and `--tableau-input formula`:
  - `build` replaces `nnf` + `insert_predecessor` + `cnf_tseitin`.
  - `check_for_function_bool` runs **on each atom**, not on the formula
    **[B1]**. It still encodes Bool subterms in term positions, plus testers
    and term-level `ite` axioms **[B4]**.
- `cdcl.rs` hands `(FormulaStore, roots)` to the tableau before the propagator exists.

### Tableau
- **Node variables:**
  - Each And/Or/Ite/Iff node gets a tableau-internal variable, reserved by
    bumping `cnf_cache.next_var` with **no `var_map` entry** **[M2]**.
  - These variables are never observed or notified, and never appear in lemmas.
  - `Not` is a negated literal; it has no variable.
- **Roots:** each root becomes a unit clause.
- **Expansion:** when node `n` is first assigned with sign `s`, the tableau
  adds the definition clauses for that polarity only:
  - And+: `¬n ∨ cᵢ` for each child
  - And−: `n ∨ ¬c₁ ∨ … ∨ ¬cₖ`
  - Or: the dual
  - Ite±: two ternary clauses each, condition first
  - Iff±: two ternary clauses each
- **Permanence:** expansion clauses are global and permanent. A "no-op
  re-expansion" is unsound under out-of-order assignment plus backtracking
  **[B5]**.
  - Watches, reasons, dependencies, backjumping and the triggered agenda are reused unchanged.
  - Backward (upward) clauses are never generated for a polarity the branch didn't reach.
- **Completion:** model completion and the fresh-variable check skip node variables.
  - At a model check every non-node variable is assigned.
  - Every unassigned node can take the value of its subformula, which
    satisfies all of its definition clauses, so the model is sound.
- **Lemmas:** they keep the general clause store. They introduce their own
  Tseitin variables (datatype lemmas, QI instances, `process_ite`,
  `boolean_dt_constraints`) and fresh `make_eq` atoms **[M1]**.
- **Proofs:** `--proof` and `--partial-proof` are rejected in formula mode until F4.

### Expected effect
With total models (F1), relevancy for the theories is limited **[M5]**. F1's measurable gains:
- fewer variables
- no backward or upward Tseitin clauses
- no egraph merges of connective nodes
- no NNF duplication of `ite` and `iff`

Measure against the clause tableau as well as CaDiCaL.

## Status (F1 implemented)

- **Code:**
  - `src/formula.rs` builds the DAG.
  - `src/sat_tableau.rs` has `add_formulas`, polarity-specific lazy
    expansion, node variables excluded from completion, and agenda priority
    by origin (input, then expansions, then lemmas).
  - Enable it with `--tableau-input formula`. The default is `clauses` until F2 and F3.
  - Proofs fall back to clause input.
  - Harness switch: `SUNDANCE_TABLEAU_INPUT`.
- **Tests:**
  - The regression suite gives 433 correct / 0 incorrect / 7 timeouts in both modes.
  - A unit test cross-checks 20k random formula DAGs (shared nodes, `Ite`,
    `Iff`, lazily revealed clauses) against brute force, including the models.
- **Verus subset** (309 hard files, 60s):

  | Mode | Timeouts | Time on files all modes solve |
  |---|---|---|
  | CaDiCaL | 0 | 1,476s |
  | Clause input | 27 | 2,233s |
  | Formula input | 37 | 2,438s |

  On the diamonds, formula and clause input tie, and both beat CaDiCaL.
- **Why formula input is slower today:**
  1. **Completion.** It accounts for about 80% of decisions: atoms under
     unreached subformulas are decided and notified anyway. A partial-model
     experiment (branch only on open clauses) cut decisions 4–8x, but gave 15
     wrong answers, 6 of them `sat` (Bool disequality, testers, backtracking).
     So F3 is required, not optional.
  2. **No sharing between instance bodies and the input.** Input connectives
     have no `var_map` entries, so each instance re-encodes its subformulas
     instead of reusing values already decided. This doubles the Bool
     variables and instantiations on `marshal_v.39`. F2 fixes it: instance
     bodies become formula nodes, memoized by uid together with the input.

## Status (F3 and F2 implemented)

- **F3: partial models** (`--partial-models`, tableau only).
  - The model check gets only assigned atoms.
  - Completion branches only on open clauses that have no unassigned
    connective literal. Definitions of unreached connectives hold under evaluation.
  - Two theory gaps found the 15 wrong answers. Both are fixed in the
    propagator through `cb_decide` requests, with no interface change:
    1. **Theory-fixed atoms.** An unassigned atom whose egraph class contains
       `true`/`false` is requested with that polarity, because its assignment
       triggers checks such as tester exclusivity.
    2. **Bool terms in argument positions** (`Egraph::is_congruence_argument`).
       Their two-valuedness only reaches the egraph through assignment
       (`f(x), f(y), f(z)` pairwise distinct).
  - When a rejection carries no lemma, the tableau asks `cb_decide` before accepting.
  - **End-of-search completion.** When a partial model is accepted while
    atoms are still open, it is completed once on that branch and checked
    again. Unmerged equalities match fewer triggers, so QI can depend on
    those atoms.
- **F2: instance bodies as formulas.**
  - `FormulaStore` is shared (`Rc<RefCell<…>>`) between the tableau and the propagator.
  - Connective variables are allocated at build time; the tableau indexes new nodes after each callback.
  - Instance and skolem bodies are built from the let-eliminated term,
    memoized with the input. The propagator sends only `(¬q ∨ root)` plus
    `check_for_function_bool` clauses for new atoms.
  - Proof steps are skipped in formula mode.
- **Branching.** In formula mode, triggered clauses prefer the literal that
  agrees with its variable's saved phase (true if never assigned).
  - Trying the first literal refuted Verus typing guards repeatedly: one file
    had 6.5k model checks and timed out, against 1.1s otherwise.
  - Positive-first alone was slower overall.
- **Hard Verus subset** (309 files, 60s):

  | Mode | Timeouts | Time (285 files all modes solve) |
  |---|---|---|
  | CaDiCaL | 0 | 1,710s |
  | Formula, partial, F1 (CNF instances) | 14 | 1,848s |
  | Formula, partial, F2, phase saving, completion | **10** | **1,683s** |

  On the full-file comparison: clause input with partial models had 15
  timeouts and 1 `unknown`; clause input with total models had 26 timeouts.

## Full UFDTLIA benchmark (commit 86dfb5b; 3,763 files, 60s, 96 parallel, same binary)

| Mode | unsat | timeout | unknown | Time on 3,089 all-unsat | Median ratio vs CaDiCaL |
|---|---|---|---|---|---|
| CaDiCaL | 3153 | 596 | 14 | 4,100s | 1.00 |
| Tableau, clause input (default) | 3165 | 589 | 9 | 4,751s | 1.07 |
| **Tableau, formula input + partial models** | **3184** | **565** | 14 | **3,490s** | **0.85** |

- Formula input with partial models against CaDiCaL: it solves 53 files
  CaDiCaL times out on and times out on 26 CaDiCaL solves. It gives
  `unknown` on 8 files CaDiCaL proves `unsat`, and proves `unsat` on 12
  files CaDiCaL leaves `unknown`.

## Investigation: `noflatand2` (fixed in 876a11e)

- An instance body `(=> F H)` was satisfied by `H`, so the nested quantifier
  atom `F` stayed unassigned.
- Both values of `F` are refutable. The `F`-false side (skolemization)
  produces ground terms that E-matching needs to refute the rest. Total
  models explored it because completion assigned `F`.
- Approaches that did not work:
  - per-branch completion of the accepted model
  - a global fallback to total models
  - a fallback with a restart
  - a fallback with a restart and reset phases

  Instances generated during the partial phase steer the later search away
  from the `F`-false branch.
- Fix: once instantiation saturates, the propagator requests the open
  quantifier atoms through `cb_decide`, skolemizing value first.
  - The regression suite gives 433/0/7 in all modes.
  - Cost: genuinely `unknown` problems take longer to answer
    (`datatypes/tester_duplication_unknown6` with clause input + partial
    models: about 7s to about 12s).
- The 8 Verus `unsat`→`unknown` cases are **not** fixed by this. Two classes:
  - `atmosphere/array*`: fail only with formula input + partial models
  - `noderep rwlock`: fail with formula input even with total models

## Later phases
- **F2: instance bodies as formulas** **[M3]**.
  - The body root becomes a node variable. The propagator sends the external
    clause `¬q ∨ n` and registers "n defines node X" through a side channel.
  - It must still allocate variables for the body's atoms (including nested
    quantifiers), run `check_for_function_bool` on those atoms, and run
    `sync_new_vars`.
  - Relax the term assertion in `cb_add_external_clause_lit`.
  - Formulas arrive mid-propagation (eager QI), so they are global.
- **F3: partial models.** Audit list:
  - arithmetic model paths
  - Nelson–Oppen probing over terms of unassigned atoms
  - Bool disequality, whose propagation needs both sides assigned **[M4]**
  - `generate_deferred_tester_clauses`, occurs check, `--trail-out`
- **F4: proofs** **[M6]**.
  - Register node variables as proof literals with `register_term(n, node_term, true)`.
  - Emit expansion clauses as definitions when they're added. Push flips and
    closures as RUP steps *as they happen*, so they interleave correctly with
    lemma steps.
  - Confirm the checker accepts literals over `=>`, `ite`, `xor` and Bool `=`.
- Keep `--tableau-input {formula,clauses}` for A/B comparison.
