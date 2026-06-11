# Egraph Trait Refactoring — Progress Summary

## What Was Done

### 1. Separated Egraph from SolverState

The original `Egraph` struct (~26 fields) conflated egraph-internal operations with solver-level state. We split it into:

- **`Egraph`** (in `src/egraphs/egraph.rs`) — pure egraph: union-find, congruence closure, predecessors, function_maps, backtracking. Has ZERO yaspar_ir imports.
- **`SolverState`** (in `src/solver_state.rs`) — owns the Egraph plus all solver state: CNF cache, context, quantifiers, datatypes, arithmetic terms, theory combination.

Fields that stayed in Egraph:
- `terms: Vec<TermSlot>` — internal term representation
- `patterns: DeterministicHashMap<u64, TermEntry>` — pattern terms for e-matching (TO BE REPLACED)
- `proof_forest: Vec<ProofForestEdge>`
- `proof_forest_backtrack_stack`
- `predecessors: Vec<FastDeterministicHashMap<u64, Predecessor>>`
- `predecessor_hash: u64`, `predecessor_level: Vec<u64>`
- `function_maps: DeterministicHashMap<String, Vec<(u64, Vec<u64>)>>`
- `true_term: u64`, `false_term: u64`
- `decision_level: usize`
- `predecessors_created_by_quantifiers`, `union_to_eclass`
- `next_id: u64` — counter for assigning egraph IDs

Fields that moved to SolverState:
- `context: Context`
- `terms_list: Vec<TermOption>` (yaspar Terms indexed by solver UID)
- `cnf_cache: CNFCache`
- `assertions`, `quantifiers`, `added_instantiations`, `added_skolemizations`
- `datatype_info`, `term_constructors`, `datatype_axioms_applied`
- `nelson_oppen_ineq_literals`, `arithmetic_terms`
- `lazy_dt`, `ddsmt`, `eager_skolem`
- `id_map: bimap::BiMap<u64, u64>` (solver UID <-> egraph ID)

### 2. Moved CC Functions into Egraph Methods

All congruence closure operations are now `impl Egraph` methods:
- `cc_union(x, y, proof_parent, level, fixed, from_quantifier) -> EgraphResult<u64>`
- `union_predecessors(u, v, level, fixed, from_quantifier) -> EgraphResult<u64>`
- `make_root(vertex, proof_parent)`
- `leastcommonancestor(u, v, tracker) -> Option<Vec<(u64, u64)>>`
- `proof_forest_backtrack(equality, y, y_root)`
- `backtrack_to(level)`
- `assert_equal(t1, t2, level) -> EgraphResult<u64>`
- `assert_disequal(t1, t2, diseq_lit, level) -> EgraphResult<u64>`
- `assert_distinct(terms, diseq_lit, level) -> EgraphResult<u64>`

`process_assignment` (solver-level entry point) lives as a free function in `solver_state.rs`.

### 3. Defined and Implemented `EgraphTrait`

The trait (in `src/egraphs/traits.rs`) defines the interface for any egraph implementation:

```rust
pub trait EgraphTrait {
    type Op: Clone + Eq + Hash;
    type TermId: Copy + Eq + Hash;

    fn register_true(&mut self) -> Self::TermId;
    fn register_false(&mut self) -> Self::TermId;
    fn register_term(&mut self, op: Self::Op, children: &[Self::TermId], dynamic: bool) -> Self::TermId;
    fn register_eq(&mut self, t1: Self::TermId, t2: Self::TermId, lit: Lit);
    fn register_boolean_term(&mut self, op: Self::Op, children: &[Self::TermId], lit: Lit) -> Self::TermId;
    fn assert_equal(&mut self, t1: Self::TermId, t2: Self::TermId, level: usize) -> EgraphResult<Self::TermId>;
    fn assert_disequal(&mut self, t1: Self::TermId, t2: Self::TermId, lit: Lit, level: usize) -> EgraphResult<Self::TermId>;
    fn assert_distinct(&mut self, terms: &[Self::TermId], lit: Lit, level: usize) -> EgraphResult<Self::TermId>;
    fn find(&self, term: Self::TermId) -> Self::TermId;
    fn are_equal(&self, t1: Self::TermId, t2: Self::TermId) -> bool;
    fn match_triggers(&mut self, trigger_term_pairs: Vec<(Self::TermId, Option<Self::TermId>)>) -> Vec<DeterministicHashMap<String, Self::TermId>>;
    fn backtrack_to(&mut self, level: usize);
    fn make_decision(&self, assignments: &[i32]) -> i32;
    fn make_decision_lit(&self, lit: Lit, assignments: &[i32]) -> Lit;
    fn explain_equality(&self, t1: Self::TermId, t2: Self::TermId) -> Option<Vec<(Self::TermId, Self::TermId)>>;
}
```

The current Egraph implements it with `type Op = Op` (our repr::Op enum) and `type TermId = u64`.

Supporting types:
- `Conflict<T> { equalities: Vec<(T,T)>, disequality: (T,T), diseq_lit: Lit }`
- `EgraphResult<T> { conflict: Option<Conflict<T>>, propagations: Vec<Lit> }`
- `MatchResult<T> { term: T, children: Vec<T> }` (currently unused, match_triggers returns DeterministicHashMap instead)

### 4. Internal Term Representation

Egraph stores terms using these types (in `src/egraphs/repr.rs`):

```rust
pub enum Op {
    App(String),       // uninterpreted function (includes indexed like "(is Variant1)")
    Eq, Ite, Not, And, Or, Implies, Distinct,
    Local(String),     // pattern variable (only in e-matching patterns)
    Constant(String),  // ground constant (leaf term)
}

pub enum Children {
    Arity0, Arity1([u64;1]), Arity2([u64;2]), ..., Arity6([u64;6]), ArityN(Vec<u64>)
}

pub struct TermEntry { pub op: Op, pub children: Children }

pub enum TermSlot { Empty, Term(TermEntry), Opaque }
```

`TermSlot::Opaque` is for quantifier terms — they participate in union-find but have no visible internal structure.

### 5. Egraph Assigns Its Own IDs

`register_term(op, children, dynamic) -> u64` uses `self.next_id` counter. The solver maintains a bidirectional map `bimap::BiMap<u64, u64>` between solver term UIDs (from yaspar hash-consing) and egraph-assigned IDs.

- `solver_state.to_egraph_id(solver_uid) -> egraph_id`
- `solver_state.to_solver_uid(egraph_id) -> solver_uid`

`SolverState::insert_predecessor` extracts `Op` and children from a yaspar `Term`, recursively registers children (getting their egraph IDs), then calls `self.egraph.register_term(op, &egraph_children, dynamic)`.

### 6. Key Correctness Fixes Made During Refactoring

- **`dynamic` flag** on `register_term`: when true, calls `find_and_union_to_eclass` to merge with existing congruent terms. Needed for both quantifier instantiation AND datatype axiom terms.
- **`diseq_lit` in Conflict**: the SAT literal that caused the disequality, stored in the conflict so solver can build correct conflict clauses.
- **`predecessors_created_by_quantifiers`** read from egraph (not SolverState's dead copy).
- **Indexed function ops** (like `(_ is Ctor)`) include indices in the key: `Op::App("(is Variant1)")` — prevents spurious congruence between different testers.
- **Pattern terms stored separately** from ground terms (in `self.patterns` HashMap) so hash-consing collisions between pattern and ground terms don't interfere.

### 7. E-matching Current State

Currently `match_term` is an Egraph method that:
- Takes `(assignment: &mut DeterministicHashMap<String, u64>, trigger_term_pairs: Vec<(u64, Option<u64>)>)`
- Looks up trigger terms from `self.patterns` HashMap
- Matches `Op::Constant` → check find equality; `Op::Local` → bind variable; `Op::App` → recurse via `find_assignments_on_term`
- Returns `Vec<DeterministicHashMap<String, u64>>` (variable name → matched egraph ID)

**Problem**: Pattern terms are stored by solver UID in `self.patterns`, but ground terms use egraph IDs. When a pattern contains a constant like `BOOL` that also exists as a ground term, `match_term` tries to call `self.find(pattern_uid)` which fails because pattern UIDs aren't in proof_forest.

---

## What Needs to Happen Next

### Immediate: Replace Pattern Representation

**Current broken approach**: Patterns stored as `TermEntry` in `self.patterns: HashMap<u64, TermEntry>` keyed by solver UID. Mixed ID spaces cause crashes.

**Target approach** (following egg/egglog): Patterns are a separate recursive tree type, never stored by ID in the egraph:

```rust
/// A pattern for e-matching. Tree structure, not stored in the egraph.
pub enum Pattern {
    /// A variable to be bound during matching
    Var(String),
    /// A ground term already in the egraph — must be in the same equivalence class
    Ground(u64),  // egraph ID
    /// A function application with sub-patterns
    App(Op, Vec<Pattern>),
}
```

**How matching works with this**:
- `Pattern::Var(name)` → bind the variable to the current ground term's egraph ID
- `Pattern::Ground(egraph_id)` → check `self.find(current_ground) == self.find(egraph_id)`
- `Pattern::App(op, sub_patterns)` → look up `op` in `function_maps`, for each match recurse into sub_patterns

**Building patterns** (in `SolverState::solver_walk_term`):
- When registering a quantifier, for each trigger pattern term:
  - `Local(x)` → `Pattern::Var(x.name)`
  - `Global(qid)` / `Constant(c)` → check if `self.id_map.get_by_left(&term.uid())` exists. If yes: `Pattern::Ground(egraph_id)`. If no: panic (ground constant not registered yet).
  - `App(f, args)` → `Pattern::App(extract_op(term), args.map(build_pattern))`

**Compiled patterns** (for efficiency):
- Store compiled patterns in a `Vec<Pattern>` on the Egraph (or SolverState), indexed by a `PatternId`.
- Quantifier triggers reference `PatternId`s instead of raw term UIDs.
- `match_triggers(pattern_id: usize, ground_hint: Option<u64>)` looks up the compiled pattern and runs matching.

### Steps to Implement

1. **Define `Pattern` enum** in `src/egraphs/repr.rs`
2. **Add `compiled_patterns: Vec<Pattern>`** to Egraph (or a separate store)
3. **Add `compile_pattern(pattern: Pattern) -> PatternId`** method
4. **Rewrite `match_term`** to take `&Pattern` and recurse structurally (no HashMap lookup for triggers)
5. **Update `solver_walk_term`** to build `Pattern` trees from yaspar Terms when registering quantifier triggers, using `self.to_egraph_id()` for ground terms
6. **Update `instantiate_quantifiers`** to pass `PatternId`s to match_triggers
7. **Remove `self.patterns: HashMap<u64, TermEntry>`** from Egraph
8. **Remove `register_pattern_entry` method**
9. **Test and verify** 352/0/17 baseline

### After Patterns Are Fixed

1. **Remove `register_term_with_id`** — the internal method is only used by the trait impl now
2. **Wire up remaining ID conversions** — any arithmetic/propagator code that still passes raw UIDs
3. **Make SolverState generic**: `SolverState<E: EgraphTrait>` — requires all egraph interactions to go through the trait
4. **Plug in semi-persistent egraph** as alternative backend

---

## File Layout

```
src/
├── egraphs/
│   ├── egraph.rs          — Egraph struct + all methods (no yaspar imports)
│   ├── traits.rs          — EgraphTrait definition + Conflict/EgraphResult types
│   ├── repr.rs            — Op, Children, TermEntry, TermSlot enums
│   ├── congruence_closure.rs — just add_parent/get_parent/get_child helpers
│   ├── proofforest.rs     — ProofForestEdge type
│   ├── unionfind.rs       — ProofTracker
│   ├── datastructures.rs  — CanonicalForm, CanonicalOp, DisequalTerm, Predecessor, etc.
│   ├── utils.rs           — get_subterms helper
│   └── mod.rs
├── solver_state.rs        — SolverState + process_assignment + find_if_eq_diseq
├── cadical_propagator.rs  — SAT solver interface
├── main.rs                — entry point
├── quantifiers/           — quantifier instantiation (calls egraph.match_triggers)
├── datatypes/             — datatype axiom generation
├── arithmetic/            — Nelson-Oppen, linear arithmetic
├── preprocess.rs          — boolean/datatype preprocessing
├── cnf.rs                 — CNF conversion
└── ...
```

## Regression Test Baseline

- **352 correct, 0 incorrect, 17 timeout** (identical to main branch)
- Tests run with: `cargo build --release --no-default-features && cargo test --release --no-default-features regression_test -- --no-capture`
