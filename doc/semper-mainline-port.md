# Semper backend: build notes and the mainline port

This records how the `semper` e-graph backend is built, the changes it needs in
the `semi-persistent-egraph` engine, and the changes that stay in Sundance, so
the engine changes can be reimplemented on the engine's `main` without rebasing
the `satcore-layer0` branch onto it. It also pins the exact branches involved. It
is not a status page: the behaviour is what the Sundance regression suite and the
arithmetic differential corpus assert.

## Branches

**Sundance (`Sundance-SMT`).**

| ref | where | commit | note |
|---|---|---|---|
| mainline | `origin/main` (github.com/yaspar-org/Sundance-SMT) | `916124c` | `#215`, de-dup instantiations |
| work | `semper-backend` (tracks `fork/semper-backend`, github.com/remi-delmas-3000/Sundance-SMT) | rebased onto `916124c` this session, 22 commits | holds the adapter + the changes below; working tree not yet committed |
| backup | `semper-backend-prerebase-20261005` | `5633d10` | the pre-rebase tip, kept as a fallback |

The engine dependency is pinned in `Cargo.toml`:
`semi-persistent-egraph = { git = ".../yaspar-org/semi-persistent", rev = "5c46fd7", optional = true }`,
behind the `semper-egraph` feature. For local engine work there is a dev-only
`[patch]` pointing at a local checkout; it is machine-local and must not be
committed.

**Engine (`semi-persistent`, the "semper" engine).**

| ref | where | commit | note |
|---|---|---|---|
| mainline | `origin/main` (github.com/yaspar-org/semi-persistent) | `a03eb03` | the port target |
| semper branch | `origin/satcore-layer0` (`fork/satcore-layer0` = `ede7c44`) | `e7d1ff4` | carries the semper engine features; Sundance pins `5c46fd7`, four commits behind this tip |
| work | `semper-merged-log` (worktree, off `5c46fd7`) | `5c46fd7` + 1 | the `merged_log` change below, not yet committed |

`main` and `satcore-layer0` share merge-base `56a06a5`; `main` is **162** commits
ahead of it, `satcore-layer0` **32**. Rebasing `satcore-layer0` onto `main` would
replay 32 commits over 162, so the plan is to reimplement only the engine changes
the adapter needs, listed below.

## The adapter (stays in Sundance)

`SemperEgraph` (`src/egraphs/semper/mod.rs`) implements `EgraphTrait` over the
engine type `EGraph31`, replacing the basic backend's hand-written trails with
the engine's mark/restore tokens: one token per decision level, and
`backtrack_to(level)` is a single `restore` to that level's token.

Two contracts are adapted. **Terms are permanent, equalities are scoped:** the
driver's id maps are never rolled back, but a restore deletes nodes made after
the mark, so the adapter indexes a stable `terms` table and logs every
registration; `backtrack_to` restores the token, then replays the logged
registrations above the restore point and repairs their table entries.
**Conflicts are asserted-equality pairs:** each `assert_equal` carries an
`Assumption` justification with its index in the assertion log, and explanation
maps indices back to the pairs; a conflict is the `true` and `false` constants
merging into one class.

EUF runs through `assert_equal`/`assert_disequal` and congruence. E-matching
(`match_triggers`) is a top-down matcher over the registration log; relevancy
filtering is adapter-side — `match_triggers` computes a relevant cone
(`relevant_slice`) and drops out-of-cone candidates (`candidate_relevant`,
`SEMPER_RELEVANCY=1`, measured at 0% pruning on the current corpus). The engine
offers a class-level match shield for this (see the next section); the adapter
does not call it yet.

## Engine changes needed on `main`

**Already on `main` (`a03eb03`), do not re-port:** the e-graph semi-persistent
`mark(ShrinkPolicy) -> EGraphToken` / `restore(EGraphToken)`; the single merge
chokepoint `merge_in_classes` and `merge_justified`; the do-not-match shield
`set_class_matchable` / `is_class_matchable` / `subsume` (the match shield is
written through the semi-persistent class store, so it rolls back on restore, and
`set_class_matchable` is two-directional so a relevancy client can un-shield as
terms become relevant); and the verified, runtime-selectable diff stores.
`containers-verus/src/diff_store.rs` defines the `DiffStore` contract with checked
`InlineStore`, `ParallelStore`, and `TrailStore` implementations, and
`dyn_store.rs` wraps them in a `DynStore` chosen at construction by
`StoreKind::{Inline, Parallel, Trail}` (the e-graph's `Cfg::Policy: StorePolicy`
resolves the store). The trail diff is already present, verified, and selectable
on `main`: it is not a port item.

**(1) Drainable merge queue — required, new this session.** Nelson-Oppen needs the
e-graph to export every equality it derives between arithmetic terms. Capture
must happen at merge time: after congruence closure the two classes are one, so
the pairing cannot be recovered from `find`. The change is confined to
`egraph/src/egraph.rs`:

- Two fields on the e-graph struct (next to `worklist`/`collisions`):
  `merged_log: Vec<(Cfg::G, Cfg::G)>` and `record_merges: bool`, both initialised
  in the constructor (`merged_log: Vec::new()`, `record_merges: false`).
- At the end of `merge_in_classes`, immediately before it returns the merge
  record `m`: `if self.record_merges { self.merged_log.push((m.survivor, m.absorbed)); }`.
  This one site catches direct, congruence, and completion merges, since all of
  them route through `merge_in_classes`.
- In `restore`, alongside the existing `worklist.clear()` / `collisions.clear()`
  / `touched.clear()`: `self.merged_log.clear();` (merges from a discarded scope
  are meaningless).
- Three public methods: `set_record_merges(&mut self, bool)` (clears the log when
  disabling), `record_merges(&self) -> bool`, and
  `take_merged_log(&mut self) -> Vec<(Cfg::G, Cfg::G)>` (a `mem::take`).

Gate check: with `record_merges` off the engine records nothing, so EUF-only runs
pay one predicted branch per merge. A unit test asserts that after an
assert + rebuild producing a congruence merge, `take_merged_log` holds both the
direct and the congruence-derived `(survivor, absorbed)` pair, and that the log
stays empty while the flag is off.

**(2) Diff-mode selection — no engine port, adapter wiring only.** `main` already
carries the verified trail/inline/parallel stores and runtime selection through
`DynStore`/`StoreKind` (see above), so there is nothing to reimplement. The only
difference is the knob: `satcore-layer0` reads `SEMPER_DIFF` (env) in
`egraph/src/{main.rs, director.rs, ematch.rs}` to choose the discipline, whereas
on `main` the discipline is chosen by building the e-graph's columns with the
`StoreKind` the `StorePolicy` resolves. The port is to map Sundance's
`--diff-mode` to `StoreKind::{Inline, Parallel, Trail}` through `main`'s
`StorePolicy`/`DynStore`, not to re-implement capture. For reference, trail is the
chronological discipline: a write appends the overwritten cell to one shared log,
`mark` records the log length, and `restore` rewinds to it, so writes and `mark`
are O(1) and `restore` costs one pass over the writes since the mark, with no
column copying — the property that makes one-mark-per-decision-level affordable.

## Sundance-side changes (do NOT go to the engine)

These live in Sundance and are carried by the `semper-backend` branch; they are
listed here because they are part of "what made the backend work", but they port
to Sundance `main`, not to the engine.

**Arithmetic drain** (`src/egraphs/semper/mod.rs`). `drain_arithmetic_equalities`
folds `take_merged_log` into equalities between arithmetic class names (a merge
whose survivor or absorbed class is arithmetic yields one equality and marks the
merged class arithmetic — the OR discipline the basic backend uses).
`mark_arithmetic` seeds the `arith_roots` set; `incremental_arithmetic` toggles
`set_record_merges` in lockstep; `backtrack_to` rebuilds `arith_roots` from the
surviving tagged terms, since the drain-before-advance discipline keeps the log
empty across a restore.

**true=false guard fix** (`src/solver_state.rs`, `src/egraphs/traits.rs`, and the
adapter impl). The driver signals a theory conflict by `true` and `false` merging.
`process_assignment` ended with `debug_assert!(find(true) != find(false), ...)`,
which was too strict: once the engine reports a true=false collision it latches
`reported_tf` and declines to re-report the same unresolved collision on the next
same-level assignment, and an ordinary disequality conflict can be returned in the
same call. A release build already solved every affected file, so only the debug
invariant was wrong. The fix adds `EgraphTrait::true_false_conflict_pending`
(default `false`; the semper impl returns `reported_tf`) and relaxes the assert to
`additional_constraints.is_some() || egraph.true_false_conflict_pending() || find(true) != find(false)`.
It is shared-driver code, so it fixes both backends; basic uses the default and is
unaffected.

## Reimplementing on `main` without rebasing

1. Branch from engine `main` (`a03eb03`). Apply change (1) to
   `egraph/src/egraph.rs` directly — it is self-contained and references only
   `merge_in_classes`, `restore`, and the struct, all present on `main`. Add the
   unit test and run `cargo test -p semi-persistent-egraph`.
2. Select the diff discipline through `main`'s verified `DynStore`/`StoreKind`
   (`StorePolicy`); there is no trail-capture port. Map `--diff-mode` to
   `StoreKind` rather than carrying `satcore-layer0`'s `SEMPER_DIFF` env reads.
3. Repin Sundance's `Cargo.toml` to the new engine commit (drop the dev `[patch]`),
   build `--features semper-egraph`, and expect signature drift on the shared APIs
   the adapter calls (`main` is 162 commits ahead of the pinned rev); resolve it in
   the adapter.
4. Validate with the arithmetic differential (`doc/semper-adapter.md`): semper vs
   basic over `tests/regression/smt_files/arithmetic/`, which must stay
   `MISMATCH=0` with `--arithmetic z3incremental` and no `--arith-solver none`, plus
   the full regression suite on both backends.
