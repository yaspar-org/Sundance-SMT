# The semper e-graph backend

This describes the `SemperEgraph` adapter (`src/egraphs/semper/mod.rs`), the
changes to the `semi-persistent-egraph` engine that let it run arithmetic, and
the trail-diff capture discipline that makes its mark/restore cheap. It is not a
status page: the current behaviour is what the regression suite and the
arithmetic differential corpus assert.

## The adapter

`SemperEgraph` implements `EgraphTrait` over the engine `EGraph31`, replacing
the basic backend's hand-written trails (signature trail, proof-forest stack,
per-level replay) with the engine's mark/restore tokens: one token per decision
level, and `backtrack_to(level)` is a single restore to that level's token,
whatever the distance.

Two contracts need adaptation.

**Terms are permanent; equalities are scoped.** The driver's id maps are never
rolled back, so a term registered at level 5 must survive a backtrack to level
0, but a semi-persistent restore deletes nodes created after the mark. The
adapter never exposes raw engine node ids: a driver id indexes a stable `terms`
table, and every registration is logged. `backtrack_to` restores the token, then
replays the logged registrations above the restore point, re-interning each term
into the restored graph and repairing its table entry. Replay resolves children
through the table, so a replayed term lands on the correct, possibly re-minted,
nodes.

**Conflicts are asserted-equality pairs.** Each `assert_equal` merge is justified
with an `Assumption` carrying its index in the assertion log; explanation maps
those indices back to the asserted pairs, and the driver rebuilds SAT literals
through `make_eq`. A conflict is signalled by the `true` and `false` constants
merging into one class: that collision is the clause the SAT solver learns and
backtracks on.

EUF runs through `assert_equal`/`assert_disequal` and the engine's congruence
closure. E-matching (`match_triggers`) is a top-down matcher over the
registration log; relevancy filtering is an opt-in traversal of the merge state
(`SEMPER_RELEVANCY=1`), measured at 0% candidate pruning on the current corpus
and parked behind the flag.

## What changed in semper to run arithmetic

Arithmetic combines with EUF by Nelson-Oppen: the e-graph must export every
equality it derives between arithmetic terms so the arithmetic solver can assert
them. `drain_arithmetic_equalities` returned nothing, so semper answered EUF only
and arithmetic required `--arith-solver none`.

**Engine, merge observation (`egraph/src/egraph.rs`).** Every merge, direct or
congruence or completion, routes through one primitive, `merge_in_classes`. A
flag-gated `merged_log` records each `(survivor, absorbed)` pair at that
chokepoint, drained by `take_merged_log` and cleared on `restore`;
`set_record_merges` gates it, so EUF-only runs record nothing. Capturing at merge
time is necessary: after congruence closure the two classes are one, so the
pairing cannot be recovered from `find`.

**Adapter, the drain.** `drain_arithmetic_equalities` folds the log into
equalities between arithmetic class names: a merge whose survivor or absorbed
class is arithmetic yields one equality and marks the merged class arithmetic,
the same OR discipline the basic backend uses on its per-root flag.
`mark_arithmetic` seeds the arithmetic-class set; `incremental_arithmetic`
toggles engine capture in lockstep. The set is a derived cache, so `backtrack_to`
rebuilds it from the surviving tagged terms against the restored union-find; the
driver drains before advancing a decision level, so the log is empty across a
restore and nothing stale survives.

**Driver, the true=false guard.** Semper's lazy rebuild surfaces true=false
collisions during an equality merge rather than through the atom-union path,
which exposed an over-strict `debug_assert` in `process_assignment`. It fired
when a collision had already been reported at that level (the engine's
`reported_tf` latch declines to re-report the same unresolved collision) or when
an ordinary disequality conflict was returned in the same call. A release build
already solved every case, so the behaviour was sound and only the debug
invariant was wrong. The guard now reads `additional_constraints.is_some() ||
egraph.true_false_conflict_pending() || find(true) != find(false)`, where
`true_false_conflict_pending` is a new `EgraphTrait` method (semper returns
`reported_tf`, default false). It fires only on a genuinely undetected merge, and
it is debug-only, so release behaviour is unchanged.

Result: the 63-file arithmetic corpus runs on semper across the inline, parallel,
and trail diff modes with verdicts matching the basic backend and no
`--arith-solver none`; both backends pass their full regression harness.

## Trail-diff for performance

The engine keeps its mutable per-node columns, including the hashcons index it
uses as a merge-repair hint cache, in a semi-persistent store whose capture
discipline `--diff-mode` selects (`inline`, `parallel`, `trail`; exported as
`SEMPER_DIFF` before construction). **Trail** is the chronological discipline: a
write appends the overwritten cell to one shared diff log, `mark` records the
log's length as a watermark, and `restore` rewinds the log to that watermark,
undoing writes newest-first. Writes are O(1) appends with no per-column
bookkeeping, `mark` is O(1), and `restore` costs one pass over the writes made
since the mark. This is what makes one-mark-per-decision-level affordable on deep
SMT search: the engine copies no column on mark or restore, and a long backtrack
is a single rewind rather than per-level replay. Inline and parallel instead
capture first-write-wins within a frame (inline tag bits, parallel a bitmap) and
suit frames that overwrite the same cell repeatedly; trail suits the
append-dominated write pattern with restores proportional to recent work, which
is the e-graph's mark/restore profile.
