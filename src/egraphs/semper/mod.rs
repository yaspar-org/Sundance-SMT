// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Semi-persistent e-graph backend for [`EgraphTrait`].
//!
//! Implements the trait over `semi-persistent-egraph`, replacing the basic
//! backend's hand-written trails (sig_trail, proof-forest stack, per-level
//! replay) with the engine's mark/restore tokens: one token per decision
//! level, and `backtrack_to` is a single restore to the target level's
//! token, whatever the distance.
//!
//! Two contracts need adaptation:
//!
//! - **Terms are permanent, equalities are scoped.** The driver's id maps
//!   (`id_map`, CNF var maps) are never rolled back, so a term registered at
//!   level 5 must survive a backtrack to level 0 — but a semi-persistent
//!   restore deletes nodes created after the mark. The backend therefore
//!   never hands out raw node ids: a driver id is an index into the stable
//!   `terms` table, and every registration is logged. `backtrack_to`
//!   restores the token, then replays the logged registrations above the
//!   restore point, re-interning each term into the restored graph and
//!   repairing its table entry. Replay resolves children through the table,
//!   so a replayed term lands on the correct (possibly re-minted) nodes.
//!
//! - **Conflicts are explained as asserted-equality pairs.** The engine's
//!   proof steps carry [`Justification`] leaves; each `assert_equal` merge
//!   is justified with `Assumption` carrying its index in the assertion
//!   log, and explanation maps the indices back to the asserted pairs the
//!   driver expects (it reconstructs SAT literals itself via `make_eq`).
//!
//! E-matching (`match_triggers`) is a port of the basic backend's top-down
//! matcher over the registration log. Relevancy filtering of match candidates
//! is a traversal of the merge state (the e-graph is the relevancy skeleton),
//! opt-in via `SEMPER_RELEVANCY=1`. E-matching is on by default
//! (`SEMPER_EMATCH=0` disables it); a Z3-cross-checked sweep of the quantifier
//! regression suite found no unsound answers.
//!
//! `drain_arithmetic_equalities` exports the EUF-derived equalities the
//! Nelson-Oppen combination needs: the engine records every merge through its
//! `merged_log` (enabled by `incremental_arithmetic`), and the adapter folds
//! that log into equalities between arithmetic classes, so arithmetic runs on
//! this backend without `--arith-solver none`.

use crate::egraphs::repr::{Op, Pattern, PatternId};
use crate::egraphs::traits::{Conflict, EgraphResult, EgraphTrait, Lit};
// FxHashMap, not utils::DeterministicHashMap: that alias is ordered (needs
// Ord, which Op lacks), and neither map here is ever iterated, so ordering
// buys nothing. FxHashMap has no random state, keeping runs reproducible.
use rustc_hash::FxHashMap;
use semi_persistent_egraph::containers::ShrinkPolicy;
use semi_persistent_egraph::id::ENodeId;
use semi_persistent_egraph::model::MachineLit;
use semi_persistent_egraph::union_find::{Justification, ProofBuf};
use semi_persistent_egraph::{EGraph31, EGraphToken, IndexLike};
// Native e-matching path (SEMPER_NATIVE_EMATCH=1): drives the engine's own
// matcher instead of the top-down reimplementation. Aliased to keep the
// adapter's own `Pattern`/`Span`/`flatten` names unambiguous.
use semi_persistent_egraph::ast::{Pattern as SemPattern, Span as SemSpan, VarId};
use semi_persistent_egraph::compile::{Atom, flatten as sem_flatten};
use semi_persistent_egraph::ematch::MatchIterator;
use semi_persistent_egraph::index::{IndexStore, VariantIndex};
use semi_persistent_egraph::model::MachineModel;
use semi_persistent_egraph::nodes::DefaultConfig;
use semi_persistent_egraph::resolve::{GlobalCtx, resolve as sem_resolve};
use semi_persistent_egraph::schedule::schedule as sem_schedule;
use std::cell::RefCell;
use std::fmt;
use std::sync::atomic::{AtomicU64, Ordering};
use yaspar_ir::ast::Local;

/// Proof forest on. Required: conflict explanation reads it; with it off
/// `explain_pairs` falls back to the whole assert trail (sound, maximal).
const PROOFS_ENABLED: bool = true;
type Eg = EGraph31<MachineLit, true, PROOFS_ENABLED>;
type SortId = semi_persistent_egraph::id::SortId;
type OpId = semi_persistent_egraph::id::OpId;

/// Sentinel for `node_to_driver`: this engine node has no driver id yet.
const NO_DRIVER: u32 = u32::MAX;

/// Native-matcher coverage counters (SEMPER_NATIVE_EMATCH). `CALLS` counts
/// `match_triggers` invocations that took the native path; `FALLBACKS` counts
/// those that bailed to the top-down matcher (a non-application trigger root,
/// a resolve failure, or a binding with no driver id). A low fallback ratio is
/// the evidence that the native matcher, not the reimplementation, is doing the
/// work. Printed on teardown when the flag is set.
static NATIVE_MATCH_CALLS: AtomicU64 = AtomicU64::new(0);
static NATIVE_MATCH_FALLBACKS: AtomicU64 = AtomicU64::new(0);
// Relevancy instrumentation (reported at Drop when SEMPER_RELEVANCY=1): marks
// made (nodes un-shielded), refreshes (one per eager matching round),
// top-down candidates skipped as shielded, quantifiers skipped as irrelevant.
static REL_MARKS: AtomicU64 = AtomicU64::new(0);
// Explanation audit (SEMPER_EXPLAIN_AUDIT=1): ordinary conflicts audited, how
// many the intern-time alignment would extend, by how many pairs, and how many
// cite a conflation it cannot recover.
static EXPLAIN_AUDITED: AtomicU64 = AtomicU64::new(0);
static EXPLAIN_INCOMPLETE: AtomicU64 = AtomicU64::new(0);
static EXPLAIN_ADDED_PAIRS: AtomicU64 = AtomicU64::new(0);
static EXPLAIN_UNRECOVERABLE: AtomicU64 = AtomicU64::new(0);
static EXPLAIN_INVALID: AtomicU64 = AtomicU64::new(0);
static EXPLAIN_TF_AUDITED: AtomicU64 = AtomicU64::new(0);
static EXPLAIN_TF_INVALID: AtomicU64 = AtomicU64::new(0);
static EXPLAIN_UNSOUND: AtomicU64 = AtomicU64::new(0);
static EXPLAIN_TF_UNSOUND: AtomicU64 = AtomicU64::new(0);
static INTERN_TOTAL: AtomicU64 = AtomicU64::new(0);
static INTERN_NONCANONICAL: AtomicU64 = AtomicU64::new(0);

/// `SEMPER_EXPLAIN_LEGACY=1`: the path-only explanation (before the
/// creator-children completion), for measurement.
fn explain_legacy() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("SEMPER_EXPLAIN_LEGACY").is_some())
}

fn explain_audit() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("SEMPER_EXPLAIN_AUDIT").is_some())
}
static REL_REFRESHES: AtomicU64 = AtomicU64::new(0);
static REL_SKIPPED_CANDIDATES: AtomicU64 = AtomicU64::new(0);
static REL_SKIPPED_QUANTIFIERS: AtomicU64 = AtomicU64::new(0);
/// Calls of the per-assignment relevancy hook.
static REL_ASSIGN_HOOKS: AtomicU64 = AtomicU64::new(0);
/// Marks the per-round gate rescan made that the hook had not (0 when the
/// hook is complete).
static REL_RESCAN_MARKS: AtomicU64 = AtomicU64::new(0);
// One sample per slice: [relevant terms, all terms, relevant Boolean terms,
// all Boolean terms]. Reported at Drop as min / avg / max / last percentages.
static REL_SAMPLES: std::sync::Mutex<Vec<[u32; 4]>> = std::sync::Mutex::new(Vec::new());

/// `SEMPER_NO_INTERN_EQ=1`: do not link co-interned arithmetic drivers (the
/// behaviour before the intern-time equality fix; see `intern_by_node`).
/// `SEMPER_INTERN_EQ_LEGACY=1`: keep intern-time pairs emitted once per run
/// (the behaviour before the backtrack fix), for measurement.
fn intern_eq_legacy() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("SEMPER_INTERN_EQ_LEGACY").is_some())
}

fn intern_eq_disabled() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("SEMPER_NO_INTERN_EQ").is_some())
}

/// `SEMPER_REL_MEASURE=1`: sample the relevant slice once per matching
/// round (eager and complete-model rounds alike) for the `SEMPER_REL_RATIO`
/// report, without filtering any match. Independent of `SEMPER_RELEVANCY`.
/// Terms already written by `rel_dump`, and its round counter.
static REL_DUMPED_TERMS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
static REL_DUMP_ROUND: AtomicU64 = AtomicU64::new(0);

fn rel_measure() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("SEMPER_REL_MEASURE").is_some())
}

/// `SEMPER_REL_NOFILTER=1`: compute relevancy (with `SEMPER_RELEVANCY=1`)
/// but never let it decide matching or instantiation: the measurement mode.
fn rel_nofilter() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("SEMPER_REL_NOFILTER").is_some())
}

static REL_ITE_EQ_FIRED: AtomicU64 = AtomicU64::new(0);

/// Seed true instance bodies as relevancy roots (Z3's behaviour, see
/// `instance_roots`). On by default; `SEMPER_REL_NO_SEED_INSTANCES=1` turns it
/// off, for measuring its share of the relevant set.
fn rel_seed_instances() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("SEMPER_REL_NO_SEED_INSTANCES").is_none())
}

/// `SEMPER_REL_NOCLASS=1`: do not close relevancy over e-classes (Z3's rule
/// set marks expressions, not classes).
fn rel_noclass() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("SEMPER_REL_NOCLASS").is_some())
}

/// Incremental top-down matching (`SUNDANCE_INCR_MATCH=1`, or
/// `--incremental-matching`): a round matches a trigger only at root
/// candidates whose class, or a class within the pattern's depth below it,
/// gained a member or a term since the previous round. Every match a full
/// scan would find and that the previous round could not have found involves
/// such a class, so the filtered round produces the same new instances; the
/// instance dedup absorbs the rest. `SUNDANCE_INCR_MATCH_DIFF=1` runs the
/// full scan as well and reports every single-pattern call where the
/// filtered scan misses a match.
fn incr_match() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("SUNDANCE_INCR_MATCH").is_some())
}
fn incr_match_diff() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("SUNDANCE_INCR_MATCH_DIFF").is_some())
}
/// Root candidates the incremental filter skipped / considered, over the run.
static INCR_SKIPPED: AtomicU64 = AtomicU64::new(0);
static INCR_CONSIDERED: AtomicU64 = AtomicU64::new(0);
/// Single-pattern calls where the filtered scan missed a match of the full
/// scan (diff mode), and the matches missed.
static INCR_DIFF_CALLS: AtomicU64 = AtomicU64::new(0);
static INCR_DIFF_MISSED: AtomicU64 = AtomicU64::new(0);

/// Nesting depth of application patterns below the root (a flat pattern
/// `f(x, y)` has depth 0).
fn pattern_depth(p: &Pattern<u32>) -> u32 {
    match p {
        Pattern::App(_, subs) => subs.iter().map(|s| pattern_depth(s) + 1).max().unwrap_or(0),
        _ => 0,
    }
}

/// Relevancy follows each assignment (`note_assignment`); on by default,
/// `SEMPER_REL_NO_INCREMENTAL=1` restores the per-round refresh only.
fn rel_incremental() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("SEMPER_REL_NO_INCREMENTAL").is_none())
}

/// Re-apply every relevant gate's rule at the start of a round. On by
/// default; `SEMPER_REL_NO_GATE_RESCAN=1` leaves the gates to the
/// incremental hook alone (measures whether the rescan still finds marks).
fn rel_gate_rescan() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("SEMPER_REL_NO_GATE_RESCAN").is_none())
}

/// Upper bound on matches pulled from the engine in one `match_triggers`
/// call before bailing to the top-down matcher. A rooted trigger yields far
/// fewer; the cap only catches a query that enumerates without bound (an
/// unrooted or rooting-ineffective shape), so it never exhausts memory inside
/// the FFI callback. Measured need: without rooting, one call reached ~11GB.
const NATIVE_MATCH_PULL_CAP: u64 = 200_000;

/// Wall-time budget for one `match_triggers` native enumeration, in
/// milliseconds (0 = unbounded, SEMPER_NATIVE_MATCH_MS overrides). A rooted
/// leapfrog join is normally sub-millisecond, but a few Verus files
/// (MiniAllocator.12 and the other `calls=0 native=NONE` files) build a join
/// whose per-pull `enter`/`backtrack`/`search` cost makes a single call run
/// for the whole solver timeout, so the match never completes and the file
/// times out even though the top-down matcher handles it in ~1s. The budget
/// bails such a call to the top-down matcher, which is authoritative.
fn native_match_budget_ms() -> u64 {
    static BUDGET: std::sync::OnceLock<u64> = std::sync::OnceLock::new();
    *BUDGET.get_or_init(|| {
        std::env::var("SEMPER_NATIVE_MATCH_MS")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(2000)
    })
}

/// Largest number of distinct root classes for which the call site roots the
/// native query (one call per class); above it the single unrooted native
/// call bails to the top-down matcher, which scans the same candidates with
/// early termination. SEMPER_NATIVE_MAX_ROOTS overrides (0 = never bail).
fn native_max_roots() -> usize {
    static MAX_ROOTS: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *MAX_ROOTS.get_or_init(|| {
        std::env::var("SEMPER_NATIVE_MAX_ROOTS")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(64)
    })
}

thread_local! {
    /// Set while the native matcher's `catch_unwind` is in scope, so a matcher
    /// panic that is about to be caught and turned into a fallback does not
    /// also print through the panic hook (the message would be noise, and at
    /// Verus scale the formatting cost is not free).
    static SUPPRESS_PANIC_MSG: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}
static PANIC_HOOK_INIT: std::sync::Once = std::sync::Once::new();

/// Install, once, a panic hook that stays silent for panics raised while
/// `SUPPRESS_PANIC_MSG` is set and delegates to the previous hook otherwise.
fn install_quiet_native_panic_hook() {
    PANIC_HOOK_INIT.call_once(|| {
        let previous = std::panic::take_hook();
        std::panic::set_hook(Box::new(move |info| {
            if !SUPPRESS_PANIC_MSG.with(|c| c.get()) {
                previous(info);
            }
        }));
    });
}

/// Counters surfaced to the driver (`propagator.sync_external_stats` reads
/// `stats.merges`).
#[derive(Default)]
pub struct SemperStats {
    pub merges: u64,
}

/// Adapter-local symbol id, assigned once per distinct `Op` at the driver
/// boundary. `Op` owns a `String` for `App` and `Constant`, and a tuple key
/// such as `(Op, usize)` cannot be probed by reference, because `Borrow`
/// cannot produce a tuple of borrows. Keying on `(SymId, u32)` instead is what
/// keeps every lookup after registration on integers: probing the old tuple
/// key allocated and freed a `String` per call.
type SymId = u32;

/// The part of an `Op` the adapter still needs once the symbol is interned:
/// enough to drive Boolean descent and to pick the commutative registration
/// for `Eq`.
#[derive(Clone, Copy, PartialEq, Eq)]
enum SymKind {
    And,
    Or,
    Not,
    Implies,
    Ite,
    Eq,
    Other,
}

impl SymKind {
    fn of(op: &Op) -> Self {
        match op {
            Op::And => SymKind::And,
            Op::Or => SymKind::Or,
            Op::Not => SymKind::Not,
            Op::Implies => SymKind::Implies,
            Op::Ite => SymKind::Ite,
            Op::Eq => SymKind::Eq,
            _ => SymKind::Other,
        }
    }
}

/// Per-symbol data, indexed by `SymId`.
struct SymInfo {
    /// `Op::to_function_map_key()`, computed once per symbol. The registry
    /// name is this plus an arity suffix, built only when `ops` misses.
    base: Box<str>,
    kind: SymKind,
}

/// One driver-visible registration, replayable after a restore. Children are
/// driver ids, resolved through the terms table at replay time. The operator
/// is a `SymId`, not an `Op`: replay must not touch a string.
enum RegEvent {
    Term { sym: SymId, children: Vec<u32> },
    Opaque,
}

/// Snapshot taken on entering a decision level: the engine token plus the
/// lengths of the scoped logs. Registrations are not truncated — they replay.
struct LevelMark {
    token: EGraphToken,
    asserts_len: usize,
    diseqs_len: usize,
    reg_len: usize,
    rel_gates_len: usize,
    intern_eqs_len: usize,
}

pub struct SemperEgraph {
    eg: Eg,
    /// Set when the true=false-collision fallback produced a conflict (see
    /// `EgraphTrait::refutation_tainted`).
    tf_taint: bool,
    term_sort: SortId,
    /// `Op` -> `SymId`. The only map still keyed on an `Op`, and it is probed
    /// by reference, so probing never clones: the owned insert happens once
    /// per distinct symbol for the lifetime of the adapter.
    syms: FxHashMap<Op, SymId>,
    /// Per-symbol data, indexed by `SymId`. Monotone, and deliberately so: a
    /// symbol is a name, and names do not become invalid on restore. Unlike
    /// the engine's `OpRegistry`, which marks and restores a `completion`
    /// entry per op, this carries no per-entry restore state, so keeping it
    /// monotone costs one string per symbol and nothing on the mark path.
    sym_info: Vec<SymInfo>,
    /// Engine op interning, keyed by (symbol, arity): the same symbol can only
    /// recur at one arity per key, and registry names are mangled with the
    /// arity so `App("f")/1` and `Constant("f")/0` cannot collide.
    ops: FxHashMap<(SymId, u32), OpId>,
    /// Scratch for resolving a registration's children into engine nodes.
    /// Detached with `mem::take` around the `reg_log` borrow so `intern`
    /// allocates no vector per replayed term.
    child_buf: Vec<ENodeId>,
    /// Driver id -> current engine node. Append-only; entries above a
    /// restore point are repaired by replay, never removed.
    terms: Vec<ENodeId>,
    /// Engine node -> first driver id that produced it. Gives `find` a
    /// canonical driver id per class (the root node's first registrant), so
    /// the driver's `find(id) == id` is-representative idiom stays
    /// meaningful. Rebuilt after a restore, since replay can re-mint nodes.
    ///
    /// A dense `Vec` indexed by the engine node id, not a hash map: node ids
    /// are dense and `find` is on the hot path (one lookup per `find`), so an
    /// array index beats a hash probe. `NO_DRIVER` marks an index with no
    /// driver id yet. Profiling showed the hashed version's probe among the
    /// top non-CaDiCaL costs on backtrack-heavy runs.
    node_to_driver: Vec<u32>,
    reg_log: Vec<RegEvent>,
    opaque_count: usize,
    /// Asserted equalities; index i is the `Assumption` payload of merge i.
    asserts: Vec<(u32, u32)>,
    /// Asserted disequalities with the literal that asserted each.
    diseqs: Vec<(u32, u32, Lit)>,
    /// Cached class roots per disequality, making the per-assert violation
    /// check O(1) for the common entry: two distinct roots stay distinct
    /// until one is absorbed, and testing "still a root" is one parent read
    /// (`find_const` on a root terminates immediately). Entries are stamped
    /// with `epoch`; a restore bumps it, because a cached root above the
    /// restore point may name a deleted or re-minted node.
    diseq_roots: Vec<(ENodeId, ENodeId)>,
    diseq_epoch: Vec<u64>,
    epoch: u64,
    /// Conflict reporting is edge-triggered: a violated disequality is
    /// reported once, not on every subsequent assertion while it stays
    /// violated. Re-reporting queued a duplicate of the same theory clause
    /// per assertion until the backtrack — 24% more clauses than the basic
    /// backend on eq_diamond14 (10906 vs 8781), with the cost showing up as
    /// CaDiCaL clause-addition and propagation time. Cleared on backtrack;
    /// a violation that survives one (possible under chronological
    /// backtracking) is re-reported once, which is sound — the clause is
    /// already in the solver either way.
    reported_diseqs: rustc_hash::FxHashSet<usize>,
    reported_tf: bool,
    /// `register_eq` watches. Recorded for the future propagation hook; the
    /// driver does not consume `EgraphResult::propagations` yet.
    eq_watches: Vec<(u32, u32, Lit)>,
    patterns: Vec<Pattern<u32>>,
    /// (op, arity) -> driver ids of registered terms, for e-matching
    /// candidate enumeration. Built incrementally from `reg_log` up to
    /// `fn_index_upto`. Both live in driver-id space, which is
    /// backtrack-stable (terms are permanent), so the index survives
    /// restores without repair — the same reason `reg_log` replays work.
    fn_index: FxHashMap<(SymId, u32), Vec<u32>>,
    fn_index_upto: usize,
    /// Terms asserted at level 0: the input formula's top level, and the
    /// seeds of the relevancy slice. Level 0 takes no token, so these are
    /// never rolled back and the vector is append-only.
    root_terms: Vec<u32>,
    /// Bodies of quantifier instances (`note_instance_root`), append-only:
    /// instance clauses are never retracted. With `SEMPER_REL_SEED_INSTANCES=1`
    /// the slice also seeds every body whose current value is true, which is
    /// what Z3's root clause `(or (not q) body)` with relevancy watches does.
    instance_roots: Vec<u32>,
    /// Relevancy gating for e-matching (SEMPER_RELEVANCY=1). When enabled,
    /// match_triggers computes the relevant cone of the current assignment
    /// (Z3's witness rules, read off the merge state: a gate's truth value
    /// is whether its root is the true or false class) and skips candidates
    /// outside it. Off by default: on the quantifier regression suite the
    /// cone covers 99.6% of all terms (the problems are small and densely
    /// connected, so almost everything is relevant), it prunes 0% of 76843
    /// e-matching candidates, and it costs about 3% (50.6s vs 49.1s) with no
    /// change in files solved. The witness rules are correct (per-file slice
    /// ratio ranges down to 0.75, so pruning does happen where there is
    /// don't-care structure); this corpus just has almost none. Revive when a
    /// workload is measured to be match-dominated with large irrelevant
    /// subformulas — the regime where Z3's relevancy pays off.
    relevancy_enabled: bool,
    /// Whether relevancy filtering applies to the next match round. Set false by
    /// the propagator for the complete-model round so every match is produced
    /// there (a Boolean-irrelevant atom's theory content can still refute the
    /// model); set true for eager partial-assignment rounds. Only consulted when
    /// `relevancy_enabled`.
    relevancy_active: bool,
    /// Latched true once a native match call exceeds the time budget; disables
    /// native matching for the rest of the solve (falls back to top-down).
    native_time_bailed: std::cell::Cell<bool>,
    /// Whether the last `match_triggers` call was answered natively
    /// (instrumentation for the instance trace, see `EgraphTrait`).
    last_match_native: std::cell::Cell<bool>,
    /// The slice for the match round in progress; None when gating is off.
    /// Relevancy worklist: terms marked but whose rule is not yet applied.
    rel_queue: Vec<u32>,
    /// Relevant gates (and/or/implies/ite), re-checked each eager round;
    /// truncated on backtrack with the level marks.
    rel_gates: Vec<u32>,
    /// Gates each driver term is a direct child of (Z3's relevancy watches):
    /// `note_assignment` re-applies these gates' rules when the child gets a
    /// truth value. Append-only, like `reg_log`.
    rel_parents: Vec<Vec<u32>>,
    /// Instance bodies (`note_instance_root`), by driver term: marked by
    /// `note_assignment` the moment their literal becomes true.
    rel_instance_root: Vec<bool>,
    /// Incremental matching: each term's class name (`find`) at the start
    /// of the previous matching round; a term registered since has none.
    incr_snapshot: Vec<u32>,
    /// Parents of each driver term (terms having it as a direct child).
    /// Append-only, like `reg_log`.
    parents: Vec<Vec<u32>>,
    /// Pattern labels: (parent op, child position, child op) for every
    /// application below an application in a pattern, (parent op, position)
    /// for every variable position, and every application op. Keyed by
    /// `Op`, resolved to symbols at each round start (a symbol may be
    /// interned after the pattern compiles).
    pc_pairs: rustc_hash::FxHashSet<(Op, u32, Op)>,
    pc_var: rustc_hash::FxHashSet<(Op, u32)>,
    /// (parent op, position) of every ground sub-pattern: matched by class,
    /// so a merge on either side makes new matches.
    pc_ground: rustc_hash::FxHashSet<(Op, u32)>,
    pattern_ops: rustc_hash::FxHashSet<Op>,
    /// Terms marked relevant since the previous round: matchable now
    /// without any e-graph change, so they seed the round as Z3's
    /// `relevant_eh` matches a newly relevant term. Cleared at round start.
    incr_newly_relevant: Vec<u32>,
    /// Deepest pattern compiled so far.
    incr_max_depth: u32,
    /// Whether the filter applies to the round in progress (off until the
    /// first `begin_matching_round`).
    incr_active: bool,
    /// Candidates of the round, by (operator, arity): the terms whose class
    /// is a class-aware ancestor of a seed, with the level they enter at
    /// (`match_top` takes those at or below the pattern's depth).
    incr_cands: rustc_hash::FxHashMap<(SymId, u32), Vec<(u32, u32)>>,
    /// Round counter and, per pattern, the round it was last scanned in: a
    /// pattern not scanned in the previous round gets a full scan (its
    /// quantifier was unassigned or gated then, so matches over unchanged
    /// structure are new to the solver), as Z3 matches a newly activated
    /// pattern against the whole e-graph.
    incr_round: u64,
    incr_last_scanned: rustc_hash::FxHashMap<PatternId, u64>,
    /// Diff mode only: every match the full scan produced, per pattern, raw
    /// bindings.
    incr_seen:
        rustc_hash::FxHashMap<PatternId, Vec<crate::utils::DeterministicHashMap<Local, u32>>>,
    /// Read position in the engine's merge log (shared with the arithmetic
    /// export, which drains it).
    rel_merge_cursor: usize,
    /// Bumped on every relevancy change and shield toggle; part of the
    /// native index cache key, since the index build reads the shield.
    rel_epoch: u64,
    /// Relevancy-restricted branching (SEMPER_REL_DECIDE=1): when set,
    /// `suggest_decision` descends the relevant Boolean structure and returns
    /// the next atom to branch on with a justifying phase.
    decide_enabled: bool,
    /// E-matching is on by default. It was gated while the congruent-atom
    /// true=false explanation bug was open (unsound unsat on 2 quantifier
    /// files); after that fix a Z3-cross-checked sweep of the quantifier
    /// suite found 0 unsound answers across 99 definitive results, so it is
    /// enabled. SEMPER_EMATCH=0 turns it off (match_triggers returns nothing,
    /// quantified problems become sound-but-incomplete).
    ematch_enabled: bool,
    /// Native e-matching (SEMPER_NATIVE_EMATCH=1): route `match_triggers`
    /// through the engine's own matcher (compile the trigger to a semper
    /// pattern, resolve/schedule/index it, enumerate against the live graph)
    /// instead of the top-down reimplementation. Off by default while parity
    /// with the basic backend is being established.
    native_ematch: bool,
    /// Native-matcher index, cached across `match_triggers` calls and rebuilt
    /// only when the e-graph changed. `IndexStore::build` is O(nodes); files
    /// with thousands of trigger-match calls per solve cannot afford one build
    /// per call (the cause of the Verus-sample timeouts), and within an
    /// instantiation round the graph is stable, so one build serves every call.
    /// The key `(reg_log.len, asserts.len, epoch)` identifies the matchable
    /// state: terms are append-only, asserted equalities grow within a level and
    /// shrink on backtrack, and `epoch` bumps on every restore — an unchanged
    /// key means an unchanged e-graph.
    cached_index: Option<IndexStore<DefaultConfig>>,
    cached_index_key: (usize, usize, u64, u64),
    /// Stable per-class binding driver: class representative node -> the minimum
    /// (earliest-registered) driver id in that class. Rebuilt with the index
    /// (same key), so the O(terms) scan is paid once per e-graph change, not per
    /// `match_triggers` call. See the binding conversion in `match_triggers_native`.
    cached_class_min: Option<FxHashMap<ENodeId, u32>>,
    /// Current SAT decision level, advanced by `notify_new_decision_level`.
    level: usize,
    /// Materialized scopes, tagged with the level that first mutated the
    /// e-graph. Marking is lazy: a decision level that only does Boolean
    /// work never takes a token, so it costs nothing here — the engine's
    /// `mark` is time-O(parent-frame captures) across every sub-container,
    /// and CaDiCaL opens a level per decision. A level with no mark needs no
    /// undo: the state at its end equals the state at the last mark below it.
    marks: Vec<(usize, LevelMark)>,
    /// Scratch for proof extraction, reused across explanations.
    scratch: RefCell<ProofBuf<ENodeId>>,
    arithmetic_terms: Vec<u32>,
    /// Intern-time arithmetic equalities. Registration interns a term that
    /// is congruent to an existing node into that node without a merge, so
    /// a second arithmetic driver of one node never appears in the merge
    /// log and the arithmetic solver holds two unrelated variables for one
    /// e-node (measured on the regression file `subtraction.smt2`: the
    /// native matcher's instance `len(get_keys_or_pivots(node!))` interns
    /// into the goal's `len(s@)` node and the proof saturates to unknown).
    /// `intern_by_node` names the first arithmetic driver of each node;
    /// a later arithmetic driver of the same node is linked to it through
    /// `intern_eqs_pending`, drained with the merge equalities. The map is
    /// rebuilt on restore with `arith_roots`, since replay re-mints nodes.
    intern_by_node: FxHashMap<ENodeId, u32>,
    intern_eqs_emitted: rustc_hash::FxHashSet<(u32, u32)>,
    /// The pairs of `intern_eqs_emitted` in emission order. The arithmetic
    /// solver scopes each exported equality to the decision level it arrived
    /// at and drops it on backtrack, so a pair emitted above the backtrack
    /// level must be forgotten here and emitted again; keeping it in the
    /// emitted set for the whole run lost it for good (measured on
    /// `subtraction.smt2` under relevancy: the arithmetic model then
    /// separated two terms the e-graph had equal, and the run accepted an
    /// inconsistent model).
    intern_eqs_trail: Vec<(u32, u32)>,
    intern_eqs_pending: Vec<(u32, u32)>,
    incremental_arith: bool,
    /// Engine class roots currently tagged arithmetic, for Nelson-Oppen
    /// equality export. Seeded by `mark_arithmetic` and propagated through the
    /// engine's `merged_log` in `drain_arithmetic_equalities`: a class is
    /// arithmetic if any member is. Maintained incrementally because the
    /// pre-merge pairing cannot be recovered from `find` after rebuild; rebuilt
    /// from `arithmetic_terms` on `backtrack_to`, since the roots it names are
    /// undone (and possibly re-minted) by restore.
    arith_roots: rustc_hash::FxHashSet<ENodeId>,
    /// The driver's true/false constants, captured at registration. Their
    /// disequality is built in: the driver debug-asserts that a true/false
    /// merge never goes undetected, so the backend must report it as a
    /// conflict itself (with no disequality literal — the equality path
    /// alone is contradictory).
    true_term: Option<u32>,
    false_term: Option<u32>,
    pub stats: SemperStats,
}

// Profile surfacing for the H4a mark/restore fraction measurement: with
// SEMPER_PROF set, the engine accumulates mark/restore wall (see
// take_markrestore_profile) and this prints the totals when the solve tears
// the e-graph down, so a runner can divide them by the process wall.
impl Drop for SemperEgraph {
    fn drop(&mut self) {
        if std::env::var_os("SEMPER_PROF").is_some() {
            let (mark_ns, mark_calls, restore_ns, restore_calls) =
                semi_persistent_egraph::take_markrestore_profile();
            eprintln!(
                "SEMPER_PROF mark_ns={mark_ns} mark_calls={mark_calls} \
                 restore_ns={restore_ns} restore_calls={restore_calls}"
            );
        }
        if std::env::var_os("SEMPER_RESTORE_PROF").is_some() {
            let per = semi_persistent_egraph::take_restore_member_profile();
            let labels = semi_persistent_egraph::RESTORE_PROF_MEMBERS;
            let line: Vec<String> = labels
                .iter()
                .zip(per.iter())
                .map(|(l, ns)| format!("{l}={ns}"))
                .collect();
            eprintln!("SEMPER_RESTORE_PROF {}", line.join(" "));
            let per = semi_persistent_egraph::take_node_restore_profile();
            let labels = semi_persistent_egraph::NODE_PROF_PARTS;
            let line: Vec<String> = labels
                .iter()
                .zip(per.iter())
                .map(|(l, ns)| format!("{l}={ns}"))
                .collect();
            eprintln!("SEMPER_NODE_PROF {}", line.join(" "));
        }
        crate::egraphs::trail_prof::report("semper");
        if self.native_ematch {
            let calls = NATIVE_MATCH_CALLS.load(Ordering::Relaxed);
            let fallbacks = NATIVE_MATCH_FALLBACKS.load(Ordering::Relaxed);
            eprintln!(
                "SEMPER_NATIVE_EMATCH match_triggers calls={calls} fallbacks={fallbacks} terms={}",
                self.terms.len()
            );
        }
        if explain_audit() {
            eprintln!(
                "SEMPER_EXPLAIN_AUDIT conflicts={} invalid={} not_level0={} incomplete={} added_pairs={} unrecoverable={} tf_conflicts={} tf_invalid={} tf_not_level0={} tainted={}",
                EXPLAIN_AUDITED.load(Ordering::Relaxed),
                EXPLAIN_INVALID.load(Ordering::Relaxed),
                EXPLAIN_UNSOUND.load(Ordering::Relaxed),
                EXPLAIN_INCOMPLETE.load(Ordering::Relaxed),
                EXPLAIN_ADDED_PAIRS.load(Ordering::Relaxed),
                EXPLAIN_UNRECOVERABLE.load(Ordering::Relaxed),
                EXPLAIN_TF_AUDITED.load(Ordering::Relaxed),
                EXPLAIN_TF_INVALID.load(Ordering::Relaxed),
                EXPLAIN_TF_UNSOUND.load(Ordering::Relaxed),
                self.tf_taint,
            );
            eprintln!(
                "SEMPER_INTERN_AUDIT interns={} created_with_noncanonical_child={} nodes={}",
                INTERN_TOTAL.load(Ordering::Relaxed),
                INTERN_NONCANONICAL.load(Ordering::Relaxed),
                self.terms.len()
            );
        }
        if incr_match() {
            eprintln!(
                "SEMPER_INCR_MATCH skipped={} considered={} diff_calls={} diff_missed={}",
                INCR_SKIPPED.load(Ordering::Relaxed),
                INCR_CONSIDERED.load(Ordering::Relaxed),
                INCR_DIFF_CALLS.load(Ordering::Relaxed),
                INCR_DIFF_MISSED.load(Ordering::Relaxed)
            );
        }
        if self.relevancy_enabled || rel_measure() {
            eprintln!(
                "SEMPER_RELEVANCY refreshes={} assign_hooks={} rescan_marks={} marks={} skipped_candidates={} skipped_quantifiers={} relevant_gates={} nofilter={}",
                REL_REFRESHES.load(Ordering::Relaxed),
                REL_ASSIGN_HOOKS.load(Ordering::Relaxed),
                REL_RESCAN_MARKS.load(Ordering::Relaxed),
                REL_MARKS.load(Ordering::Relaxed),
                REL_SKIPPED_CANDIDATES.load(Ordering::Relaxed),
                REL_SKIPPED_QUANTIFIERS.load(Ordering::Relaxed),
                self.rel_gates.len(),
                rel_nofilter(),
            );
            let samples = REL_SAMPLES.lock().expect("rel samples");
            if !samples.is_empty() {
                let pct = |r: u32, t: u32| {
                    if t == 0 {
                        100.0
                    } else {
                        100.0 * r as f64 / t as f64
                    }
                };
                let all: Vec<f64> = samples.iter().map(|s| pct(s[0], s[1])).collect();
                let bools: Vec<f64> = samples.iter().map(|s| pct(s[2], s[3])).collect();
                let stat = |v: &[f64]| {
                    let min = v.iter().cloned().fold(f64::INFINITY, f64::min);
                    let max = v.iter().cloned().fold(f64::NEG_INFINITY, f64::max);
                    let avg = v.iter().sum::<f64>() / v.len() as f64;
                    (min, avg, max, v[v.len() - 1])
                };
                let (amin, aavg, amax, alast) = stat(&all);
                let (bmin, bavg, bmax, blast) = stat(&bools);
                let last = samples[samples.len() - 1];
                eprintln!(
                    "SEMPER_REL_RATIO samples={} noclass={} all_pct min={amin:.1} avg={aavg:.1} max={amax:.1} last={alast:.1} \
                     bool_pct min={bmin:.1} avg={bavg:.1} max={bmax:.1} last={blast:.1} last_counts rel={} terms={} rel_bool={} bool={} \
                     ite_eq_fired={} seed_instances={} instance_roots={}",
                    samples.len(),
                    rel_noclass(),
                    last[0],
                    last[1],
                    last[2],
                    last[3],
                    REL_ITE_EQ_FIRED.load(Ordering::Relaxed),
                    rel_seed_instances(),
                    self.instance_roots.len()
                );
            }
        }
    }
}

impl Default for SemperEgraph {
    fn default() -> Self {
        Self::new()
    }
}

impl SemperEgraph {
    pub fn new() -> Self {
        let mut eg = Eg::new();
        // One interned (hence non-concrete) sort for every term: the driver
        // enforces sort discipline upstream in yaspar, and the engine's sort
        // checks only require merge endpoints to agree.
        let term_sort = eg.sorts_mut().intern("SunTerm");
        // Relevancy carries marks across merges (closure), so it reads the
        // engine's merge log from the start.
        if std::env::var("SEMPER_RELEVANCY").is_ok_and(|v| v == "1") {
            eg.set_record_merges(true);
        }
        SemperEgraph {
            eg,
            tf_taint: false,
            term_sort,
            syms: FxHashMap::default(),
            sym_info: Vec::new(),
            ops: FxHashMap::default(),
            child_buf: Vec::new(),
            terms: Vec::new(),
            node_to_driver: Vec::new(),
            reg_log: Vec::new(),
            opaque_count: 0,
            asserts: Vec::new(),
            diseqs: Vec::new(),
            diseq_roots: Vec::new(),
            diseq_epoch: Vec::new(),
            epoch: 0,
            reported_diseqs: rustc_hash::FxHashSet::default(),
            reported_tf: false,
            eq_watches: Vec::new(),
            patterns: Vec::new(),
            fn_index: FxHashMap::default(),
            fn_index_upto: 0,
            root_terms: Vec::new(),
            instance_roots: Vec::new(),
            relevancy_enabled: std::env::var("SEMPER_RELEVANCY").is_ok_and(|v| v == "1"),
            relevancy_active: true,
            // Latched once a native match call exceeds the wall-time budget:
            // from then on this solve uses the top-down matcher directly,
            // instead of wasting the budget on every call of a join the engine
            // enumerates pathologically (the top-down matcher solves these
            // files in seconds). Cell so the catch_unwind closure can set it
            // through a shared borrow.
            native_time_bailed: std::cell::Cell::new(false),
            last_match_native: std::cell::Cell::new(false),
            rel_queue: Vec::new(),
            rel_gates: Vec::new(),
            rel_parents: Vec::new(),
            rel_instance_root: Vec::new(),
            incr_snapshot: Vec::new(),
            parents: Vec::new(),
            pc_pairs: rustc_hash::FxHashSet::default(),
            pc_var: rustc_hash::FxHashSet::default(),
            pc_ground: rustc_hash::FxHashSet::default(),
            pattern_ops: rustc_hash::FxHashSet::default(),
            incr_newly_relevant: Vec::new(),
            incr_max_depth: 0,
            incr_active: false,
            incr_cands: rustc_hash::FxHashMap::default(),
            incr_round: 0,
            incr_last_scanned: rustc_hash::FxHashMap::default(),
            incr_seen: rustc_hash::FxHashMap::default(),
            rel_merge_cursor: 0,
            rel_epoch: 0,
            decide_enabled: std::env::var("SEMPER_REL_DECIDE").is_ok_and(|v| v == "1"),
            ematch_enabled: std::env::var("SEMPER_EMATCH").map_or(true, |v| v != "0"),
            native_ematch: std::env::var("SEMPER_NATIVE_EMATCH").is_ok_and(|v| v == "1"),
            cached_index: None,
            cached_index_key: (usize::MAX, usize::MAX, u64::MAX, u64::MAX),
            cached_class_min: None,
            level: 0,
            marks: Vec::new(),
            scratch: RefCell::new(ProofBuf::new()),
            arithmetic_terms: Vec::new(),
            intern_by_node: FxHashMap::default(),
            intern_eqs_emitted: rustc_hash::FxHashSet::default(),
            intern_eqs_trail: Vec::new(),
            intern_eqs_pending: Vec::new(),
            incremental_arith: false,
            arith_roots: rustc_hash::FxHashSet::default(),
            true_term: None,
            false_term: None,
            stats: SemperStats::default(),
        }
    }

    fn node(&self, driver_id: u32) -> ENodeId {
        self.terms[driver_id as usize]
    }

    /// Intern an `Op` to its `SymId`, assigning one on first sight. This is
    /// the only place the adapter hashes an `Op`, and the only place it ever
    /// clones one: the probe borrows, and the insert happens once per symbol.
    fn sym_id(&mut self, op: &Op) -> SymId {
        if let Some(&sym) = self.syms.get(op) {
            return sym;
        }
        let sym = u32::try_from(self.sym_info.len()).expect("symbol table exceeds u32");
        self.sym_info.push(SymInfo {
            base: op.to_function_map_key().into_boxed_str(),
            kind: SymKind::of(op),
        });
        self.syms.insert(op.clone(), sym);
        sym
    }

    /// The `SymId` for an already-interned `Op`, without assigning one. A
    /// symbol that was never registered indexes no terms, so callers that are
    /// only probing an index treat `None` as "no candidates".
    fn sym_lookup(&self, op: &Op) -> Option<SymId> {
        self.syms.get(op).copied()
    }

    fn op_id(&mut self, sym: SymId, arity: usize) -> OpId {
        let arity_key = u32::try_from(arity).expect("arity fits u32");
        if let Some(&id) = self.ops.get(&(sym, arity_key)) {
            return id;
        }
        let info = &self.sym_info[sym as usize];
        let is_eq = info.kind == SymKind::Eq;
        // Every op is arity-indexed, And/Or included: AC-completion for the
        // connectives is done at the term layer (`cnf.rs::ac_and`/`ac_or`
        // flatten, sort and dedupe the children), not by an engine set op.
        // The engine-level variant (register_set("and"/"or")) was measured
        // and rejected: its positional conflation explainer tainted 98/99
        // regression files from unsat to unknown.
        let name = format!("{}${arity}", info.base);
        // The registry is the authority, the map only a cache: the registry
        // is semi-persistent, so a restore can drop ops registered in the
        // popped scopes, and `backtrack_to` clears the cache to match. An op
        // that survived the restore is found again by name; one that was
        // dropped is re-registered by the replay that needs it.
        let id = if let Some(id) = self.eg.ops().id_by_name(&name) {
            id
        } else if is_eq && arity == 2 {
            // Eq gets the commutative (sorted-pair) representation so both
            // argument orders intern to one node.
            self.eg
                .ops_mut()
                .register_c(&name, [self.term_sort, self.term_sort], self.term_sort)
        } else {
            let sorts = vec![self.term_sort; arity];
            self.eg.ops_mut().register(&name, &sorts, self.term_sort)
        };
        self.ops.insert((sym, arity_key), id);
        id
    }

    /// Intern one registration event into the engine, returning the node.
    /// Used both for first registration and for replay after a restore.
    fn intern(&mut self, event_index: usize) -> ENodeId {
        // Detach the scratch so resolving children borrows only `reg_log` and
        // `terms`, leaving `op_id` free to take `&mut self` afterwards. This
        // is what lets replay run without cloning the operator or allocating
        // a fresh child vector per term.
        let mut buf = std::mem::take(&mut self.child_buf);
        buf.clear();
        // Resolve the event while `reg_log` is borrowed, then drop the borrow
        // before anything needs `&mut self`. The symbol is a `Copy` id, so
        // nothing has to be cloned out of the log to survive the match.
        let sym = match &self.reg_log[event_index] {
            RegEvent::Term { sym, children } => {
                buf.extend(children.iter().map(|&c| self.terms[c as usize]));
                Some(*sym)
            }
            RegEvent::Opaque => None,
        };
        let node = match sym {
            Some(sym) => {
                let op_id = self.op_id(sym, buf.len());
                if explain_audit() {
                    // Creation under existing merges: `add` stores each child's
                    // class root, and keeps no history of the child it was
                    // given (history is written only on rebuild).
                    INTERN_TOTAL.fetch_add(1, Ordering::Relaxed);
                    if buf.iter().any(|&c| self.eg.find_const(c) != c) {
                        INTERN_NONCANONICAL.fetch_add(1, Ordering::Relaxed);
                    }
                }
                self.eg.add(op_id, &buf)
            }
            None => {
                // A unique nullary op per opaque index keeps replay
                // deterministic: the same event re-interns the same symbol.
                // Lookup-or-register for the same reason as `op_id`: a
                // restore between two replays of this event drops and
                // re-creates the registry entry.
                let name = format!("opaque${event_index}");
                let op_id = match self.eg.ops().id_by_name(&name) {
                    Some(id) => id,
                    None => self.eg.ops_mut().register(&name, &[], self.term_sort),
                };
                self.eg.add(op_id, &[])
            }
        };
        self.child_buf = buf;
        node
    }

    fn push_registration(&mut self, event: RegEvent) -> u32 {
        self.reg_log.push(event);
        let before = self.eg.node_count();
        let node = self.intern(self.reg_log.len() - 1);
        self.rel_shield_if_fresh(node, before);
        let driver_id = u32::try_from(self.terms.len()).expect("driver term table exceeds u32");
        self.terms.push(node);
        self.set_node_driver(node, driver_id);
        if let RegEvent::Term { children, .. } = &self.reg_log[driver_id as usize] {
            for &c in children.clone().iter() {
                let c = c as usize;
                if c >= self.parents.len() {
                    self.parents.resize_with(c + 1, Vec::new);
                }
                self.parents[c].push(driver_id);
            }
        }
        if self.relevancy_enabled && self.rel_is_gate(driver_id) {
            if let RegEvent::Term { children, .. } = &self.reg_log[driver_id as usize] {
                for &c in children.clone().iter() {
                    let c = c as usize;
                    if c >= self.rel_parents.len() {
                        self.rel_parents.resize_with(c + 1, Vec::new);
                    }
                    self.rel_parents[c].push(driver_id);
                }
            }
        }
        driver_id
    }

    /// Whether driver term `t` is a gate (and/or/implies/ite).
    fn rel_is_gate(&self, t: u32) -> bool {
        matches!(
            &self.reg_log[t as usize],
            RegEvent::Term { sym, .. }
                if matches!(
                    self.sym_info[*sym as usize].kind,
                    SymKind::And | SymKind::Or | SymKind::Implies | SymKind::Ite
                )
        )
    }

    /// `t` was just given a truth value: carry the merges, re-apply `t`'s own
    /// rule if it is a relevant gate, and the rule of every relevant gate `t`
    /// is a child of (`t` may now be a witness, chosen at the time it became
    /// true, as Z3 chooses). Then propagate.
    fn rel_on_assignment(&mut self, t: u32) {
        if !self.relevancy_enabled || !rel_incremental() {
            return;
        }
        REL_ASSIGN_HOOKS.fetch_add(1, Ordering::Relaxed);
        self.rel_absorb_merges();
        // An instance body is a root once true (Z3 asserts the instance as a
        // root clause with relevancy watches).
        if rel_seed_instances()
            && self
                .rel_instance_root
                .get(t as usize)
                .copied()
                .unwrap_or(false)
            && (t as usize) < self.terms.len()
        {
            let tr = self.true_term.map(|x| self.eg.find_const(self.node(x)));
            let fr = self.false_term.map(|x| self.eg.find_const(self.node(x)));
            if self.bool_value(t, tr, fr) == Some(true) {
                self.rel_mark(t);
            }
        }
        if self.eg.is_node_matchable(self.node(t)) && self.rel_is_gate(t) {
            self.rel_apply(t);
        }
        if let Some(parents) = self.rel_parents.get(t as usize) {
            let parents = parents.clone();
            for g in parents {
                if self.eg.is_node_matchable(self.node(g)) {
                    self.rel_apply(g);
                }
            }
        }
        self.rel_propagate();
    }

    /// Record the first driver id for an engine node (first-registrant wins),
    /// growing the dense map as needed.
    fn set_node_driver(&mut self, node: ENodeId, driver_id: u32) {
        let idx = node.to_usize();
        if idx >= self.node_to_driver.len() {
            self.node_to_driver.resize(idx + 1, NO_DRIVER);
        }
        if self.node_to_driver[idx] == NO_DRIVER {
            self.node_to_driver[idx] = driver_id;
        }
    }

    /// Take a token for the current level if it has none yet. Every mutating
    /// entry point calls this first, which is what makes marking lazy.
    fn ensure_scope(&mut self) {
        if self.level == 0 {
            return;
        }
        if self.marks.last().is_some_and(|&(l, _)| l >= self.level) {
            return;
        }
        let mark = LevelMark {
            token: self.eg.mark(ShrinkPolicy::Never),
            asserts_len: self.asserts.len(),
            diseqs_len: self.diseqs.len(),
            reg_len: self.reg_log.len(),
            rel_gates_len: self.rel_gates.len(),
            intern_eqs_len: self.intern_eqs_trail.len(),
        };
        self.marks.push((self.level, mark));
    }

    /// The asserted-equality pairs whose merges (closed under congruence)
    /// force `find(a) == find(b)`.
    fn explain_pairs(&self, a: u32, b: u32) -> Vec<(u32, u32)> {
        let mut buf = self.scratch.borrow_mut();
        buf.steps.clear();
        let ok = self.eg.explain_deep(self.node(a), self.node(b), &mut buf);
        if !ok {
            // `explain` returns false on a `PROOFS = false` e-graph
            // (containers-verus `union_find.rs`), not only on unequal
            // classes. The closure is generated by exactly the live assert
            // trail, so the whole trail is a sound (maximal) antecedent set.
            // Without this the release build emitted an empty conflict clause
            // on a proofs-off e-graph: immediate UNSAT on satisfiable inputs
            // (measured on 2 of 3 `:status sat` files).
            // With PROOFS on, `explain` fails only on unequal classes, which
            // the callers never pass; the fallback is then unreachable.
            return self.asserts.clone();
        }
        // Proof-path order, deduplicated by first occurrence. Sorted order
        // was also tried on the hypothesis that antecedent order steers
        // CaDiCaL's watched literals onto a different search trajectory:
        // measured no difference on the 103-file subset (11.9s vs 11.7s,
        // run noise), so the choice between them is free. Path order is
        // kept because the dedup is O(k) against the sort's O(k log k).
        let mut seen: rustc_hash::FxHashSet<(u32, u32)> = rustc_hash::FxHashSet::default();
        buf.steps
            .iter()
            .filter_map(|&(_, _, j)| match j {
                Justification::Assumption { lit } => Some(self.asserts[lit.as_usize()]),
                _ => None,
            })
            .filter(|&p| seen.insert(p))
            .collect()
    }

    /// A complete antecedent set for `a = b`, as driver-term equalities, and
    /// whether some step could not be recovered (the caller taints).
    ///
    /// The engine's forest path is over NODES, and a node's stored children
    /// are the class representatives its children had when it was interned,
    /// not the driver term's own children. Two consequences, each a source of
    /// equalities the path uses but never cites: (1) a congruence step between
    /// nodes A and B compares their stored children, so the equalities between
    /// the creator terms' actual children (`r@` against `route(..)` when the
    /// node of `(< r@ ..)` stored `route(..)`'s class) are missing; (2) a term
    /// that interned onto a node another term created equals that creator
    /// only through such child equalities. This closes both: every congruence
    /// step adds its creator terms' child pairs, every cited term is paired
    /// with its node's creator, and pairs on one node are expanded child by
    /// child, recursively, until every pair is explained by assumptions.
    /// Measured with `SEMPER_EXPLAIN_AUDIT=1` (the congruence-closure check of
    /// each antecedent set); `SEMPER_EXPLAIN_LEGACY=1` restores the old
    /// path-only explanation.
    fn explain_complete(&self, a: u32, b: u32) -> (Vec<(u32, u32)>, bool) {
        let mut out: Vec<(u32, u32)> = Vec::new();
        let mut tainted = false;
        let mut todo: Vec<(u32, u32)> = vec![(a, b)];
        let mut done: rustc_hash::FxHashSet<(u32, u32)> = rustc_hash::FxHashSet::default();
        let mut aligned: rustc_hash::FxHashSet<u32> = rustc_hash::FxHashSet::default();
        let mut cited: Vec<u32> = vec![a, b];
        loop {
            // Align every cited term to the creator of its node.
            while let Some(t) = cited.pop() {
                if !aligned.insert(t) {
                    continue;
                }
                match self.node_driver(self.node(t)) {
                    Some(r) if r != t => todo.push((t, r)),
                    Some(_) => {}
                    None => tainted = true,
                }
            }
            let Some((x, y)) = todo.pop() else { break };
            if x == y || !done.insert((x.min(y), x.max(y))) {
                continue;
            }
            if self.node(x) == self.node(y) {
                // Same node, different terms: equal through their children.
                let cx = self.reg_children(x).to_vec();
                let cy = self.reg_children(y).to_vec();
                if cx.len() != cy.len() {
                    tainted = true;
                    continue;
                }
                for (i, &c) in cx.iter().enumerate() {
                    let rc = self.eg.find_const(self.node(c));
                    let partner = if self.eg.find_const(self.node(cy[i])) == rc {
                        Some(cy[i])
                    } else {
                        cy.iter()
                            .copied()
                            .find(|&d| self.eg.find_const(self.node(d)) == rc)
                    };
                    match partner {
                        Some(d) => {
                            todo.push((c, d));
                            cited.push(c);
                            cited.push(d);
                        }
                        None => tainted = true,
                    }
                }
                continue;
            }
            let mut buf = self.scratch.borrow_mut();
            buf.steps.clear();
            if !self.eg.explain_deep(self.node(x), self.node(y), &mut buf) {
                // Proofs-off e-graph: the whole trail is a sound antecedent set.
                return (self.asserts.clone(), false);
            }
            let steps: Vec<_> = buf.steps.clone();
            drop(buf);
            for (na, nb, j) in steps {
                match j {
                    Justification::Assumption { lit } => {
                        let (p, q) = self.asserts[lit.as_usize()];
                        out.push((p, q));
                        cited.push(p);
                        cited.push(q);
                    }
                    Justification::Congruence { .. } => {
                        match (self.node_driver(na), self.node_driver(nb)) {
                            (Some(ca), Some(cb)) => {
                                // The creators sit on different nodes; pair
                                // them through their children by expanding
                                // as if they shared one (same op, congruent).
                                if ca != cb {
                                    let cx = self.reg_children(ca).to_vec();
                                    let cy = self.reg_children(cb).to_vec();
                                    if cx.len() != cy.len() {
                                        tainted = true;
                                    } else {
                                        for (i, &c) in cx.iter().enumerate() {
                                            let rc = self.eg.find_const(self.node(c));
                                            let partner =
                                                if self.eg.find_const(self.node(cy[i])) == rc {
                                                    Some(cy[i])
                                                } else {
                                                    cy.iter().copied().find(|&d| {
                                                        self.eg.find_const(self.node(d)) == rc
                                                    })
                                                };
                                            match partner {
                                                Some(d) => {
                                                    todo.push((c, d));
                                                    cited.push(c);
                                                    cited.push(d);
                                                }
                                                None => tainted = true,
                                            }
                                        }
                                    }
                                }
                                cited.push(ca);
                                cited.push(cb);
                            }
                            _ => tainted = true,
                        }
                    }
                    _ => tainted = true,
                }
            }
        }
        let mut seen: rustc_hash::FxHashSet<(u32, u32)> = rustc_hash::FxHashSet::default();
        out.retain(|&p| seen.insert(p));
        (out, tainted)
    }

    /// The conflict explanation used by the driver: complete by default,
    /// the old path-only one with `SEMPER_EXPLAIN_LEGACY=1`.
    fn explain_conflict(&mut self, a: u32, b: u32) -> Vec<(u32, u32)> {
        if explain_legacy() {
            return self.explain_pairs(a, b);
        }
        let (eqs, tainted) = self.explain_complete(a, b);
        if tainted {
            self.taint();
        }
        eqs
    }

    /// Explain a true=false collision completely.
    ///
    /// The base forest path's assumption leaves are facts about specific
    /// terms, but a term that interned onto a node created by a
    /// syntactically different term is only equal to that node's other
    /// residents under earlier merges the forest never recorded as edges.
    /// `align_to_creator` recovers those implicit equalities for every term
    /// the antecedent set cites, transitively.
    fn explain_true_false(&mut self, t: u32, f: u32) -> Vec<(u32, u32)> {
        let mut out = self.explain_pairs(t, f);
        let tf = [t, f];
        // Every assumption pair is a fact about its TERMS, but the forest path
        // it justifies runs over NODES. A term that interned onto a node some
        // OTHER term created (hash-cons keys on canonical children, so merely
        // class-equal children suffice) carries an implicit equality to that
        // creator term whose justification the forest never recorded. Align
        // every cited term to its node's first registrant, recursively; the
        // first registrant's syntax matches the node, so each chain grounds
        // out in assumptions. The worklist also aligns the terms cited by the
        // pairs the alignment itself appends.
        let mut visited: rustc_hash::FxHashSet<(u32, u32)> = rustc_hash::FxHashSet::default();
        let mut aligned: rustc_hash::FxHashSet<u32> = rustc_hash::FxHashSet::default();
        let mut i = 0;
        while i < out.len() {
            let (a, b) = out[i];
            i += 1;
            for x in [a, b] {
                if aligned.insert(x) {
                    self.align_to_creator(x, &mut out, &mut visited);
                }
            }
        }
        // Drop any incidental references to the true/false constants and dedup.
        out.retain(|&(a, b)| !tf.contains(&a) || !tf.contains(&b));
        let mut seen: rustc_hash::FxHashSet<(u32, u32)> = rustc_hash::FxHashSet::default();
        out.retain(|&p| seen.insert(p));
        out
    }

    /// Scan the disequality log for one violated by the current classes.
    ///
    /// The specific disequalities are checked BEFORE the built-in true/false
    /// pair, and this order is load-bearing for soundness. Two equality atoms
    /// that are syntactically different but whose arguments have merged
    /// hash-cons to one engine node; asserting them to opposite truth values
    /// then merges that node with both true and false. Explaining that
    /// true=false collision directly walks a forest path of just the two
    /// atom=truth-value assumptions (there is no congruence edge to expand,
    /// because congruent terms share a node), which OMITS the argument
    /// equalities that made the atoms congruent and yields an unsound clause.
    /// Every such collision is backed by a specific disequality (the atom
    /// asserted false registered one on its sides), and explaining THAT pair
    /// walks the argument merges, so checking specific disequalities first
    /// produces the complete, sound antecedent set. The true/false check
    /// stays as a fallback for collisions no specific disequality covers
    /// (e.g. non-equality Boolean terms). Per-entry cost is two parent reads
    /// via the cached roots.
    /// The first registrant of an engine node: the term whose registration
    /// created it, so the one whose syntax the node's stored children match.
    fn node_driver(&self, node: ENodeId) -> Option<u32> {
        let d = *self.node_to_driver.get(node.to_usize())?;
        (d != NO_DRIVER).then_some(d)
    }

    /// Explain the implicit equality between term `x` and the first
    /// registrant of `node(x)`: nothing when `x` created the node itself;
    /// otherwise `x` interned onto it because its children were class-equal
    /// to the creator's at intern time, an equality judgment the forest never
    /// recorded as an edge. Matches the two terms' registered children by
    /// class, explains each matched pair, and aligns the matched children to
    /// THEIR creators, because the same conflation can occur at any depth.
    /// Terminates: the creator registered first, so ids strictly decrease
    /// along every chain, and `visited` deduplicates. A child it cannot match
    /// taints the run (see `EgraphTrait::refutation_tainted`).
    fn align_to_creator(
        &mut self,
        x: u32,
        extra: &mut Vec<(u32, u32)>,
        visited: &mut rustc_hash::FxHashSet<(u32, u32)>,
    ) {
        let r = self.node_driver(self.node(x));
        let Some(r) = r else {
            // A cited term's node has no recorded first registrant: cannot
            // recover the conflation. Taint.
            self.taint();
            return;
        };
        if r == x {
            return;
        }
        self.expand_syntactic_pair(x, r, extra, visited);
    }

    /// Recover the argument equalities behind two syntactically different
    /// terms that HASH-CONSED to one node (so the forest has no edge between
    /// them and a plain path walk omits why they are equal). See
    /// `align_to_creator` for the recursion and termination argument.
    fn expand_syntactic_pair(
        &mut self,
        x: u32,
        y: u32,
        extra: &mut Vec<(u32, u32)>,
        visited: &mut rustc_hash::FxHashSet<(u32, u32)>,
    ) {
        if !visited.insert((x.min(y), x.max(y))) {
            return;
        }
        let cx = self.reg_children(x).to_vec();
        let cy = self.reg_children(y).to_vec();
        if cx.len() != cy.len() {
            // Cannot expand: the antecedent set may be missing the equalities
            // behind the collision. Taint the run so an unsat that leans on
            // this clause degrades to unknown.
            self.taint();
            return;
        }
        for (i, &a) in cx.iter().enumerate() {
            // Prefer the positional partner; fall back to any class-matching
            // one (commutative orientation).
            let partner =
                if self.eg.find_const(self.node(a)) == self.eg.find_const(self.node(cy[i])) {
                    Some(cy[i])
                } else {
                    cy.iter().copied().find(|&b| {
                        self.eg.find_const(self.node(a)) == self.eg.find_const(self.node(b))
                    })
                };
            match partner {
                Some(b) => {
                    if a != b {
                        extra.extend(self.explain_pairs(a, b));
                    }
                    // The matched children are themselves cited terms now:
                    // their own intern-time conflations need explaining too.
                    self.align_to_creator(a, extra, visited);
                    self.align_to_creator(b, extra, visited);
                }
                None => {
                    // No class-matching partner: cannot fully recover. Taint.
                    self.taint();
                }
            }
        }
    }

    /// `SEMPER_EXPLAIN_AUDIT=1`: for an ordinary disequality conflict, run
    /// the intern-time alignment that `explain_true_false` applies (without
    /// changing the conflict or the taint flag) and count the conflicts whose
    /// plain forest explanation omits an equality the alignment adds, or cites
    /// a conflation the alignment cannot recover. Measurement only.
    fn audit_explanation(&mut self, t1: u32, t2: u32, base: &[(u32, u32)]) {
        let saved_taint = self.tf_taint;
        self.tf_taint = false;
        let mut out: Vec<(u32, u32)> = base.to_vec();
        out.push((t1, t2));
        let mut visited: rustc_hash::FxHashSet<(u32, u32)> = rustc_hash::FxHashSet::default();
        let mut aligned: rustc_hash::FxHashSet<u32> = rustc_hash::FxHashSet::default();
        let mut i = 0;
        while i < out.len() {
            let (a, b) = out[i];
            i += 1;
            for x in [a, b] {
                if aligned.insert(x) {
                    self.align_to_creator(x, &mut out, &mut visited);
                }
            }
        }
        let unrecoverable = self.tf_taint;
        self.tf_taint = saved_taint;
        let base_set: rustc_hash::FxHashSet<(u32, u32)> = base.iter().copied().collect();
        let added = out[base.len() + 1..]
            .iter()
            .filter(|p| !base_set.contains(p) && !base_set.contains(&(p.1, p.0)))
            .count();
        EXPLAIN_AUDITED.fetch_add(1, Ordering::Relaxed);
        if !self.explanation_entails(base, t1, t2) {
            EXPLAIN_INVALID.fetch_add(1, Ordering::Relaxed);
            if !self.valid_modulo_level0(base, t1, t2) {
                EXPLAIN_UNSOUND.fetch_add(1, Ordering::Relaxed);
                self.dump_invalid("diseq NOT valid modulo level 0", base, t1, t2);
            }
        }
        if added > 0 {
            EXPLAIN_INCOMPLETE.fetch_add(1, Ordering::Relaxed);
            EXPLAIN_ADDED_PAIRS.fetch_add(added as u64, Ordering::Relaxed);
        }
        if unrecoverable {
            EXPLAIN_UNRECOVERABLE.fetch_add(1, Ordering::Relaxed);
        }
    }

    /// Whether the equalities `eqs` entail `x = y` by congruence closure over
    /// the registered (syntactic) terms alone: union the pairs, then merge any
    /// two cited-or-reachable terms with the same symbol whose children are
    /// pairwise equal, to a fixpoint. This is the validity test of an
    /// antecedent set; the e-graph's own path may rely on intern-time
    /// conflations that this check does not assume. Measurement only.
    fn explanation_entails(&self, eqs: &[(u32, u32)], x: u32, y: u32) -> bool {
        // Collect every term reachable from the cited ones.
        let mut terms: Vec<u32> = Vec::new();
        let mut seen: rustc_hash::FxHashSet<u32> = rustc_hash::FxHashSet::default();
        let mut stack: Vec<u32> = eqs
            .iter()
            .flat_map(|&(a, b)| [a, b])
            .chain([x, y])
            .collect();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            terms.push(t);
            stack.extend(self.reg_children(t).iter().copied());
        }
        let idx: FxHashMap<u32, usize> = terms.iter().enumerate().map(|(i, &t)| (t, i)).collect();
        let mut parent: Vec<usize> = (0..terms.len()).collect();
        fn find(p: &mut [usize], mut i: usize) -> usize {
            while p[i] != i {
                p[i] = p[p[i]];
                i = p[i];
            }
            i
        }
        for &(a, b) in eqs {
            let (ra, rb) = (find(&mut parent, idx[&a]), find(&mut parent, idx[&b]));
            parent[ra] = rb;
        }
        // Congruence to a fixpoint (quadratic per pass; audit inputs are small).
        let key = |s: &Self, t: u32| match &s.reg_log[t as usize] {
            RegEvent::Term { sym, children } => Some((*sym, children.len())),
            RegEvent::Opaque => None,
        };
        loop {
            let mut changed = false;
            let mut sig: FxHashMap<(u32, Vec<usize>), usize> = FxHashMap::default();
            for (i, &t) in terms.iter().enumerate() {
                let Some((sym, _)) = key(self, t) else {
                    continue;
                };
                let mut ch: Vec<usize> = self
                    .reg_children(t)
                    .iter()
                    .map(|c| find(&mut parent, idx[c]))
                    .collect();
                // `=` is registered commutatively (one node for both
                // orientations), so its signature is order-free.
                if self.sym_info[sym as usize].kind == SymKind::Eq {
                    ch.sort_unstable();
                }
                let k = (sym as u32, ch);
                if let Some(&j) = sig.get(&k) {
                    let (ri, rj) = (find(&mut parent, i), find(&mut parent, j));
                    if ri != rj {
                        parent[ri] = rj;
                        changed = true;
                    }
                } else {
                    sig.insert(k, i);
                }
            }
            if !changed {
                break;
            }
        }
        find(&mut parent, idx[&x]) == find(&mut parent, idx[&y])
    }

    /// S-expression of a registered term, cut at `depth` (audit dumps).
    fn fmt_term(&self, t: u32, depth: usize) -> String {
        match &self.reg_log[t as usize] {
            RegEvent::Opaque => format!("#opaque{t}"),
            RegEvent::Term { sym, children } => {
                let name = &self.sym_info[*sym as usize].base;
                if children.is_empty() {
                    format!("{name}")
                } else if depth == 0 {
                    format!("({name} ...)#{t}")
                } else {
                    let cs: Vec<String> = children
                        .iter()
                        .map(|&c| self.fmt_term(c, depth - 1))
                        .collect();
                    format!("({name} {})", cs.join(" "))
                }
            }
        }
    }

    /// Print an explanation the audit rejected (`SEMPER_EXPLAIN_AUDIT=2`,
    /// first 5): the conflict, the antecedent pairs, and the justification
    /// kinds of the engine's path between the two terms.
    /// An explanation the congruence check rejected: is it valid once every
    /// level-0 assertion is added? Level-0 facts hold in every model, so an
    /// explanation that only omits them still yields a sound clause; one that
    /// omits a decision-level equality does not.
    fn valid_modulo_level0(&self, eqs: &[(u32, u32)], x: u32, y: u32) -> bool {
        let level0_len = self
            .marks
            .first()
            .map_or(self.asserts.len(), |(_, m)| m.asserts_len);
        let mut all: Vec<(u32, u32)> = eqs.to_vec();
        all.extend_from_slice(&self.asserts[..level0_len]);
        self.explanation_entails(&all, x, y)
    }

    fn dump_invalid(&self, kind: &str, eqs: &[(u32, u32)], x: u32, y: u32) {
        static DUMPED: AtomicU64 = AtomicU64::new(0);
        if std::env::var("SEMPER_EXPLAIN_AUDIT").as_deref() != Ok("2")
            || DUMPED.fetch_add(1, Ordering::Relaxed) >= 5
        {
            return;
        }
        eprintln!(
            "AUDIT-INVALID {kind}: {} = {}  [terms #{x} #{y}, nodes {:?} {:?}]",
            self.fmt_term(x, 3),
            self.fmt_term(y, 3),
            self.node(x),
            self.node(y)
        );
        for &(a, b) in eqs {
            eprintln!(
                "  eq #{a} #{b}: {} = {}",
                self.fmt_term(a, 3),
                self.fmt_term(b, 3)
            );
        }
        let mut buf = self.scratch.borrow_mut();
        buf.steps.clear();
        let ok = self.eg.explain_deep(self.node(x), self.node(y), &mut buf);
        // First congruence step whose creator-child pairs the antecedents do
        // not entail: print both creators' children (as nodes) against the
        // engine's recorded premises for the two nodes.
        let steps_copy: Vec<_> = buf.steps.clone();
        for (_, _, j) in &steps_copy {
            if let Justification::Congruence { node_a, node_b } = j {
                let (Some(ca), Some(cb)) = (self.node_driver(*node_a), self.node_driver(*node_b))
                else {
                    eprintln!("  congruence {node_a:?}-{node_b:?}: a node without creator");
                    continue;
                };
                let (xa, xb) = (
                    self.reg_children(ca).to_vec(),
                    self.reg_children(cb).to_vec(),
                );
                let bad = xa.len() != xb.len()
                    || xa
                        .iter()
                        .zip(xb.iter())
                        .any(|(&p, &q)| p != q && !self.explanation_entails(eqs, p, q));
                if bad {
                    let na: Vec<ENodeId> = xa.iter().map(|&c| self.node(c)).collect();
                    let nb: Vec<ENodeId> = xb.iter().map(|&c| self.node(c)).collect();
                    eprintln!(
                        "  FIRST UNENTAILED congruence {node_a:?}(#{ca}) - {node_b:?}(#{cb})"
                    );
                    eprintln!(
                        "    creator a children nodes {na:?}, engine premises {:?}",
                        self.eg.original_children(*node_a)
                    );
                    eprintln!(
                        "    creator b children nodes {nb:?}, engine premises {:?}",
                        self.eg.original_children(*node_b)
                    );
                    eprintln!("    a: {}", self.fmt_term(ca, 2));
                    eprintln!("    b: {}", self.fmt_term(cb, 2));
                    if let Some((p, q)) = xa
                        .iter()
                        .copied()
                        .zip(xb.iter().copied())
                        .find(|&(p, q)| p != q && !self.explanation_entails(eqs, p, q))
                    {
                        eprintln!(
                            "    unentailed child pair #{p} {} = #{q} {}",
                            self.fmt_term(p, 2),
                            self.fmt_term(q, 2)
                        );
                        let mut b2 = ProofBuf::new();
                        let ok2 = self.eg.explain_deep(self.node(p), self.node(q), &mut b2);
                        eprintln!("    its engine path ok={ok2}, {} steps", b2.steps.len());
                        for (x, y, jj) in b2.steps.iter().take(12) {
                            let what = match jj {
                                Justification::Assumption { lit } => {
                                    let (u, v) = self.asserts[lit.as_usize()];
                                    let in_eqs = eqs.contains(&(u, v)) || eqs.contains(&(v, u));
                                    format!(
                                        "assumption #{u} #{v} in_antecedents={in_eqs}: {} = {}",
                                        self.fmt_term(u, 1),
                                        self.fmt_term(v, 1)
                                    )
                                }
                                other => format!("{other:?}"),
                            };
                            eprintln!("      {x:?}-{y:?}: {what}");
                        }
                    }
                    break;
                }
            }
        }
        eprintln!("  engine path ok={ok}, {} steps:", buf.steps.len());
        for (a, b, j) in buf.steps.iter() {
            let what = match j {
                Justification::Assumption { lit } => {
                    let (p, q) = self.asserts[lit.as_usize()];
                    format!(
                        "assumption #{p} #{q}: {} = {}",
                        self.fmt_term(p, 2),
                        self.fmt_term(q, 2)
                    )
                }
                other => format!("{other:?}"),
            };
            let da = self
                .node_to_driver
                .get(a.to_usize())
                .copied()
                .unwrap_or(NO_DRIVER);
            let db = self
                .node_to_driver
                .get(b.to_usize())
                .copied()
                .unwrap_or(NO_DRIVER);
            eprintln!("    {a:?}(#{da})-{b:?}(#{db}): {what}");
        }
    }

    fn violated_diseq(&mut self) -> Option<Conflict<u32>> {
        // Observe the implicit true != false collision before scanning the
        // ordinary disequalities. A single merge can both violate an ordinary
        // disequality and collapse true into false; the loop below returns the
        // ordinary conflict first, so unless the coincident true=false merge is
        // latched here it goes unrecorded, and a later same-level assignment
        // that returns no conflict trips the "merged without detection"
        // invariant in process_assignment.
        let tf_pair = match (self.true_term, self.false_term) {
            (Some(t), Some(f))
                if self.eg.find_const(self.node(t)) == self.eg.find_const(self.node(f)) =>
            {
                Some((t, f))
            }
            _ => None,
        };
        for i in 0..self.diseqs.len() {
            if self.reported_diseqs.contains(&i) {
                continue;
            }
            let (t1, t2, lit) = self.diseqs[i];
            let (r1, r2) = if self.diseq_epoch[i] == self.epoch {
                // Two distinct roots stay distinct until one is absorbed;
                // find_const on a still-live root is a single parent read.
                self.diseq_roots[i]
            } else {
                (self.node(t1), self.node(t2))
            };
            let nr1 = self.eg.find_const(r1);
            let nr2 = self.eg.find_const(r2);
            if nr1 == nr2 {
                self.reported_diseqs.insert(i);
                // Latch a coincident true=false merge even though the ordinary
                // disequality is the conflict returned here.
                self.reported_tf = self.reported_tf || tf_pair.is_some();
                let equalities = self.explain_conflict(t1, t2);
                if explain_audit() {
                    self.audit_explanation(t1, t2, &equalities);
                }
                return Some(Conflict {
                    equalities,
                    disequality: (t1, t2),
                    diseq_lit: Some(lit),
                });
            }
            self.diseq_roots[i] = (nr1, nr2);
            self.diseq_epoch[i] = self.epoch;
        }
        if let Some((t, f)) = tf_pair
            && !self.reported_tf
        {
            self.reported_tf = true;
            let eqs = if explain_legacy() {
                self.explain_true_false(t, f)
            } else {
                let mut eqs = self.explain_conflict(t, f);
                let tf = [t, f];
                eqs.retain(|&(a, b)| !tf.contains(&a) || !tf.contains(&b));
                eqs
            };
            if explain_audit() {
                EXPLAIN_TF_AUDITED.fetch_add(1, Ordering::Relaxed);
                if !self.explanation_entails(&eqs, t, f) {
                    EXPLAIN_TF_INVALID.fetch_add(1, Ordering::Relaxed);
                    if !self.valid_modulo_level0(&eqs, t, f) {
                        EXPLAIN_TF_UNSOUND.fetch_add(1, Ordering::Relaxed);
                        self.dump_invalid("true=false NOT valid modulo level 0", &eqs, t, f);
                    }
                }
            }
            return Some(Conflict {
                equalities: eqs,
                disequality: (t, f),
                diseq_lit: None,
            });
        }
        None
    }

    fn result_after_merge(&mut self) -> EgraphResult<u32> {
        match self.violated_diseq() {
            Some(c) => EgraphResult::with_conflict(c),
            None => EgraphResult::ok(),
        }
    }

    /// Extend the (op, arity) -> terms index over registrations made since
    /// the last call. Driver ids and `reg_log` children never change, so
    /// extension is the only maintenance the index ever needs.
    fn ensure_fn_index(&mut self) {
        for i in self.fn_index_upto..self.reg_log.len() {
            if let RegEvent::Term { sym, children } = &self.reg_log[i] {
                let key = (*sym, u32::try_from(children.len()).expect("arity fits u32"));
                self.fn_index
                    .entry(key)
                    .or_default()
                    .push(u32::try_from(i).expect("driver id fits u32"));
            }
        }
        self.fn_index_upto = self.reg_log.len();
    }

    /// Shield a node that the last intern created (relevancy registers every
    /// node unmatchable until relevancy reaches it). A registration that
    /// interned into an existing node leaves that node's state alone.
    fn rel_shield_if_fresh(&mut self, node: ENodeId, nodes_before: usize) {
        if self.relevancy_enabled && node.to_usize() >= nodes_before {
            self.eg.set_node_matchable(node, false);
        }
    }

    fn reg_children(&self, term: u32) -> &[u32] {
        match &self.reg_log[term as usize] {
            RegEvent::Term { children, .. } => children,
            RegEvent::Opaque => &[],
        }
    }

    // --- Relevancy (SEMPER_RELEVANCY=1) ----------------------------------
    //
    // Z3's relevancy (`smt_relevancy.cpp`), kept in the engine. Every node is
    // registered shielded from e-matching (`FLAG_UNMATCHABLE`) and un-shielded
    // when relevancy reaches it, so the native matcher's index never sees an
    // irrelevant node and the top-down matcher skips it at candidate time:
    // no match is produced and then discarded. The flag lives in the
    // semi-persistent node stores, so a mark made at a decision level is
    // undone by the restore of that level, as Z3 undoes its marks on
    // backtrack. Rules, applied when a term is marked and re-applied to every
    // relevant gate at the start of each eager matching round:
    //   and = true, or = false, implies = false: every child;
    //   and = false / or = true: one witness, none if a witness is already
    //     relevant (Z3's choice), else the first in child order;
    //   implies = true: a if a is false, else b if b is true;
    //   ite: both branches in one class -> the branches, not the condition
    //     (the DAG rule; Z3 always marks the condition); otherwise the
    //     condition and the taken branch;
    //   any other application or equality: every argument;
    //   quantifiers are opaque nodes: relevancy stops at them.
    // Closure (Z3's `mark_as_relevant` walks the enode class, `add_eq` carries
    // relevancy across a merge): marking a term marks every member of its
    // class, and a merge in which one side is relevant marks the merged class,
    // except the true and false classes, which every assigned atom joins in
    // this adapter (Z3 merges an atom into them only for `merge_tf` enodes).
    // `SEMPER_REL_NOCLASS=1` turns the closure off, for measurement.
    // Seeds: the level-0 asserted atoms, and every quantifier instance body
    // once it is true (Z3 asserts `(or (not q) body)` as a root clause with
    // relevancy watches). The whole set is never recomputed: a round costs the
    // merges since the last round, the seeds, and the relevant gates.

    /// Whether `t`'s node is relevant (un-shielded). Always true while
    /// relevancy is off.
    fn rel_is_marked(&self, t: u32) -> bool {
        !self.relevancy_enabled || self.eg.is_node_matchable(self.node(t))
    }

    /// Whether `node`'s class is the true or the false class.
    fn rel_is_truth_class(&self, node: ENodeId) -> bool {
        let r = self.eg.find_const(node);
        self.true_term
            .is_some_and(|t| self.eg.find_const(self.node(t)) == r)
            || self
                .false_term
                .is_some_and(|t| self.eg.find_const(self.node(t)) == r)
    }

    /// Mark `t` relevant (and, under the closure, its whole class), queueing
    /// every newly marked term for rule application.
    fn rel_mark(&mut self, t: u32) {
        if !self.relevancy_enabled {
            return;
        }
        let n = self.node(t);
        if self.eg.is_node_matchable(n) {
            return;
        }
        self.ensure_scope();
        self.eg.set_node_matchable(n, true);
        self.rel_epoch += 1;
        REL_MARKS.fetch_add(1, Ordering::Relaxed);
        if incr_match() {
            self.incr_newly_relevant.push(t);
        }
        self.rel_queue.push(t);
        if !rel_noclass() && !self.rel_is_truth_class(n) {
            self.rel_mark_class(n);
        }
    }

    /// Un-shield every still-shielded member of `node`'s class and queue
    /// their drivers (the closure step).
    fn rel_mark_class(&mut self, node: ENodeId) {
        let members: Vec<ENodeId> = self
            .eg
            .class_members(node)
            .filter(|&m| !self.eg.is_node_matchable(m))
            .collect();
        if members.is_empty() {
            return;
        }
        self.ensure_scope();
        for m in members {
            self.eg.set_node_matchable(m, true);
            self.rel_epoch += 1;
            REL_MARKS.fetch_add(1, Ordering::Relaxed);
            if let Some(&d) = self.node_to_driver.get(m.to_usize())
                && d != NO_DRIVER
            {
                if incr_match() {
                    self.incr_newly_relevant.push(d);
                }
                self.rel_queue.push(d);
            }
        }
    }

    /// Apply the rule of the (relevant) term `t`: mark the children it makes
    /// relevant on the current assignment.
    fn rel_apply(&mut self, t: u32) {
        let (kind, children) = match &self.reg_log[t as usize] {
            RegEvent::Term { sym, children } => {
                (self.sym_info[*sym as usize].kind, children.clone())
            }
            RegEvent::Opaque => return,
        };
        let tr = self.true_term.map(|x| self.eg.find_const(self.node(x)));
        let fr = self.false_term.map(|x| self.eg.find_const(self.node(x)));
        let val = |s: &Self, c: u32| s.bool_value(c, tr, fr);
        match kind {
            SymKind::And | SymKind::Or => {
                let is_gate_kind = |k| k == SymKind::And || k == SymKind::Or;
                debug_assert!(is_gate_kind(kind));
                match val(self, t) {
                    None => {}
                    Some(v) => {
                        // and=true / or=false: every child; and=false /
                        // or=true: one witness with value `v`.
                        let all = (kind == SymKind::And) == v;
                        if all {
                            for c in children {
                                self.rel_mark(c);
                            }
                        } else if !children
                            .iter()
                            .any(|&c| val(self, c) == Some(v) && self.rel_is_marked(c))
                            && let Some(&w) = children.iter().find(|&&c| val(self, c) == Some(v))
                        {
                            self.rel_mark(w);
                        }
                    }
                }
            }
            SymKind::Implies if children.len() == 2 => match val(self, t) {
                Some(false) => {
                    self.rel_mark(children[0]);
                    self.rel_mark(children[1]);
                }
                Some(true) => {
                    if val(self, children[0]) == Some(false) {
                        self.rel_mark(children[0]);
                    } else if val(self, children[1]) == Some(true) {
                        self.rel_mark(children[1]);
                    }
                }
                None => {}
            },
            SymKind::Ite if children.len() == 3 => {
                if self.find(children[1]) == self.find(children[2]) {
                    REL_ITE_EQ_FIRED.fetch_add(1, Ordering::Relaxed);
                    self.rel_mark(children[1]);
                    self.rel_mark(children[2]);
                } else {
                    self.rel_mark(children[0]);
                    match val(self, children[0]) {
                        Some(true) => self.rel_mark(children[1]),
                        Some(false) => self.rel_mark(children[2]),
                        None => {}
                    }
                }
            }
            _ => {
                for c in children {
                    self.rel_mark(c);
                }
            }
        }
    }

    /// Drain the mark queue, applying each newly marked term's rule; gates
    /// are remembered for the per-round re-check.
    fn rel_propagate(&mut self) {
        while let Some(t) = self.rel_queue.pop() {
            if let RegEvent::Term { sym, .. } = &self.reg_log[t as usize]
                && matches!(
                    self.sym_info[*sym as usize].kind,
                    SymKind::And | SymKind::Or | SymKind::Implies | SymKind::Ite
                )
            {
                self.rel_gates.push(t);
            }
            self.rel_apply(t);
        }
    }

    /// Carry relevancy across the merges logged since the last call (Z3's
    /// `add_eq`: when one side of a merge is relevant, the merged class is).
    /// Reads the engine's merge log with a cursor; the arithmetic export
    /// drains the log, so it calls this first.
    fn rel_absorb_merges(&mut self) {
        if !self.relevancy_enabled {
            return;
        }
        let log_len = self.eg.merged_log().len();
        if self.rel_merge_cursor > log_len {
            self.rel_merge_cursor = 0; // the log was drained or cleared
        }
        if !rel_noclass() {
            let merges: Vec<(ENodeId, ENodeId)> =
                self.eg.merged_log()[self.rel_merge_cursor..].to_vec();
            for (s, a) in merges {
                if (self.eg.is_node_matchable(s) || self.eg.is_node_matchable(a))
                    && !self.rel_is_truth_class(s)
                {
                    self.rel_mark_class(s);
                }
            }
        }
        self.rel_merge_cursor = log_len;
    }

    /// Bring the relevant set up to date with the current assignment: carry
    /// relevancy across the merges since the last refresh, seed the roots and
    /// the true instance bodies, re-apply every relevant gate's rule (a gate
    /// may have been assigned, or may have gained a witness, since it was
    /// marked), and propagate. Called at the start of each eager round.
    fn rel_refresh(&mut self) {
        if !self.relevancy_enabled {
            return;
        }
        REL_REFRESHES.fetch_add(1, Ordering::Relaxed);
        self.rel_absorb_merges();
        if !self.incremental_arith {
            // Nobody else drains the log: drop what was read.
            let _ = self.eg.take_merged_log();
            self.rel_merge_cursor = 0;
        }
        let roots = self.root_terms.clone();
        for t in roots {
            self.rel_mark(t);
        }
        if rel_seed_instances() {
            let tr = self.true_term.map(|x| self.eg.find_const(self.node(x)));
            let fr = self.false_term.map(|x| self.eg.find_const(self.node(x)));
            let inst = self.instance_roots.clone();
            for t in inst {
                if (t as usize) < self.terms.len() && self.bool_value(t, tr, fr) == Some(true) {
                    self.rel_mark(t);
                }
            }
        }
        self.rel_propagate();
        if rel_gate_rescan() {
            let before = REL_MARKS.load(Ordering::Relaxed);
            let gates = self.rel_gates.clone();
            for g in gates {
                self.rel_apply(g);
            }
            self.rel_propagate();
            REL_RESCAN_MARKS.fetch_add(
                REL_MARKS.load(Ordering::Relaxed) - before,
                Ordering::Relaxed,
            );
        }
        if rel_measure() {
            self.rel_sample();
        }
        if let Some(path) = std::env::var_os("SEMPER_REL_DUMP") {
            self.rel_dump(&path);
        }
    }

    /// Diagnostic (`SEMPER_REL_DUMP=<file>`): append the state of one
    /// filtered round to `<file>`: the definitions of terms registered since
    /// the last dump (`T id symbol child..`, `T id OPAQUE`), then the round's
    /// seeds, relevant terms, Boolean values and class representatives, so a
    /// blocked instance can be explained offline (`scripts/rel_explain.py`).
    fn rel_dump(&self, path: &std::ffi::OsStr) {
        use std::io::Write;
        let Ok(mut f) = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(path)
        else {
            return;
        };
        let start = REL_DUMPED_TERMS.load(Ordering::Relaxed);
        let n = self.terms.len();
        let mut out = String::new();
        for i in start..n {
            match &self.reg_log[i] {
                RegEvent::Term { sym, children } => {
                    out.push_str(&format!("T {i} {}", self.sym_info[*sym as usize].base));
                    for c in children {
                        out.push_str(&format!(" {c}"));
                    }
                    out.push('\n');
                }
                RegEvent::Opaque => out.push_str(&format!("T {i} OPAQUE\n")),
            }
        }
        REL_DUMPED_TERMS.store(n, Ordering::Relaxed);
        let round = REL_DUMP_ROUND.fetch_add(1, Ordering::Relaxed) + 1;
        let tr = self.true_term.map(|x| self.eg.find_const(self.node(x)));
        let fr = self.false_term.map(|x| self.eg.find_const(self.node(x)));
        let join = |v: &mut dyn Iterator<Item = u32>| {
            v.map(|x| x.to_string()).collect::<Vec<_>>().join(" ")
        };
        out.push_str(&format!("ROUND {round} terms={n} level={}\n", self.level));
        out.push_str(&format!(
            "ROOTS {}\n",
            join(&mut self.root_terms.iter().copied())
        ));
        out.push_str(&format!(
            "IROOTS {}\n",
            join(&mut self.instance_roots.iter().copied())
        ));
        out.push_str(&format!(
            "REL {}\n",
            join(&mut (0..n as u32).filter(|&i| self.eg.is_node_matchable(self.terms[i as usize])))
        ));
        out.push_str(&format!(
            "TRUE {}\n",
            join(&mut (0..n as u32).filter(|&i| self.bool_value(i, tr, fr) == Some(true)))
        ));
        out.push_str(&format!(
            "FALSE {}\n",
            join(&mut (0..n as u32).filter(|&i| self.bool_value(i, tr, fr) == Some(false)))
        ));
        out.push_str(&format!(
            "CLASS {}\n",
            join(&mut (0..n as u32).map(|i| self.find(i)))
        ));
        let _ = f.write_all(out.as_bytes());
    }

    /// Relevant / total over all registered terms and over the Boolean ones
    /// (connectives, equalities, connective children, assigned atoms), for
    /// the `SEMPER_REL_RATIO` report. Measurement only: O(terms).
    fn rel_sample(&self) {
        let tr = self.true_term.map(|x| self.eg.find_const(self.node(x)));
        let fr = self.false_term.map(|x| self.eg.find_const(self.node(x)));
        let n = self.terms.len();
        let mut is_bool = vec![false; n];
        for (i, ev) in self.reg_log.iter().enumerate().take(n) {
            let RegEvent::Term { sym, children } = ev else {
                continue;
            };
            let kind = self.sym_info[*sym as usize].kind;
            match kind {
                SymKind::And | SymKind::Or | SymKind::Not | SymKind::Implies | SymKind::Eq => {
                    is_bool[i] = true;
                    if kind != SymKind::Eq {
                        for &c in children {
                            is_bool[c as usize] = true;
                        }
                    }
                }
                SymKind::Ite => {
                    if let Some(&c) = children.first() {
                        is_bool[c as usize] = true;
                    }
                }
                SymKind::Other => {}
            }
            if self.bool_value(i as u32, tr, fr).is_some() {
                is_bool[i] = true;
            }
        }
        let (mut rel, mut rel_bool, mut tot_bool) = (0u32, 0u32, 0u32);
        for i in 0..n {
            let m = self.eg.is_node_matchable(self.terms[i]);
            if m {
                rel += 1;
            }
            if is_bool[i] {
                tot_bool += 1;
                if m {
                    rel_bool += 1;
                }
            }
        }
        REL_SAMPLES
            .lock()
            .expect("rel samples")
            .push([rel, n as u32, rel_bool, tot_bool]);
    }

    /// Link an arithmetic driver to the first arithmetic driver of its node
    /// (see `intern_by_node`): the pair is reported by the next
    /// `drain_arithmetic_equalities`, once per pair.
    fn link_intern_driver(&mut self, term: u32) {
        // SEMPER_NO_INTERN_EQ=1 reproduces the pre-fix behaviour (no link),
        // for measuring the fix against the runs recorded before it.
        if intern_eq_disabled() {
            return;
        }
        let node = self.terms[term as usize];
        match self.intern_by_node.entry(node) {
            std::collections::hash_map::Entry::Vacant(e) => {
                e.insert(term);
            }
            std::collections::hash_map::Entry::Occupied(e) => {
                let first = *e.get();
                if first != term && self.intern_eqs_emitted.insert((first, term)) {
                    self.intern_eqs_pending.push((first, term));
                    self.intern_eqs_trail.push((first, term));
                }
            }
        }
    }

    /// Mark the run's refutation untrustworthy (see `refutation_tainted`): the
    /// SAT core may still derive unsat, but `cdcl.rs` reports it as unknown.
    /// SEMPER_TAINT_TRACE=1 reports the first taint so a verdict downgraded to
    /// unknown can be traced to the intern-time conflation the adapter could
    /// not explain (`align_to_creator` aligns `reg_children` positionally, which
    /// fits the commutative `=` pair but not an AC set conflation).
    fn taint(&mut self) {
        if !self.tf_taint && std::env::var_os("SEMPER_TAINT_TRACE").is_some() {
            eprintln!(
                "SEMPER_TAINT: intern-time conflation could not be explained; \
                 an unsat refutation will be reported as unknown"
            );
        }
        self.tf_taint = true;
    }

    /// Whether `cand` is shielded from matching in this round: relevancy is
    /// filtering and relevancy has not reached `cand`'s node. The top-down
    /// matcher skips such a candidate, as the native index skips its node.
    fn rel_shielded(&self, cand: u32) -> bool {
        self.rel_filtering() && !self.eg.is_node_matchable(self.node(cand))
    }

    /// Whether relevancy decides matching in the current round.
    fn rel_filtering(&self) -> bool {
        self.relevancy_enabled && self.relevancy_active && !rel_nofilter()
    }

    // --- Relevancy-restricted branching (phase-aware) ---------------------
    //
    // A structural relevant-first decision policy (Z3 CASE_SPLIT=3). It
    // descends the Boolean structure from the level-0 assertions carrying a
    // *desired polarity* `want` (the assertions want to be true), and returns
    // the first unassigned atom to branch on together with the phase that
    // pushes its relevant, not-yet-satisfied ancestor gate toward
    // satisfaction. Polarity is threaded explicitly and flipped at `not`
    // (`want` -> `!want`), which is the negation bookkeeping NNF would make
    // implicit; because the driver already NNF-normalizes before Tseitin,
    // negations sit at the leaves, so the flip is cheap. For `and`/`or` the
    // children inherit the parent's `want` unchanged (the monotonicity of the
    // NNF structure): and/or-true both want true children, and/or-false both
    // want false children. Assigned nodes are read off the merge state and
    // pruned, so already-justified structure is skipped and only live
    // don't-care-free decisions are produced.

    /// Seed a relevancy root from an `assert_equal`/`assert_disequal` whose
    /// shape is "Boolean atom asserted to a truth value": exactly when one
    /// endpoint is the true or false constant, the other endpoint is the
    /// asserted atom and becomes a root. Plain term equalities seed nothing.
    fn seed_root_if_boolean(&mut self, t1: u32, t2: u32) {
        let is_tf = |t: u32| Some(t) == self.true_term || Some(t) == self.false_term;
        let root = if is_tf(t2) && !is_tf(t1) {
            t1
        } else if is_tf(t1) && !is_tf(t2) {
            t2
        } else {
            return;
        };
        self.root_terms.push(root);
        // Z3 marks an assertion relevant when it is asserted
        // (`internalize_assertion` -> `mark_as_relevant`), before any
        // propagation. Marking only at the first round's refresh came after
        // level 0 had assigned every fuel guard, so each guard's `or` saw
        // both children true and took the first in stored order: 0 round-1
        // instances on rabbitmq role.7 against 248 with relevancy off.
        if self.relevancy_enabled && rel_incremental() {
            self.rel_mark(root);
            self.rel_propagate();
        }
    }

    fn bool_value(&self, t: u32, tr: Option<ENodeId>, fr: Option<ENodeId>) -> Option<bool> {
        let r = self.eg.find_const(self.node(t));
        if Some(r) == tr {
            Some(true)
        } else if Some(r) == fr {
            Some(false)
        } else {
            None
        }
    }

    fn suggest_rec(
        &self,
        t: u32,
        want: bool,
        tr: Option<ENodeId>,
        fr: Option<ENodeId>,
        visited: &mut rustc_hash::FxHashSet<(u32, bool)>,
    ) -> Option<(u32, bool)> {
        if !visited.insert((t, want)) {
            return None;
        }
        // Bail only when the node is already assigned OPPOSITE to what we want:
        // that branch is decided against us, nothing here helps. A node assigned
        // TOWARD `want` is not a dead end — an assigned-true `and` still has
        // unassigned children that must become true, and those are the relevant
        // decisions. So we do not return here on a matching assignment; each
        // gate below decides whether descending is still productive.
        let val = self.bool_value(t, tr, fr);
        if val == Some(!want) {
            return None;
        }
        let is_true = |c: u32| self.bool_value(c, tr, fr) == Some(true);
        let is_false = |c: u32| self.bool_value(c, tr, fr) == Some(false);
        let (kind, children) = match &self.reg_log[t as usize] {
            RegEvent::Term { sym, children } => {
                (self.sym_info[*sym as usize].kind, children.clone())
            }
            RegEvent::Opaque => return None,
        };
        match kind {
            SymKind::And => {
                if want {
                    // Every child must be true: descend all, deciding the
                    // unassigned ones true.
                    children
                        .iter()
                        .find_map(|&c| self.suggest_rec(c, true, tr, fr, visited))
                } else {
                    // One false child suffices: if one is already false the
                    // gate is justified (the rest are don't-cares); else decide
                    // the first undetermined child false.
                    if children.iter().any(|&c| is_false(c)) {
                        None
                    } else {
                        children
                            .iter()
                            .find_map(|&c| self.suggest_rec(c, false, tr, fr, visited))
                    }
                }
            }
            SymKind::Or => {
                if want {
                    // One true child suffices: already-true child justifies the
                    // gate and masks the rest (relevancy); else decide one true.
                    if children.iter().any(|&c| is_true(c)) {
                        None
                    } else {
                        children
                            .iter()
                            .find_map(|&c| self.suggest_rec(c, true, tr, fr, visited))
                    }
                } else {
                    // Every child must be false.
                    children
                        .iter()
                        .find_map(|&c| self.suggest_rec(c, false, tr, fr, visited))
                }
            }
            // Negation flips the desired polarity.
            SymKind::Not => children
                .first()
                .and_then(|&c| self.suggest_rec(c, !want, tr, fr, visited)),
            // (=> a b) = (or (not a) b).
            SymKind::Implies if children.len() == 2 => {
                let (a, b) = (children[0], children[1]);
                if want {
                    if is_false(a) || is_true(b) {
                        None
                    } else {
                        self.suggest_rec(a, false, tr, fr, visited)
                            .or_else(|| self.suggest_rec(b, true, tr, fr, visited))
                    }
                } else {
                    self.suggest_rec(a, true, tr, fr, visited)
                        .or_else(|| self.suggest_rec(b, false, tr, fr, visited))
                }
            }
            // ite(c, th, el): decide the condition first if open, else descend
            // the taken branch. The condition's phase is a free choice.
            SymKind::Ite if children.len() == 3 => match self.bool_value(children[0], tr, fr) {
                None => self.suggest_rec(children[0], true, tr, fr, visited),
                Some(true) => self.suggest_rec(children[1], want, tr, fr, visited),
                Some(false) => self.suggest_rec(children[2], want, tr, fr, visited),
            },
            // Leaf atom (Eq / App / Distinct / Constant). Decide it only if it
            // is unassigned; an atom already assigned toward `want` needs no
            // decision.
            _ => {
                if val.is_none() {
                    Some((t, want))
                } else {
                    None
                }
            }
        }
    }

    // --- E-matching -------------------------------------------------------
    //
    // A faithful port of the basic backend's top-down matcher, over the
    // registration log instead of its function_maps: same binding
    // discipline (variables bind raw ids, consistency compared by class),
    // same congruence dedup (candidates with canonically equal subterm
    // vectors are matched once), same multi-trigger semantics (one
    // substitution threaded through all trigger patterns). Bridging to the
    // engine's compiled leapfrog matcher is the planned upgrade; this port
    // establishes behavioral parity first so that swap is measurable.

    /// Start of a matching round, incremental matching (semi-naive, as
    /// Z3's `mam::add_eq_eh`): the matches a full scan would find now and
    /// the previous round could not have found each involve a term created
    /// since, or a class merge since, used at a step of the pattern. So the
    /// round's root candidates are the class-aware ancestors, up to the
    /// deepest pattern, of: every new term; every parent of a member of the
    /// renamed side of a merge, at a position whose pattern label is an
    /// operator of the other side or a variable; and every parent of a
    /// member of the other side at a position whose label is an operator of
    /// the renamed side. Ancestors go through every member of a class and
    /// keep only operators that occur in patterns, which leaves the
    /// true/false classes (every assigned atom joins one) out: their parents
    /// are gates, which patterns never contain. Cost: one pass over the
    /// terms plus the parents of the renamed sides.
    fn incr_begin_round(&mut self) {
        let n = self.terms.len();
        let old_n = self.incr_snapshot.len();
        let mut rep = Vec::with_capacity(n);
        for t in 0..n {
            rep.push(self.find(t as u32));
        }
        let mut members: rustc_hash::FxHashMap<u32, Vec<u32>> = rustc_hash::FxHashMap::default();
        for t in 0..n {
            members.entry(rep[t]).or_default().push(t as u32);
        }
        let mut renamed: rustc_hash::FxHashMap<u32, Vec<u32>> = rustc_hash::FxHashMap::default();
        for t in 0..old_n {
            if self.incr_snapshot[t] != rep[t] {
                renamed.entry(rep[t]).or_default().push(t as u32);
            }
        }
        // Pattern labels resolved to symbols for this round.
        let pc: rustc_hash::FxHashSet<(SymId, u32, SymId)> = self
            .pc_pairs
            .iter()
            .filter_map(|(f, i, g)| Some((self.sym_lookup(f)?, *i, self.sym_lookup(g)?)))
            .collect();
        let pcv: rustc_hash::FxHashSet<(SymId, u32)> = self
            .pc_var
            .iter()
            .filter_map(|(f, i)| Some((self.sym_lookup(f)?, *i)))
            .collect();
        let pcg: rustc_hash::FxHashSet<(SymId, u32)> = self
            .pc_ground
            .iter()
            .filter_map(|(f, i)| Some((self.sym_lookup(f)?, *i)))
            .collect();
        let pops: rustc_hash::FxHashSet<SymId> = self
            .pattern_ops
            .iter()
            .filter_map(|f| self.sym_lookup(f))
            .collect();
        let op_of = |s: &Self, t: u32| match &s.reg_log[t as usize] {
            RegEvent::Term { sym, .. } => Some(*sym),
            RegEvent::Opaque => None,
        };
        let mut seeds: Vec<u32> = (old_n as u32..n as u32).collect();
        // Marked relevant since the previous round (the shield no longer
        // hides them); a mark undone by a backtrack and redone is listed
        // again.
        let newly = std::mem::take(&mut self.incr_newly_relevant);
        seeds.extend(newly.into_iter().filter(|&t| (t as usize) < n));
        // Parents of `m` at a position whose label admits an operator of
        // `other_ops`, is a ground term (matched by class), or, when `vars`,
        // is a variable (a repeated variable's consistency check is by class).
        let seed_parents = |s: &Self,
                            m: u32,
                            other_ops: &rustc_hash::FxHashSet<SymId>,
                            vars: bool,
                            out: &mut Vec<u32>| {
            let Some(ps) = s.parents.get(m as usize) else {
                return;
            };
            for &p in ps {
                let Some(f) = op_of(s, p) else { continue };
                if !pops.contains(&f) {
                    continue;
                }
                let hit = s.reg_children(p).iter().enumerate().any(|(i, &c)| {
                    c == m
                        && ((vars && pcv.contains(&(f, i as u32)))
                            || pcg.contains(&(f, i as u32))
                            || other_ops.iter().any(|&g| pc.contains(&(f, i as u32, g))))
                });
                if hit {
                    out.push(p);
                }
            }
        };
        // Merged classes: every member of a class with a renamed member seeds
        // its parents against the operators of the members that had a
        // different representative in the previous round (new terms count as
        // their own class). Not "renamed against not renamed": when two
        // classes merge into a third whose root keeps its id, every member of
        // both sides is renamed and nothing is "other", and the match between
        // one side's parent and the other side's member is missed (found on
        // the basic port: quantifier_backtrack13 under eager rounds;
        // same code here).
        let old_rep = |s: &Self, t: u32| -> u32 {
            if (t as usize) < old_n {
                s.incr_snapshot[t as usize]
            } else {
                u32::MAX - t
            }
        };
        for (&z, _r) in &renamed {
            let all = &members[&z];
            // Members grouped by previous-round class, one operator set per
            // group (per member it was O(class size squared) per round; on
            // the true class that was 90% of an eager round on the basic
            // port).
            let mut groups: rustc_hash::FxHashMap<u32, Vec<u32>> = rustc_hash::FxHashMap::default();
            for &m in all {
                groups.entry(old_rep(self, m)).or_default().push(m);
            }
            let group_ops: Vec<(u32, rustc_hash::FxHashSet<SymId>)> = groups
                .iter()
                .map(|(&o, ms)| (o, ms.iter().filter_map(|&t| op_of(self, t)).collect()))
                .collect();
            for (o, ms) in &groups {
                let mut other_ops: rustc_hash::FxHashSet<SymId> = rustc_hash::FxHashSet::default();
                for (o2, ops) in &group_ops {
                    if o2 != o {
                        other_ops.extend(ops.iter().copied());
                    }
                }
                if other_ops.is_empty() && pcg.is_empty() {
                    continue;
                }
                for &m in ms {
                    seed_parents(self, m, &other_ops, true, &mut seeds);
                }
            }
        }
        // Splits: a backtrack can divide a class of the previous round into
        // parts. In the merged class the congruence dedup matched one
        // representative per canonical child vector, so the instances of the
        // other parts' candidates were never produced and are new to the
        // solver's term-level dedup once the parts are apart. Every member of
        // a split class seeds its parents, against the other parts' operators.
        let mut by_old: rustc_hash::FxHashMap<u32, Vec<u32>> = rustc_hash::FxHashMap::default();
        for t in 0..old_n {
            by_old
                .entry(self.incr_snapshot[t])
                .or_default()
                .push(t as u32);
        }
        for (_, group) in by_old {
            let mut parts: rustc_hash::FxHashMap<u32, Vec<u32>> = rustc_hash::FxHashMap::default();
            for &t in &group {
                parts.entry(rep[t as usize]).or_default().push(t);
            }
            if parts.len() < 2 {
                continue;
            }
            let all_ops: Vec<(u32, rustc_hash::FxHashSet<SymId>)> = parts
                .iter()
                .map(|(&z, ms)| (z, ms.iter().filter_map(|&t| op_of(self, t)).collect()))
                .collect();
            for (z, ms) in &parts {
                let mut other_ops: rustc_hash::FxHashSet<SymId> = rustc_hash::FxHashSet::default();
                for (z2, ops) in &all_ops {
                    if z2 != z {
                        other_ops.extend(ops.iter().copied());
                    }
                }
                for &m in ms {
                    seed_parents(self, m, &other_ops, true, &mut seeds);
                }
            }
        }
        // Class-aware ancestors, by level.
        let mut level_of: rustc_hash::FxHashMap<u32, u32> = rustc_hash::FxHashMap::default();
        let mut frontier: Vec<u32> = Vec::new();
        for t in seeds {
            if level_of.insert(t, 0).is_none() {
                frontier.push(t);
            }
        }
        let mut expanded: rustc_hash::FxHashSet<u32> = rustc_hash::FxHashSet::default();
        for k in 1..=self.incr_max_depth {
            let mut next = Vec::new();
            for &u in &frontier {
                let name = rep[u as usize];
                if !expanded.insert(name) {
                    continue;
                }
                for &m in &members[&name] {
                    let Some(ps) = self.parents.get(m as usize) else {
                        continue;
                    };
                    for &p in ps {
                        if op_of(self, p).is_some_and(|f| pops.contains(&f))
                            && !level_of.contains_key(&p)
                        {
                            level_of.insert(p, k);
                            next.push(p);
                        }
                    }
                }
            }
            frontier = next;
        }
        self.incr_cands.clear();
        for (&t, &lvl) in &level_of {
            if let RegEvent::Term { sym, children } = &self.reg_log[t as usize] {
                let key = (*sym, u32::try_from(children.len()).expect("arity fits u32"));
                self.incr_cands.entry(key).or_default().push((t, lvl));
            }
        }
        for v in self.incr_cands.values_mut() {
            v.sort_unstable();
        }
        self.incr_snapshot = rep;
        self.incr_active = true;
        self.incr_round += 1;
    }

    /// Diff mode: the full scan's matches that the filtered scan did not
    /// produce and that no earlier round produced either (earlier matches
    /// are kept with raw bindings and canonicalized against the current
    /// classes, so a merge since does not make an old match look new).
    fn incr_diff(
        &mut self,
        pattern: PatternId,
        filtered: &[crate::utils::DeterministicHashMap<Local, u32>],
    ) {
        let mut a = crate::utils::DeterministicHashMap::default();
        let full = self.match_pairs(&mut a, &[(pattern, None)], false);
        let canon = |m: &crate::utils::DeterministicHashMap<Local, u32>| {
            let mut kv: Vec<(Local, u32)> =
                m.iter().map(|(l, &d)| (l.clone(), self.find(d))).collect();
            kv.sort();
            kv
        };
        let fk: rustc_hash::FxHashSet<Vec<(Local, u32)>> = filtered.iter().map(canon).collect();
        let seen: rustc_hash::FxHashSet<Vec<(Local, u32)>> = self
            .incr_seen
            .get(&pattern)
            .map(|v| v.iter().map(canon).collect())
            .unwrap_or_default();
        let missed_raw: Vec<&crate::utils::DeterministicHashMap<Local, u32>> = full
            .iter()
            .filter(|m| {
                let k = canon(m);
                !fk.contains(&k) && !seen.contains(&k)
            })
            .collect();
        let missed = missed_raw.len();
        if missed > 0 {
            INCR_DIFF_CALLS.fetch_add(1, Ordering::Relaxed);
            INCR_DIFF_MISSED.fetch_add(missed as u64, Ordering::Relaxed);
            eprintln!(
                "INCR_DIFF round={} pattern={pattern} {:?} full={} filtered={} missed_new={missed}",
                self.incr_round,
                self.patterns[pattern],
                full.len(),
                filtered.len()
            );
            for m in missed_raw.iter().take(3) {
                let b: Vec<String> = m
                    .iter()
                    .map(|(l, &d)| {
                        format!(
                            "{}->{} (class {})",
                            l.symbol,
                            self.fmt_term(d, 3),
                            self.find(d)
                        )
                    })
                    .collect();
                eprintln!("INCR_DIFF   missed [{}]", b.join("; "));
            }
        }
        self.incr_seen.entry(pattern).or_default().extend(full);
    }

    /// `filter`: apply the incremental candidate filter to the first pair
    /// (the round's rooted pattern); the remaining pairs join unfiltered.
    fn match_pairs(
        &self,
        assignment: &mut crate::utils::DeterministicHashMap<Local, u32>,
        pairs: &[(PatternId, Option<u32>)],
        filter: bool,
    ) -> Vec<crate::utils::DeterministicHashMap<Local, u32>> {
        let Some(&(pattern_id, hint)) = pairs.first() else {
            return vec![assignment.clone()];
        };
        // Borrowed, not cloned: `match_top` takes `&self`, so the pattern
        // borrow coexists with it. Cloning here deep-copied the whole pattern
        // tree, strings included, once per matched pair.
        self.match_top(
            assignment,
            &self.patterns[pattern_id],
            hint,
            &pairs[1..],
            filter,
        )
    }

    fn match_top(
        &self,
        assignment: &mut crate::utils::DeterministicHashMap<Local, u32>,
        pattern: &Pattern<u32>,
        hint: Option<u32>,
        remaining: &[(PatternId, Option<u32>)],
        filter: bool,
    ) -> Vec<crate::utils::DeterministicHashMap<Local, u32>> {
        match pattern {
            Pattern::Var(name) => {
                let ground = hint.expect("Pattern::Var requires a ground term to bind");
                match assignment.get(name) {
                    None => {
                        assignment.insert(name.clone(), ground);
                        self.match_pairs(assignment, remaining, false)
                    }
                    Some(&v) if self.find(v) == self.find(ground) => {
                        self.match_pairs(assignment, remaining, false)
                    }
                    Some(_) => vec![],
                }
            }
            Pattern::Ground(id) => match hint {
                Some(ground) if self.find(*id) == self.find(ground) => {
                    self.match_pairs(assignment, remaining, false)
                }
                None => self.match_pairs(assignment, remaining, false),
                _ => vec![],
            },
            Pattern::App(op, subs) => {
                // A pattern symbol the adapter never interned indexes no
                // terms, so an absent `SymId` means no candidates.
                let Some(sym) = self.sym_lookup(op) else {
                    return vec![];
                };
                let arity = u32::try_from(subs.len()).expect("arity fits u32");
                // Incremental: only the round's candidates for this operator,
                // at or below the pattern's depth; otherwise every term.
                let depth = pattern_depth(pattern);
                let candidates: Vec<u32> = if filter {
                    let all = self.fn_index.get(&(sym, arity)).map_or(0, |c| c.len());
                    let mut cs: Vec<u32> = self
                        .incr_cands
                        .get(&(sym, arity))
                        .map(|v| {
                            v.iter()
                                .filter(|&&(_, l)| l <= depth)
                                .map(|&(t, _)| t)
                                .collect()
                        })
                        .unwrap_or_default();
                    // Terms registered since the round's snapshot (by the
                    // round's own conversions and axioms) are candidates too;
                    // `fn_index` lists are in registration order.
                    let since = self.incr_snapshot.len() as u32;
                    if let Some(list) = self.fn_index.get(&(sym, arity)) {
                        let start = list.partition_point(|&t| t < since);
                        cs.extend(list[start..].iter().copied());
                    }
                    INCR_CONSIDERED.fetch_add(cs.len() as u64, Ordering::Relaxed);
                    INCR_SKIPPED.fetch_add(all.saturating_sub(cs.len()) as u64, Ordering::Relaxed);
                    cs
                } else {
                    match self.fn_index.get(&(sym, arity)) {
                        Some(c) => c.clone(),
                        None => return vec![],
                    }
                };
                let ground_root = hint.map(|t| self.find(t));
                let mut out = Vec::new();
                let mut considered: rustc_hash::FxHashSet<Vec<u32>> =
                    rustc_hash::FxHashSet::default();
                for cand in candidates {
                    if self.rel_shielded(cand) {
                        REL_SKIPPED_CANDIDATES.fetch_add(1, Ordering::Relaxed);
                        continue;
                    }
                    if let Some(gr) = ground_root
                        && self.find(cand) != gr
                    {
                        continue;
                    }
                    let subterms: Vec<u32> = self.reg_children(cand).to_vec();
                    let canonical: Vec<u32> = subterms.iter().map(|&s| self.find(s)).collect();
                    if !considered.insert(canonical) {
                        continue;
                    }
                    let mut sub_assignment = assignment.clone();
                    out.extend(self.match_subs(&mut sub_assignment, subs, &subterms, remaining));
                }
                out
            }
        }
    }

    fn match_subs(
        &self,
        assignment: &mut crate::utils::DeterministicHashMap<Local, u32>,
        sub_patterns: &[Pattern<u32>],
        grounds: &[u32],
        remaining: &[(PatternId, Option<u32>)],
    ) -> Vec<crate::utils::DeterministicHashMap<Local, u32>> {
        let Some(pattern) = sub_patterns.first() else {
            return self.match_pairs(assignment, remaining, false);
        };
        let ground = grounds[0];
        let rest_patterns = &sub_patterns[1..];
        let rest_grounds = &grounds[1..];
        match pattern {
            Pattern::Var(name) => match assignment.get(name) {
                None => {
                    assignment.insert(name.clone(), ground);
                    self.match_subs(assignment, rest_patterns, rest_grounds, remaining)
                }
                Some(&v) if self.find(v) == self.find(ground) => {
                    self.match_subs(assignment, rest_patterns, rest_grounds, remaining)
                }
                Some(_) => vec![],
            },
            Pattern::Ground(id) => {
                if self.find(*id) == self.find(ground) {
                    self.match_subs(assignment, rest_patterns, rest_grounds, remaining)
                } else {
                    vec![]
                }
            }
            Pattern::App(op, children) => {
                let Some(sym) = self.sym_lookup(op) else {
                    return vec![];
                };
                let arity = u32::try_from(children.len()).expect("arity fits u32");
                let Some(candidates) = self.fn_index.get(&(sym, arity)) else {
                    return vec![];
                };
                let ground_root = self.find(ground);
                let mut out = Vec::new();
                let mut considered: rustc_hash::FxHashSet<Vec<u32>> =
                    rustc_hash::FxHashSet::default();
                for &cand in candidates {
                    if self.rel_shielded(cand) {
                        REL_SKIPPED_CANDIDATES.fetch_add(1, Ordering::Relaxed);
                        continue;
                    }
                    if self.find(cand) != ground_root {
                        continue;
                    }
                    let subterms: Vec<u32> = self.reg_children(cand).to_vec();
                    let canonical: Vec<u32> = subterms.iter().map(|&s| self.find(s)).collect();
                    if !considered.insert(canonical) {
                        continue;
                    }
                    let mut sub_assignment = assignment.clone();
                    for mut sub in self.match_subs(&mut sub_assignment, children, &subterms, &[]) {
                        out.extend(self.match_subs(
                            &mut sub,
                            rest_patterns,
                            rest_grounds,
                            remaining,
                        ));
                    }
                }
                out
            }
        }
    }

    /// Translate one adapter trigger pattern into a semper AST pattern,
    /// collecting pattern variables (shared name table across the call) and
    /// ground leaves (recorded as globals). Returns `None` when an operator in
    /// the pattern indexes no term — the whole pattern then cannot match, the
    /// same verdict the top-down matcher reaches on an unknown symbol.
    fn build_sem_pattern(
        &self,
        pat: &Pattern<u32>,
        var_names: &mut Vec<Local>,
        var_of: &mut FxHashMap<Local, usize>,
        grounds: &mut Vec<(String, u32)>,
    ) -> Option<SemPattern> {
        match pat {
            Pattern::Var(local) => {
                let idx = *var_of.entry(local.clone()).or_insert_with(|| {
                    let i = var_names.len();
                    var_names.push(local.clone());
                    i
                });
                Some(SemPattern::Var(format!("pv{idx}"), SemSpan::Dummy))
            }
            // A ground subterm matches by equivalence class: bind it as a
            // global whose e-class the caller fills in after `rebuild`.
            Pattern::Ground(id) => {
                let name = format!("g{}", grounds.len());
                grounds.push((name.clone(), *id));
                Some(SemPattern::Var(name, SemSpan::Dummy))
            }
            Pattern::App(op, children) => {
                // The registry name is `{base}${arity}` (see `op_id`); an
                // operator the adapter never registered indexes no term.
                let name = format!("{}${}", op.to_function_map_key(), children.len());
                if self.eg.ops().id_by_name(&name).is_none() {
                    return None;
                }
                let mut kids = Vec::with_capacity(children.len());
                for c in children {
                    kids.push(self.build_sem_pattern(c, var_names, var_of, grounds)?);
                }
                Some(SemPattern::Plain {
                    op: name,
                    children: kids,
                    span: SemSpan::Dummy,
                })
            }
        }
    }

    /// Native e-matching: compile the trigger patterns to a semper query, run
    /// the engine's matcher against the live e-graph, and return the same
    /// substitutions (pattern variable -> driver term id) the top-down matcher
    /// would. `Some` is a complete, sound match set for `pairs`; `None` means
    /// "not modeled here, use the top-down matcher" — a non-application trigger
    /// root (not a well-formed SMT trigger), a resolve failure, or a binding
    /// with no driver id.
    fn match_triggers_native(
        &mut self,
        pairs: &[(PatternId, Option<u32>)],
    ) -> Option<Vec<crate::utils::DeterministicHashMap<Local, u32>>> {
        if pairs.is_empty() {
            return Some(vec![crate::utils::DeterministicHashMap::default()]);
        }

        // Phase A: translate adapter patterns into one semper query. The
        // variable table is shared across the pairs, so a `Local` recurring in
        // two patterns of a multipattern resolves to one engine variable and
        // the join happens natively.
        let mut var_names: Vec<Local> = Vec::new();
        let mut var_of: FxHashMap<Local, usize> = FxHashMap::default();
        let mut grounds: Vec<(String, u32)> = Vec::new();
        let mut sem_pats: Vec<SemPattern> = Vec::with_capacity(pairs.len());
        for &(pid, _) in pairs {
            let pat = &self.patterns[pid];
            if !matches!(pat, Pattern::App(..)) {
                return None; // top-down matcher binds a bare var/ground root
            }
            match self.build_sem_pattern(pat, &mut var_names, &mut var_of, &mut grounds) {
                Some(p) => sem_pats.push(p),
                None => return Some(Vec::new()), // an operator indexes no term
            }
        }

        // Root-candidate guard, for an unrooted call only (the call site passes
        // no hint when `trigger_root_candidates` returned `None`, i.e. the root
        // operator has more than `native_max_roots()` candidate classes, or
        // native is off). An unrooted query's root atom sweeps every term with
        // the root operator, and a deep pattern with no match exhausts that
        // join inside a single `next_match` that neither the pull cap nor the
        // time budget can interrupt (MiniAllocator.12: 655 unrooted
        // `has_type(apply(lambda(...)))` calls over 3796 terms, one of which
        // never returns). The top-down matcher scans the same `fn_index`
        // candidates with early termination and, measured, finds the identical
        // logical match set (SEMPER_NATIVE_DIFF reports a difference of 0), so
        // with many candidates the unrooted sweep buys nothing: bail to
        // top-down. No candidates means no match at all.
        if pairs[0].1.is_none()
            && let Pattern::App(op, subs) = &self.patterns[pairs[0].0]
        {
            let Some(sym) = self.sym_lookup(op) else {
                return Some(Vec::new()); // operator never interned: indexes no term
            };
            let arity = u32::try_from(subs.len()).expect("arity fits u32");
            self.ensure_fn_index();
            let n = self.fn_index.get(&(sym, arity)).map_or(0, |c| c.len());
            if n == 0 {
                return Some(Vec::new());
            }
            let max_roots = native_max_roots();
            if max_roots != 0 && n > max_roots {
                return None; // many roots, unrooted: top-down matcher is authoritative
            }
        }

        // Phase B: refresh the match index only when the e-graph changed since
        // the last build. On a cache hit the graph is already canonical (no
        // merges or new terms since the last rebuild) and the cached index is
        // reused — this is what makes thousands of same-level trigger-match
        // calls affordable instead of one O(nodes) build each.
        let key = (
            self.reg_log.len(),
            self.asserts.len(),
            self.epoch,
            self.rel_epoch,
        );
        if self.cached_index.is_none() || self.cached_index_key != key {
            self.eg.rebuild();
            self.cached_index = Some(IndexStore::build(&self.eg));
            let mut cm: FxHashMap<ENodeId, u32> = FxHashMap::default();
            for d in 0..self.terms.len() as u32 {
                let rep = self.eg.find_const(self.node(d));
                cm.entry(rep).or_insert(d);
            }
            self.cached_class_min = Some(cm);
            self.cached_index_key = key;
        }

        // Phase C: compile the query. Ground leaves become globals bound to
        // their current class; the first pattern's root is bound to the hint's
        // class when the call site passed one (see below).
        // SEMPER_NATIVE_TRACE=1: print each call's shape before enumeration, so
        // a call that never returns is identified by the last line printed. An
        // UNROOTED first pattern sweeps every term with its operator (the
        // blow-up shape); `rooted@c` binds the root to class c first.
        {
            static TRACE: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
            if *TRACE.get_or_init(|| std::env::var_os("SEMPER_NATIVE_TRACE").is_some()) {
                let desc: Vec<String> = pairs
                    .iter()
                    .map(|&(pid, h)| match h {
                        Some(t) => format!("p{pid}:rooted@{}", self.find(t)),
                        None => format!("p{pid}:UNROOTED"),
                    })
                    .collect();
                eprintln!(
                    "NATIVE_TRACE pairs={} [{}] terms={} pats={:?}",
                    pairs.len(),
                    desc.join(" "),
                    self.terms.len(),
                    pairs
                        .iter()
                        .map(|&(pid, _)| format!("{:?}", self.patterns[pid]))
                        .collect::<Vec<_>>()
                );
            }
        }
        // Rooting: `instantiate_quantifiers` passes the triggering term it got
        // from `trigger_root_candidates` (one call per distinct root class) as
        // the first pattern's hint. The engine's `node` (root) position always
        // resolves to a fresh local, so rooting goes through an injected
        // `(= root rh0)` atom: `resolve` lowers it to `EqGlobal` and the
        // scheduler's `BindGlobal` binds the root to that class before any
        // other atom scans. Without it the scheduler is free to scan the
        // variables' domains first, which on a flat all-variable pattern such
        // as `ens%update_headless_service(x1, x2, x3, ...)` over 4645 terms is
        // 4645^k and never returns from a single `next_match` (rabbitmq
        // headless_service.6 and five more Verus files): no pull cap, time
        // budget or engine step counter can interrupt one pull. The union over
        // the call site's hints is exactly the unrooted result, since the root
        // atom's operator already restricts the root to those nodes
        // (SEMPER_NATIVE_DIFF stays 0). Hints on later patterns of a
        // multipattern are not modeled natively: top-down handles them.
        if pairs[1..].iter().any(|&(_, h)| h.is_some()) {
            return None;
        }
        let roots: Vec<Option<ENodeId>> =
            vec![pairs[0].1.map(|t| self.eg.find_const(self.node(t)))];

        // Phase D: enumerate each rooted query and convert bindings to driver
        // ids. `catch_unwind` because the engine's pull matcher panics on query
        // shapes it cannot assemble (an unbound variable in `enter` on some
        // multipattern/ground-child triggers); this runs inside the CaDiCaL
        // propagator FFI callback, where an escaping panic is a non-unwinding
        // abort, so it must be caught and turned into a fall back to the
        // top-down matcher. The pull cap and the wall-time budget span the
        // whole call (all root classes). Enumeration only reads the e-graph
        // (the rebuild above is the sole mutation), so discarding a partial run
        // leaves no inconsistent state.
        install_quiet_native_panic_hook();
        // Relevancy (SEMPER_RELEVANCY=1) needs no step here: shielded nodes
        // are absent from the index (`FLAG_UNMATCHABLE`, honoured while the
        // round's matching shield is on), so the join never enumerates them.
        // Stable per-class binding driver (see `cached_class_min`): the
        // instantiation dedup keys on the substituted Term, so a binding must map
        // to the same term across rounds or the same logical match re-instantiates
        // and the search diverges. `node_to_driver[find_const(..)]` tracks the
        // union-find rep, which shifts on merges; the earliest-registered driver
        // per class is stable, mirroring the top-down matcher's earliest-candidate
        // binding.
        let class_min = self
            .cached_class_min
            .as_ref()
            .expect("class_min built in Phase B");
        let budget_ms = native_match_budget_ms();
        let start = std::time::Instant::now();
        let mut pulls: u64 = 0;
        let mut out_all: Vec<crate::utils::DeterministicHashMap<Local, u32>> = Vec::new();
        for root in roots {
            // Phase C, per root: compile the query. Ground leaves become
            // globals bound to their current class; the root, when given,
            // becomes the `rh0` global.
            let mut fq = sem_flatten(&sem_pats);
            let mut globals: GlobalCtx<SortId, ENodeId> = GlobalCtx::new();
            for (name, driver) in &grounds {
                let cls = self.eg.find_const(self.node(*driver));
                globals.insert(name.clone(), self.term_sort, cls);
            }
            if let Some(cls) = root {
                let gname = "rh0".to_string();
                globals.insert(gname.clone(), self.term_sort, cls);
                fq.atoms.push(Atom::Eq(fq.root_vars[0].clone(), gname));
            }
            let rq =
                sem_resolve(&fq, self.eg.ops(), self.eg.sorts(), &MachineModel, &globals).ok()?;
            let shape = rq.shape.clone();
            let plan = sem_schedule(&rq);
            // VarId of each distinct Local, for the output substitution. A name
            // resolve did not place in the shape means a shape this path does
            // not model — bail rather than mis-report.
            let mut var_vids: Vec<(Local, VarId)> = Vec::with_capacity(var_names.len());
            for (i, local) in var_names.iter().enumerate() {
                var_vids.push((local.clone(), shape.find_var(&format!("pv{i}"))?));
            }

            SUPPRESS_PANIC_MSG.with(|c| c.set(true));
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let index = VariantIndex::naive(
                    self.cached_index
                        .as_ref()
                        .expect("match index built in Phase B"),
                );
                let mut it = MatchIterator::new(&plan, &self.eg, &index, &globals);
                let mut out: Vec<crate::utils::DeterministicHashMap<Local, u32>> = Vec::new();
                while it.next_match() {
                    pulls += 1;
                    if pulls > NATIVE_MATCH_PULL_CAP {
                        return None; // runaway enumeration: top-down matcher is authoritative
                    }
                    // Wall-time bail: a join whose per-pull cost is high (not
                    // its count) runs past the solver timeout in one call.
                    // Checked every 64 pulls to keep `Instant::now` off the hot
                    // path.
                    if budget_ms != 0
                        && pulls & 0x3f == 0
                        && start.elapsed().as_millis() as u64 > budget_ms
                    {
                        // Latch native off for the rest of this solve: this
                        // join is pathological for the engine, and paying the
                        // budget on every subsequent call accumulates past the
                        // solver timeout.
                        self.native_time_bailed.set(true);
                        return None; // over time budget: top-down matcher is authoritative
                    }
                    let m = it.env();
                    let mut subst = crate::utils::DeterministicHashMap::default();
                    for (local, vid) in &var_vids {
                        let cls = self.eg.find_const(m.get(*vid));
                        let driver = class_min
                            .get(&cls)
                            .copied()
                            .unwrap_or_else(|| self.node_to_driver[cls.to_usize()]);
                        if driver == NO_DRIVER {
                            return None; // unnameable class: top-down matcher is authoritative
                        }
                        subst.insert(local.clone(), driver);
                    }
                    out.push(subst);
                }
                Some(out)
            }));
            SUPPRESS_PANIC_MSG.with(|c| c.set(false));
            match result {
                Ok(Some(out)) => out_all.extend(out),
                Ok(None) => return None, // bailed: top-down matcher is authoritative
                Err(_) => return None, // engine could not match this shape: use the top-down matcher
            }
        }
        Some(out_all)
    }
}

impl EgraphTrait for SemperEgraph {
    fn refutation_tainted(&self) -> bool {
        self.tf_taint
    }

    fn true_false_conflict_pending(&self) -> bool {
        // Set when `violated_diseq` reports a true=false collision, cleared on
        // backtrack. While set, a later merge at the same level that keeps true
        // and false merged is not re-reported, so the driver must not treat the
        // persisting collision as an undetected merge.
        self.reported_tf
    }

    type Op = Op;
    type TermId = u32;

    fn register_term(&mut self, op: Op, children: &[u32], _dynamic: bool) -> u32 {
        // Hash-consing plus build-time child canonicalization make every
        // registration "dynamic": a term congruent to an existing one under
        // the current classes interns to that node.
        self.ensure_scope();
        let sym = self.sym_id(&op);
        self.push_registration(RegEvent::Term {
            sym,
            children: children.to_vec(),
        })
    }

    fn register_constant(&mut self, op: Op) -> u32 {
        let tf = match &op {
            Op::Constant(s) if s == "true" => Some(true),
            Op::Constant(s) if s == "false" => Some(false),
            _ => None,
        };
        self.ensure_scope();
        let sym = self.sym_id(&op);
        let id = self.push_registration(RegEvent::Term {
            sym,
            children: Vec::new(),
        });
        match tf {
            Some(true) => self.true_term.get_or_insert(id),
            Some(false) => self.false_term.get_or_insert(id),
            None => return id,
        };
        id
    }

    fn register_opaque(&mut self) -> u32 {
        self.ensure_scope();
        self.opaque_count += 1;
        self.push_registration(RegEvent::Opaque)
    }

    fn compile_pattern(&mut self, pattern: Pattern<u32>) -> PatternId {
        self.incr_max_depth = self.incr_max_depth.max(pattern_depth(&pattern));
        fn labels(
            p: &Pattern<u32>,
            pairs: &mut rustc_hash::FxHashSet<(Op, u32, Op)>,
            vars: &mut rustc_hash::FxHashSet<(Op, u32)>,
            grounds: &mut rustc_hash::FxHashSet<(Op, u32)>,
            ops: &mut rustc_hash::FxHashSet<Op>,
        ) {
            if let Pattern::App(f, subs) = p {
                ops.insert(f.clone());
                for (i, sub) in subs.iter().enumerate() {
                    match sub {
                        Pattern::App(g, _) => {
                            pairs.insert((f.clone(), i as u32, g.clone()));
                        }
                        Pattern::Var(_) => {
                            vars.insert((f.clone(), i as u32));
                        }
                        Pattern::Ground(_) => {
                            grounds.insert((f.clone(), i as u32));
                        }
                    }
                    labels(sub, pairs, vars, grounds, ops);
                }
            }
        }
        labels(
            &pattern,
            &mut self.pc_pairs,
            &mut self.pc_var,
            &mut self.pc_ground,
            &mut self.pattern_ops,
        );
        self.patterns.push(pattern);
        self.patterns.len() - 1
    }

    fn register_eq(&mut self, t1: u32, t2: u32, lit: Lit) {
        self.eq_watches.push((t1, t2, lit));
    }

    fn register_boolean_term(&mut self, op: Op, children: &[u32], _lit: Lit) -> u32 {
        self.ensure_scope();
        let sym = self.sym_id(&op);
        self.push_registration(RegEvent::Term {
            sym,
            children: children.to_vec(),
        })
    }

    fn mark_arithmetic(&mut self, term: u32) {
        self.arithmetic_terms.push(term);
        // Seed the arithmetic flag on the term's current class root. Merges are
        // propagated later, in the drain fold.
        let root = self.eg.find_const(self.node(term));
        self.arith_roots.insert(root);
        self.link_intern_driver(term);
    }

    fn incremental_arithmetic(&mut self, enabled: bool) {
        self.incremental_arith = enabled;
        // Turn the engine's merge capture on/off in lockstep: EUF-only runs
        // leave it off and the engine records nothing.
        // Relevancy reads the same log (merge closure), so it stays on while
        // relevancy is enabled.
        self.eg.set_record_merges(enabled || self.relevancy_enabled);
    }

    fn discard_speculative_arithmetic_equalities(&mut self) {
        // The merge log holds the probe's speculative merges: drain them as
        // usual (relevancy and the arithmetic class flags read them) and drop
        // the result. The intern-time pairs (`intern_eqs_pending`)
        // come from registrations, not from the probe, and each is emitted
        // once (`intern_eqs_emitted`), so discarding them here lost them for
        // good; they stay queued for the next real drain.
        let kept = std::mem::take(&mut self.intern_eqs_pending);
        let _ = self.drain_arithmetic_equalities();
        self.intern_eqs_pending = kept;
    }

    fn drain_arithmetic_equalities(&mut self) -> Vec<(u32, u32)> {
        // Fold the engine's merge log (captured at merge time, in order) into
        // arithmetic-class equalities. A merge whose survivor or absorbed class
        // is arithmetic yields an equality between the two class names and makes
        // the merged class arithmetic (OR semantics, mirroring the basic
        // backend's per-root flag). The pairing is read from the pre-merge
        // roots, which is why capture happens in the engine, not here.
        self.rel_absorb_merges();
        let merges = self.eg.take_merged_log();
        self.rel_merge_cursor = 0;
        let mut out: Vec<(u32, u32)> = Vec::with_capacity(merges.len());
        for (survivor, absorbed) in merges {
            let s_arith = self.arith_roots.contains(&survivor);
            let a_arith = self.arith_roots.contains(&absorbed);
            if s_arith || a_arith {
                let ds = self.node_to_driver[survivor.to_usize()];
                let da = self.node_to_driver[absorbed.to_usize()];
                debug_assert!(
                    ds != NO_DRIVER && da != NO_DRIVER,
                    "merged class roots come from registrations and carry a driver id"
                );
                out.push((ds, da));
                // The post-merge root is the survivor; the absorbed root is no
                // longer a root. Carry the arithmetic flag onto the survivor.
                self.arith_roots.insert(survivor);
            }
            // Keep the set over current roots only.
            self.arith_roots.remove(&absorbed);
        }
        // Intern-time pairs: two arithmetic drivers of one node, which no
        // merge ever reports (see `intern_by_node`).
        out.append(&mut self.intern_eqs_pending);
        out
    }

    fn notify_new_decision_level(&mut self) {
        let prof_t = crate::egraphs::trail_prof::enabled().then(std::time::Instant::now);
        // Lazy: the token is taken by the first mutation at this level, if
        // any (see `ensure_scope`).
        self.level += 1;
        if let Some(t) = prof_t {
            crate::egraphs::trail_prof::record_level(t.elapsed().as_nanos() as u64);
        }
    }

    fn assert_equal(&mut self, t1: u32, t2: u32) -> EgraphResult<u32> {
        self.ensure_scope();
        let idx = self.asserts.len();
        self.asserts.push((t1, t2));
        let word = u32::try_from(idx).expect("assertion log exceeds the index word");
        let merged = self.eg.merge_justified(
            self.node(t1),
            self.node(t2),
            Justification::Assumption { lit: word },
        );
        // Seed the relevancy roots only with genuine top-level Boolean
        // assertions: the driver asserts an atom's truth by merging its node
        // with the true/false constant, so an assert_equal at level 0 with one
        // constant endpoint means "this Boolean atom is asserted", and the
        // other endpoint IS that atom. A plain equality like (= x0 x1) reaches
        // assert_equal as its two term sides, which are NOT Boolean atoms and
        // must not seed the cone (that seeded from constants and marked
        // everything relevant); its own atom node is seeded separately by the
        // true/false merge.
        if self.level == 0 {
            self.seed_root_if_boolean(t1, t2);
        }
        if merged.is_none() {
            // Already equal: no class changed, so no rebuild is needed and
            // no disequality can have become violated.
            return EgraphResult::ok();
        }
        self.stats.merges += 1;
        self.eg.rebuild();
        self.result_after_merge()
    }

    fn assert_disequal(&mut self, t1: u32, t2: u32, lit: Lit) -> EgraphResult<u32> {
        self.ensure_scope();
        let r1 = self.eg.find_const(self.node(t1));
        let r2 = self.eg.find_const(self.node(t2));
        if self.level == 0 {
            self.seed_root_if_boolean(t1, t2);
        }
        self.diseqs.push((t1, t2, lit));
        self.diseq_roots.push((r1, r2));
        self.diseq_epoch.push(self.epoch);
        if r1 == r2 {
            self.reported_diseqs.insert(self.diseqs.len() - 1);
            return EgraphResult::with_conflict(Conflict {
                equalities: self.explain_conflict(t1, t2),
                disequality: (t1, t2),
                diseq_lit: Some(lit),
            });
        }
        EgraphResult::ok()
    }

    fn assert_distinct(&mut self, terms: &[u32], lit: Lit) -> EgraphResult<u32> {
        for (i, &t1) in terms.iter().enumerate() {
            for &t2 in &terms[i + 1..] {
                let r = self.assert_disequal(t1, t2, lit);
                if r.conflict.is_some() {
                    return r;
                }
            }
        }
        EgraphResult::ok()
    }

    fn find(&self, term: u32) -> u32 {
        let root = self.eg.find_const(self.node(term));
        // Every engine node was produced by a registration, so the root
        // always has a driver id; its first registrant is the class name.
        let d = self.node_to_driver[root.to_usize()];
        debug_assert_ne!(d, NO_DRIVER, "every node comes from a registration");
        d
    }

    fn are_equal(&self, t1: u32, t2: u32) -> bool {
        self.eg.find_const(self.node(t1)) == self.eg.find_const(self.node(t2))
    }

    fn match_triggers(
        &mut self,
        trigger_term_pairs: Vec<(PatternId, Option<u32>)>,
    ) -> Vec<crate::utils::DeterministicHashMap<Local, u32>> {
        if !self.ematch_enabled {
            return Vec::new();
        }
        if self.native_ematch && !self.native_time_bailed.get() {
            NATIVE_MATCH_CALLS.fetch_add(1, Ordering::Relaxed);
            let native = self.match_triggers_native(&trigger_term_pairs);
            // SEMPER_NATIVE_DIFF=1: run the top-down matcher too and report the
            // *logical* set difference (bindings canonicalized to their class, so
            // class-rep vs concrete-child driver choices do not masquerade as
            // match differences). Isolates whether native finds genuinely more
            // matches or merely differs in binding representation.
            if std::env::var_os("SEMPER_NATIVE_DIFF").is_some() {
                self.ensure_fn_index();
                let mut a = crate::utils::DeterministicHashMap::default();
                let td = self.match_pairs(&mut a, &trigger_term_pairs, false);
                let canon = |set: &[crate::utils::DeterministicHashMap<Local, u32>]| {
                    let mut keys: rustc_hash::FxHashSet<Vec<(Local, u32)>> =
                        rustc_hash::FxHashSet::default();
                    for m in set {
                        let mut kv: Vec<(Local, u32)> =
                            m.iter().map(|(l, &d)| (l.clone(), self.find(d))).collect();
                        kv.sort();
                        keys.insert(kv);
                    }
                    keys
                };
                if let Some(nat) = &native {
                    let nk = canon(nat);
                    let tk = canon(&td);
                    if nk != tk {
                        let only_n = nk.difference(&tk).count();
                        let only_t = tk.difference(&nk).count();
                        eprintln!(
                            "NATIVE_DIFF pairs={} native={} topdown={} native_only={} topdown_only={}",
                            trigger_term_pairs.len(),
                            nk.len(),
                            tk.len(),
                            only_n,
                            only_t
                        );
                    }
                }
            }
            if let Some(matches) = native {
                self.last_match_native.set(true);
                return matches;
            }
            // Bailed (non-application root, resolve failure, or an unconvertible
            // binding): fall through to the top-down matcher, which is correct
            // for every trigger shape.
            NATIVE_MATCH_FALLBACKS.fetch_add(1, Ordering::Relaxed);
        }
        self.last_match_native.set(false);
        self.ensure_fn_index();
        let mut filter = incr_match() && self.incr_active;
        if filter {
            let first = trigger_term_pairs[0].0;
            let prev = self.incr_last_scanned.insert(first, self.incr_round);
            // Scanned in the previous round: the diff since then is exact.
            // Otherwise the pattern was inactive and needs the whole graph.
            filter = prev == Some(self.incr_round - 1);
        }
        let mut assignment = crate::utils::DeterministicHashMap::default();
        let matches = self.match_pairs(&mut assignment, &trigger_term_pairs, filter);
        if incr_match_diff() && trigger_term_pairs.len() == 1 {
            if filter {
                self.incr_diff(trigger_term_pairs[0].0, &matches);
            } else {
                // Unfiltered call: every match is known from here on.
                self.incr_seen
                    .entry(trigger_term_pairs[0].0)
                    .or_default()
                    .extend(matches.iter().cloned());
            }
        }
        matches
    }

    /// One triggering term per distinct e-class carrying the pattern's root
    /// operator, from `fn_index`. `None` when the native matcher is off or
    /// latched off (the top-down matcher scans `fn_index` once, unrooted,
    /// with early termination; per-root calls would make that O(roots x
    /// candidates)), when the first pattern is not an application, or when
    /// the operator has more than `native_max_roots()` candidate classes
    /// (the unrooted native call then bails to top-down in
    /// `match_triggers_native`). `Some(empty)` when the operator indexes no
    /// term.
    fn trigger_root_candidates(&mut self, pattern: PatternId) -> Option<Vec<u32>> {
        if !self.ematch_enabled || !self.native_ematch || self.native_time_bailed.get() {
            return None;
        }
        let Pattern::App(op, subs) = &self.patterns[pattern] else {
            return None;
        };
        let Some(sym) = self.sym_lookup(op) else {
            return Some(Vec::new());
        };
        let arity = u32::try_from(subs.len()).expect("arity fits u32");
        self.ensure_fn_index();
        let Some(cands) = self.fn_index.get(&(sym, arity)) else {
            return Some(Vec::new());
        };
        let max_roots = native_max_roots();
        if max_roots != 0 && cands.len() > max_roots {
            return None;
        }
        let mut seen: rustc_hash::FxHashSet<ENodeId> = rustc_hash::FxHashSet::default();
        let mut out = Vec::new();
        for &t in cands {
            // A shielded node has no index entry this round, so rooting a
            // native call at it would find nothing.
            if self.rel_shielded(t) {
                continue;
            }
            if seen.insert(self.eg.find_const(self.node(t))) {
                out.push(t);
            }
        }
        Some(out)
    }

    fn last_match_native(&self) -> bool {
        self.last_match_native.get()
    }

    fn note_instance_root(&mut self, term: u32) {
        self.instance_roots.push(term);
        let i = term as usize;
        if i >= self.rel_instance_root.len() {
            self.rel_instance_root.resize(i + 1, false);
        }
        self.rel_instance_root[i] = true;
    }

    fn note_assignment(&mut self, term: u32) {
        self.rel_on_assignment(term);
    }

    fn begin_matching_round(&mut self) {
        if incr_match() {
            self.incr_begin_round();
        }
    }

    fn incremental_matching(&self) -> bool {
        incr_match()
    }

    fn set_relevancy_active(&mut self, active: bool) {
        // Called once at the start of every matching round by the propagator:
        // eager rounds are filtered (shield on, relevant set refreshed), the
        // complete-model round sees every node (shield off).
        self.relevancy_active = active;
        if !self.relevancy_enabled {
            return;
        }
        // Shield going off: every shielded term becomes matchable without a
        // mark, so the incremental matcher scans every pattern in full.
        if self.eg.matching_shield() && !(active && !rel_nofilter()) {
            self.incr_last_scanned.clear();
        }
        self.eg.set_matching_shield(active && !rel_nofilter());
        self.rel_epoch += 1;
        if active {
            self.rel_refresh();
        }
    }

    fn is_term_relevant(&self, term: u32) -> bool {
        let r = !self.rel_filtering() || self.eg.is_node_matchable(self.node(term));
        if !r {
            REL_SKIPPED_QUANTIFIERS.fetch_add(1, Ordering::Relaxed);
        }
        r
    }

    fn backtrack_to(&mut self, level: usize) {
        let prof_t = crate::egraphs::trail_prof::enabled().then(std::time::Instant::now);
        self.level = level;
        self.reported_diseqs.clear();
        // `reported_tf` is refreshed from the post-restore true/false roots at
        // the end of this function, not cleared here: a ground (level-0)
        // true=false collision the restore does not separate is still pending
        // and must stay latched.
        // Marks are level-ascending; the first one above the target is the
        // restore point, and it also undoes every deeper mark (ancestor
        // restore). No mark above the target means no e-graph mutation
        // happened there: nothing to undo.
        let pos = self.marks.partition_point(|&(l, _)| l <= level);
        if pos == self.marks.len() {
            if let Some(t) = prof_t {
                crate::egraphs::trail_prof::record_backtrack(t.elapsed().as_nanos() as u64);
            }
            return;
        }
        let (_, mark) = self
            .marks
            .drain(pos..)
            .next()
            .expect("guarded by the length check above");
        self.eg.restore(mark.token);
        // Cached disequality roots may name nodes deleted by the restore.
        self.epoch += 1;
        // The restore may have dropped ops registered in the popped scopes;
        // the cache would hand out their dangling ids, so it is cleared and
        // repopulated from the registry on demand.
        self.ops.clear();
        self.asserts.truncate(mark.asserts_len);
        self.diseqs.truncate(mark.diseqs_len);
        self.diseq_roots.truncate(mark.diseqs_len);
        self.diseq_epoch.truncate(mark.diseqs_len);
        // Terms registered above the restore point were deleted with it, but
        // the driver's id maps still name them: replay their registrations
        // into the restored graph and repair the table entries.
        for i in mark.reg_len..self.reg_log.len() {
            let before = self.eg.node_count();
            let node = self.intern(i);
            self.rel_shield_if_fresh(node, before);
            let table_index = self.terms.len() - (self.reg_log.len() - i);
            self.terms[table_index] = node;
        }
        // Relevancy: the restore undid the marks of the popped levels (they
        // live in the node flags); drop the gates they recorded, restart the
        // merge-log cursor (the restore cleared the log), and invalidate the
        // native index.
        self.rel_gates.truncate(mark.rel_gates_len);
        self.rel_queue.clear();
        self.rel_merge_cursor = 0;
        self.rel_epoch += 1;
        // Replay can re-mint node ids, so the reverse map is rebuilt from
        // the repaired table (first registrant wins, as at registration).
        if mark.reg_len < self.reg_log.len() {
            for e in self.node_to_driver.iter_mut() {
                *e = NO_DRIVER;
            }
            let terms = std::mem::take(&mut self.terms);
            for (i, &node) in terms.iter().enumerate() {
                self.set_node_driver(node, i as u32);
            }
            self.terms = terms;
        }
        // The restore undid (and may have re-minted) the engine roots that
        // `arith_roots` named, so rebuild it from the surviving arithmetic terms
        // against the restored union-find. Drain-before-advance keeps the merge
        // log empty here, and the engine cleared it on restore, so the next
        // drain reports no stale equality.
        if self.incremental_arith {
            self.arith_roots.clear();
            // Replay may have interned the surviving arithmetic drivers into
            // different nodes than before the restore, so the per-node first
            // driver map is rebuilt as well; a pair already linked keeps its
            // literal (the e-graph watch justifies it at whatever level it
            // holds), a newly co-interned pair is reported at the next drain.
            self.intern_by_node.clear();
            // Forget the pairs emitted in the popped levels (the arithmetic
            // solver dropped them), so the relinking below emits them again
            // when the two drivers still share a node.
            if !intern_eq_legacy() && mark.intern_eqs_len < self.intern_eqs_trail.len() {
                let popped: rustc_hash::FxHashSet<(u32, u32)> =
                    self.intern_eqs_trail.drain(mark.intern_eqs_len..).collect();
                for p in &popped {
                    self.intern_eqs_emitted.remove(p);
                }
                self.intern_eqs_pending.retain(|p| !popped.contains(p));
            }
            let terms = std::mem::take(&mut self.arithmetic_terms);
            for &t in &terms {
                let root = self.eg.find_const(self.node(t));
                self.arith_roots.insert(root);
                self.link_intern_driver(t);
            }
            self.arithmetic_terms = terms;
        }
        // A reported true=false collision the restore did not separate is still
        // pending: keep it latched so a later same-level assignment is not taken
        // for an undetected merge. A restore that separated them clears it.
        let tf_still_merged = match (self.true_term, self.false_term) {
            (Some(t), Some(f)) => {
                self.eg.find_const(self.node(t)) == self.eg.find_const(self.node(f))
            }
            _ => false,
        };
        self.reported_tf = self.reported_tf && tf_still_merged;
        if let Some(t) = prof_t {
            crate::egraphs::trail_prof::record_backtrack(t.elapsed().as_nanos() as u64);
        }
    }

    fn suggest_decision(&self) -> Option<(u32, bool)> {
        if !self.decide_enabled {
            return None;
        }
        let tr = self.true_term.map(|t| self.eg.find_const(self.node(t)));
        let fr = self.false_term.map(|t| self.eg.find_const(self.node(t)));
        let mut visited: rustc_hash::FxHashSet<(u32, bool)> = rustc_hash::FxHashSet::default();
        for &r in &self.root_terms {
            if let Some(d) = self.suggest_rec(r, true, tr, fr, &mut visited) {
                return Some(d);
            }
        }
        None
    }

    fn make_decision(&self, _assignments: &[i32]) -> i32 {
        0
    }

    fn make_decision_lit(&self, _lit: Lit, _assignments: &[i32]) -> Lit {
        0
    }

    fn explain_equality(&self, t1: u32, t2: u32) -> Option<Vec<(u32, u32)>> {
        if !self.are_equal(t1, t2) {
            return None;
        }
        if explain_legacy() {
            return Some(self.explain_pairs(t1, t2));
        }
        // No `&mut self` here to taint: an unrecoverable step falls back to
        // the whole assertion trail, which is a sound (maximal) antecedent set.
        let (eqs, tainted) = self.explain_complete(t1, t2);
        Some(if tainted { self.asserts.clone() } else { eqs })
    }
}

impl fmt::Display for SemperEgraph {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "SemperEgraph: {} terms, {} asserts, {} diseqs, level {}",
            self.terms.len(),
            self.asserts.len(),
            self.diseqs.len(),
            self.level
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn constant(e: &mut SemperEgraph, name: &str) -> u32 {
        e.register_constant(Op::Constant(name.to_string()))
    }

    #[test]
    fn transitivity_conflict_reports_path_and_diseq_lit() {
        let mut e = SemperEgraph::new();
        let a = constant(&mut e, "a");
        let b = constant(&mut e, "b");
        let c = constant(&mut e, "c");
        assert!(e.assert_equal(a, b).conflict.is_none());
        assert!(e.assert_equal(b, c).conflict.is_none());
        let r = e.assert_disequal(a, c, 7);
        let conflict = r.conflict.expect("a=b, b=c contradicts a!=c");
        assert_eq!(conflict.disequality, (a, c));
        assert_eq!(conflict.diseq_lit, Some(7));
        let mut expected = vec![(a, b), (b, c)];
        expected.sort_unstable();
        assert_eq!(conflict.equalities, expected);
    }

    #[test]
    fn congruence_conflict_explains_leaf_assertion() {
        let mut e = SemperEgraph::new();
        let a = constant(&mut e, "a");
        let b = constant(&mut e, "b");
        let fa = e.register_term(Op::App("f".to_string()), &[a], false);
        let fb = e.register_term(Op::App("f".to_string()), &[b], false);
        assert!(e.assert_disequal(fa, fb, 3).conflict.is_none());
        let r = e.assert_equal(a, b);
        let conflict = r.conflict.expect("a=b forces f(a)=f(b)");
        assert_eq!(conflict.disequality, (fa, fb));
        assert_eq!(conflict.diseq_lit, Some(3));
        assert_eq!(conflict.equalities, vec![(a, b)]);
    }

    // Acceptance #2: a congruence-derived merge of two arithmetic classes is
    // drained as the equality between the two tagged terms; a non-arithmetic
    // merge produces nothing.
    #[test]
    fn drain_exports_congruence_equality_of_tagged_terms() {
        let mut e = SemperEgraph::new();
        e.incremental_arithmetic(true);
        let a = constant(&mut e, "a");
        let b = constant(&mut e, "b");
        let fa = e.register_term(Op::App("f".to_string()), &[a], false);
        let fb = e.register_term(Op::App("f".to_string()), &[b], false);
        e.mark_arithmetic(fa);
        e.mark_arithmetic(fb);
        // Direct merge a=b (neither tagged) rebuilds into the congruence
        // f(a)=f(b) (both tagged).
        assert!(e.assert_equal(a, b).conflict.is_none());
        let eqs = e.drain_arithmetic_equalities();
        assert_eq!(
            eqs.len(),
            1,
            "only the arithmetic congruence f(a)=f(b) is exported, not a=b: {eqs:?}"
        );
        let got: std::collections::BTreeSet<u32> = [eqs[0].0, eqs[0].1].into_iter().collect();
        let want: std::collections::BTreeSet<u32> = [fa, fb].into_iter().collect();
        assert_eq!(got, want, "drained pair must be the two tagged terms");
        // Draining is a take.
        assert!(e.drain_arithmetic_equalities().is_empty());
    }

    // Acceptance #3: after a restore across a decision level the next drain
    // reports no stale equality, and arith_roots is rebuilt so a re-merge still
    // exports correctly.
    #[test]
    fn drain_is_restore_safe() {
        let mut e = SemperEgraph::new();
        e.incremental_arithmetic(true);
        let a = constant(&mut e, "a");
        let b = constant(&mut e, "b");
        let fa = e.register_term(Op::App("f".to_string()), &[a], false);
        let fb = e.register_term(Op::App("f".to_string()), &[b], false);
        e.mark_arithmetic(fa);
        e.mark_arithmetic(fb);

        e.notify_new_decision_level();
        assert!(e.assert_equal(a, b).conflict.is_none());
        assert!(e.are_equal(fa, fb));
        assert_eq!(e.drain_arithmetic_equalities().len(), 1);

        // Restore: the congruence is undone, and the next drain is empty.
        e.backtrack_to(0);
        assert!(!e.are_equal(fa, fb), "restore undoes the congruence");
        assert!(
            e.drain_arithmetic_equalities().is_empty(),
            "no stale equality after restore"
        );

        // arith_roots was rebuilt from the surviving tagged terms, so a fresh
        // re-merge still exports f(a)=f(b).
        e.notify_new_decision_level();
        assert!(e.assert_equal(a, b).conflict.is_none());
        let eqs = e.drain_arithmetic_equalities();
        assert_eq!(eqs.len(), 1, "post-restore re-merge still exports: {eqs:?}");
        let got: std::collections::BTreeSet<u32> = [eqs[0].0, eqs[0].1].into_iter().collect();
        let want: std::collections::BTreeSet<u32> = [fa, fb].into_iter().collect();
        assert_eq!(got, want);
    }

    /// Reproduction of `conformance::semper::random_conflicts_are_valid`
    /// seed 31 (engine-only explanations): after a backtrack the replayed
    /// `f(c3)` and `f(g(f(c1,c2)))` shared a node without recorded evidence.
    #[test]
    fn replay_keeps_creation_evidence() {
        let mut e = SemperEgraph::new();
        let app = |e: &mut SemperEgraph, f: &str, ch: &[u32]| {
            e.register_term(Op::App(f.to_string()), ch, true)
        };
        let c: Vec<u32> = (0..4).map(|i| app(&mut e, &format!("c{i}"), &[])).collect();
        let (c0, c1, c2, c3) = (c[0], c[1], c[2], c[3]);
        e.notify_new_decision_level();
        let _ = e.assert_equal(c0, c3);
        e.backtrack_to(0);
        let _ = e.assert_equal(c3, c0);
        let _ = e.assert_equal(c2, c0);
        let _ = e.assert_equal(c3, c1);
        e.notify_new_decision_level();
        let _g6 = app(&mut e, "g", &[c1, c2]);
        let _ = e.assert_equal(c0, c2);
        let f7 = app(&mut e, "f", &[c1, c2]);
        e.backtrack_to(0);
        let g8 = app(&mut e, "g", &[f7]);
        e.notify_new_decision_level();
        let _ = e.assert_equal(g8, c3);
        e.notify_new_decision_level();
        e.notify_new_decision_level();
        e.notify_new_decision_level();
        e.notify_new_decision_level();
        let f12 = app(&mut e, "f", &[g8]);
        e.notify_new_decision_level();
        let f16 = app(&mut e, "f", &[c3]);
        e.backtrack_to(1);
        let n12 = e.node(f12);
        let n16 = e.node(f16);
        assert!(e.are_equal(f12, f16));
        let mut buf = e.scratch.borrow_mut();
        buf.steps.clear();
        let ok = e.eg.explain_deep(n12, n16, &mut buf);
        let assumptions: Vec<_> = buf
            .steps
            .iter()
            .filter_map(|&(_, _, j)| match j {
                Justification::Assumption { lit } => Some(e.asserts[lit.as_usize()]),
                _ => None,
            })
            .collect();
        assert!(ok);
        assert!(
            assumptions.contains(&(g8, c3)) || assumptions.contains(&(c3, g8)),
            "f(c3) = f(g(f(c1,c2))) must cite g8 = c3; got {assumptions:?}"
        );
    }

    #[test]
    fn eq_atoms_intern_symmetrically() {
        let mut e = SemperEgraph::new();
        let a = constant(&mut e, "a");
        let b = constant(&mut e, "b");
        let ab = e.register_term(Op::Eq, &[a, b], false);
        let ba = e.register_term(Op::Eq, &[b, a], false);
        assert!(e.are_equal(ab, ba));
    }

    #[test]
    fn backtrack_is_one_restore_across_levels() {
        let mut e = SemperEgraph::new();
        let a = constant(&mut e, "a");
        let b = constant(&mut e, "b");
        let c = constant(&mut e, "c");
        e.notify_new_decision_level();
        assert!(e.assert_equal(a, b).conflict.is_none());
        e.notify_new_decision_level();
        assert!(e.assert_equal(b, c).conflict.is_none());
        assert!(e.are_equal(a, c));
        e.backtrack_to(0);
        assert!(!e.are_equal(a, b));
        assert!(!e.are_equal(b, c));
    }

    #[test]
    fn terms_registered_in_scope_survive_backtrack() {
        // The driver's id maps are never rolled back, so a term registered
        // at level 1 must stay usable after backtracking to level 0.
        let mut e = SemperEgraph::new();
        let a = constant(&mut e, "a");
        let b = constant(&mut e, "b");
        e.notify_new_decision_level();
        let fa = e.register_term(Op::App("f".to_string()), &[a], false);
        assert!(e.assert_equal(fa, b).conflict.is_none());
        e.backtrack_to(0);
        // The equality is undone; the term is not.
        assert!(!e.are_equal(fa, b));
        let fa2 = e.register_term(Op::App("f".to_string()), &[a], false);
        assert!(e.are_equal(fa, fa2));
        // And it still participates in congruence.
        e.notify_new_decision_level();
        let c = constant(&mut e, "c");
        let fc = e.register_term(Op::App("f".to_string()), &[c], false);
        assert!(e.assert_equal(a, c).conflict.is_none());
        assert!(e.are_equal(fa, fc));
    }

    #[test]
    fn levels_without_writes_take_no_token_and_backtrack_correctly() {
        let mut e = SemperEgraph::new();
        let a = constant(&mut e, "a");
        let b = constant(&mut e, "b");
        let c = constant(&mut e, "c");
        // Levels 1 and 2 do only Boolean work (no e-graph calls); the first
        // mutation happens at level 3.
        e.notify_new_decision_level();
        e.notify_new_decision_level();
        e.notify_new_decision_level();
        assert!(e.assert_equal(a, b).conflict.is_none());
        assert_eq!(e.marks.len(), 1, "only the mutating level takes a token");
        // Backtracking to an empty level above the mark undoes level 3's
        // merge (the state at level 2's end equals the pre-mark state).
        e.backtrack_to(2);
        assert!(!e.are_equal(a, b));
        assert!(e.marks.is_empty());
        // Backtracking through levels that never materialized is a no-op.
        e.backtrack_to(0);
        assert!(!e.are_equal(a, b));
        // The next scope works normally.
        e.notify_new_decision_level();
        assert!(e.assert_equal(b, c).conflict.is_none());
        e.backtrack_to(0);
        assert!(!e.are_equal(b, c));
    }

    #[test]
    fn distinct_is_pairwise() {
        let mut e = SemperEgraph::new();
        let a = constant(&mut e, "a");
        let b = constant(&mut e, "b");
        let c = constant(&mut e, "c");
        assert!(e.assert_distinct(&[a, b, c], 9).conflict.is_none());
        let r = e.assert_equal(a, c);
        let conflict = r.conflict.expect("distinct(a,b,c) contradicts a=c");
        assert_eq!(conflict.diseq_lit, Some(9));
    }
}
