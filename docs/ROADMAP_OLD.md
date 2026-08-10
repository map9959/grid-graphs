# Phase Roadmap for the Full-Degree Spanning Tree Problem on Grid Graphs

## Problem

The **grid graph** `G(m, n)` has `m × n` vertices arranged in a rectangular
grid; each vertex is adjacent to the (up to four) vertices immediately above,
below, left, and right of it. A **spanning tree** `T` of `G(m, n)` is a
connected acyclic subgraph that contains every vertex. A vertex `v` is
**full-degree in `T`** if `deg_T(v) = deg_G(v)` — equivalently, every grid
edge incident to `v` is retained in `T`.

This project analyzes
> `P(m, n)` := max over spanning trees `T` of the count of full-degree
> vertices.

Both empirical (Rust DP, exhaustive on small grids) and formal (Lean 4 +
mathlib bound expressions) machinery are in this repo. See
`docs/DERIVATION.md` for the original problem write-up and motivation.

## Repository navigation

| Path | Purpose |
|------|---------|
| `src/main.rs`, `src/analysis.rs`, `src/witness.rs` | Rust DP solver, bound expressions, witness-tree extractor |
| `data/extended.csv`, `data/extended_long.csv` | DP-computed `P(m, n)` for `m ≤ 8`, `n ≤ 35` |
| `analysis/recurrences.md` | Per-`m` first-difference cycles, periods, exact `α_m` |
| `analysis/conjectures.md` | Closed-form formulas for `P(m, n)`, m ≤ 8 |
| `analysis/oeis.md` | OEIS hits and prior-art notes |
| `analysis/proofs_m345.md` | Per-`m` constructive lower bounds with checker |
| `analysis/proofs_upper.md` | Phase 4 matching upper bounds (Karp + witness-period methods) |
| `analysis/proofs_diagonal.md`, `analysis/PHASE_PATTERN.md` | Diagonal proof program and exact residue-zero phase family |
| `analysis/diagonal_patterns.py`, `analysis/check_diagonal_patterns.py` | Parametric diagonal constructions and independent checker |
| `analysis/check_constructions.py` | Independent verifier of explicit spanning trees |
| `analysis/extract_patterns.py` | Phase 4 helper: decode per-column edge patterns from a witness |
| `analysis/render_witness.py`, `analysis/motif_search.py` | Motif inspection scratchpads |
| `src/transfer.rs`, `src/transfer_util.rs` | Phase 4 column-state transfer matrix + Karp's max-mean cycle |
| `src/motif.rs` | Phase 4 witness gain-sequence period detection and ASCII visualizer |
| `lean/GridGraphs/Defs.lean`, `lean/GridGraphs/Bounds.lean`, `lean/GridGraphs/Forced.lean`, `lean/GridGraphs/ForestExtension.lean` | Lean definitions, bounds, forced edges, and forest-to-tree completion |
| `lean/STATUS.md`, `lean/EVIDENCE.md` | Lean-side status and lemma index |

## Status

| Phase | Title | Status | Reference |
|-------|-------|--------|-----------|
| 1 | Per-`m` closed-form conjectures | **Done** | `analysis/recurrences.md`, `analysis/conjectures.md` |
| 2 | OEIS / prior-art lookup | **Done** | `analysis/oeis.md` |
| 3 | DP backtracking → motif extraction (constructive LBs) | **Done (mostly)** | `analysis/proofs_m345.md`, `src/witness.rs` |
| 4 | Matching upper bounds via Karp's max-mean cycle | **Done for m ≤ 6 rigorously, m ≤ 10 empirically** | `analysis/proofs_upper.md`, `src/transfer.rs`, `src/motif.rs` |
| 5 | Conjecture A as a theorem (`α_m = (m+2)/3 ⇔ m ≡ 1 mod 3`) | Pending — **recommended next** | — |
| 6 | Per-m closed forms for `m ≡ 0, 2 (mod 3)` | Pending | — |
| 7 | Diagonal `P(n, n)`: prove the revised piecewise formula | **In progress**; exact bases and substantial upper-bound infrastructure are formalized, while the global planar realization and stable residue-two lower family remain open | `analysis/proofs_diagonal.md`, `lean/STATUS.md`, current roadmap below |
| 8 | Lean formalization of `P(m, n) ≤ basicUB m n` | **Done** | `lean/GridGraphs/Spanning.lean` (`preserved_le_basicUB`) |
| 9 | Lean formalization of per-`m` constructions and Conjecture A | Pending (multi-month) | — |

## Current diagonal critical path (authoritative)

This section supersedes the older recurrence-first execution order later in
Phase 7. The current strategy is to prove matching **absolute upper and lower
bounds** first, derive the exact diagonal formula directly, and only then
derive `DiagonalRecurrence` as a corollary.

```text
planar upper bounds + explicit lower constructions
  -> exact diagonal formula
  -> DiagonalRecurrence
```

This avoids making the unfinished crop-equality phase classification and
arbitrary-maximizer reverse frames prerequisites for the formula.

### Execution plan

| Step | Work | Deliverable | Completion gate |
|---:|---|---|---|
| 1 | Consolidate the planar realization interface | A `GridChannelContourRealization` combining a pruned channel forest, canonical demands, split-outer exits, merger slots, and carrier roots | The structure carries geometric data rather than assuming an embedding into the final combined resource |
| 2 | Construct canonical pruned channels | Realize the `n+3` row/column and corner germs as leaves or exits of an actual pruned channel forest | The demand map is injective and the parent relation follows genuine immediate channel continuation |
| 3 | Prove joint merger/root accounting | Embed `MergerSlot ⊕ roots` into `internalEdgeFinset T U ⊕ components(grid[F])` | All `k-1` merger multiplicities are retained and component terminals are globally unique |
| 4 | Prove the universal planar waste bound | `square_grid_tree_universalWaste : n + 2 ≤ incidenceWaste (...)` | The theorem holds for every square-grid spanning tree with no realization hypothesis |
| 5 | Exclude tight residue-two waste | Prove `ResidueTwoExactWasteExcluded`, equivalently nonexistence of the tight acyclic support profile | For `n=3k+2`, `W ≠ n+2` |
| 6 | Exclude stable near-tight waste | Prove `StableResidueTwoNearWasteExcluded`, equivalently nonexistence of the stable near profile | For `k≥5`, `W ≠ n+5` |
| 7 | Derive the complete absolute upper formula | `maxPreserved n n ≤ diagonalFormulaP n` by residue classes | Includes `P(17)≤110` without a separate crop-equality classification |
| 8 | Package existing lower constructions | One theorem covering residue zero, residue one, and finite residue-two widths through `n=20` | Only stable residue-two widths `n≥23` remain |
| 9 | Build a new stable residue-two family | Explicit family of score `3k²+7k` for every `k≥7`, with symbolic forced acyclicity or connected U-U dual | The candidate passes all local-cell, separator, and global incidence-forest gates before Lean implementation |
| 10 | Prove the complete absolute lower formula | `diagonalFormulaP n ≤ maxPreserved n n` | Covers every `n≥3` |
| 11 | Prove the unconditional formula directly | `maxPreserved_eq_diagonalFormulaP_unconditional` | Combine Steps 7 and 10 by antisymmetry |
| 12 | Derive the recurrence afterward | `diagonalRecurrence_proved : DiagonalRecurrence` from the exact formula and formula arithmetic | No crop equality phases or arbitrary-maximizer reverse frames are required |
| 13 | Final verification | Full Lean build, `git diff --check`, and prohibited-token scan | No assumptions, solvers, exhaustive scripts, or computational proof shortcuts |

### Current completion table

The previous two-sided surgery plan delivered useful infrastructure, but it is
not itself the current critical path to the formula.

| Area | Status | Formal result or remaining gate |
|---|---|---|
| Public tooth-cut certificate | Mostly complete | Defect-sized owner-labelled terminals, physical tooth endpoints, exact endpoint coverage, forced endpoints, bounded deletion, and insertion validity are public; root paths remain private |
| Grid specialization | Complete | Rectangular grids are triangle-free; a genuine owner can be inserted after at most three non-neighbor deletions |
| Sequential delete/add surgery | Complete | Dependent traces preserve acyclicity and have exact telescoping cardinality |
| Trace normalization and crop ledger | Complete | Final state is normalized to `(C \ D) ∪ R`; exact delete/add frame-loss wrappers are proved |
| Shared deletion accounting | Complete as an identity | Endpoint-fiber excess is exactly the deletion saving; no theorem yet forces enough cross-owner endpoint collisions |
| Sixteen crops | Partial | All sixteen crops, exact survival/frame-loss incidence sums, selection, and conditional recurrence interfaces exist; full adjacent-offset transfer geometry is absent |
| Crop discharge and aggregate surplus | Open | No proof of `Σ_Q (|R_Q|-|D_Q|) ≥ Σ_Q (ℓ_Q-2n)_+` |
| Exact bases | Complete | `P(3)=4`, `P(4)=8`, and `P(5)=11` are unconditional Lean theorems |
| Planar pruning and resource adapters | Partial | Abstract channel-forest count, split outer ports, carrier roots, merger factorization, and conditional contour routing exist; the grid realization is missing |
| Universal waste | Open | Requires Steps 1-4 above |
| Residue-two upper exclusions | Open | Tight and stable near-profile nonexistence are reduced but not proved |
| Stable residue-two lower construction | Open | Exact constructions exist through `n=20`; no valid exact family from `n=23` onward is known |
| Exact formula and recurrence | Open | Arithmetic assembly is ready once upper and lower bounds close |

### Upper-bound track

The following modules already provide most of the target types and generic
accounting:

- `PlaneChannelForest.lean`
- `ChannelContourRouting.lean`
- `GridCotreeSplitOuter.lean`
- `GridShoreChannelForest.lean`
- `ChannelCarrierRoots.lean`
- `ChannelMergerResources.lean`
- `NoncrossingShoreChannels.lean`

The missing realization should package data of the following shape:

```lean
structure GridChannelContourRealization ... where
  Carrier : Type
  carrierFintype : Fintype Carrier
  carrierDecidableEq : DecidableEq Carrier

  channels : PlaneChannelForest Carrier

  demandEmbedding :
    CanonicalShoreDemand axis n ↪ channels.demand

  exitEmbedding :
    channels.exits ↪ GridCotreeOuterPort T

  separator :
    channels.forest.MergerSlot →
      GridDirectionalDart.RootedChannelMerger root

  separatorInjective : ...

  rootContact : channels.forest.roots → CotreeFreeSet T
  carrierPruned : channels.forest.CarrierPruned rootContact

  terminalDisjointness : ...
```

The important endpoint is an unconditional existence theorem:

```lean
theorem exists_gridChannelContourRealization
    (hn : 3 ≤ n)
    (hT : IsSpanningSubtree (gridGraph n n) T) :
    Nonempty (GridChannelContourRealization hT)
```

#### Demand construction

Use tagged external germs:

- one left-side germ for each row, or top-side germ for each column;
- three distinct clockwise corner germs;
- actual channel states following cotree/contour continuation;
- private source germs removed only after their first geometric event is
  classified.

The construction must prove:

- sources are distinct;
- every source is a leaf or an immediate split-outer exit;
- common suffixes merge rather than being duplicated;
- unary continuation states are pruned;
- no parent is selected by arbitrary strict-supershore choice.

#### Merger and terminal accounting

At every `k`-way merger, retain exactly `k-1` slots. Each slot must receive a
distinct rooted separator dart and then either an internal `U-U` tree edge or a
preserved-component terminal. Roots and noninternal merger terminals must be
charged jointly so that one preserved component is never used twice.

Once this is realized, `ChannelContourRouting` already supplies

```text
n + 3 ≤ W + 1,
W ≥ n + 2.
```

#### Residue-two exclusions

The reductions are already formalized:

- `ResidueTwoTightAttachmentContradiction` is equivalent to nonexistence of an
  acyclic support of cardinality `6k²+5k+2`.
- `StableResidueTwoPersistentAttachmentDebt` is equivalent to nonexistence of
  the stable near profile of cardinality `6k²+5k+3`.

The preferred proof is a phase-refined channel realization. Tight residue-two
channels must not use exactly `n+3` resources, and stable channels must not use
exactly `n+6`. Component identity and checkerboard phase must survive pruning
so that the extra phase debt becomes a genuine extra merger, exit, or carrier
resource.

Do not resume scalar component or boundary potentials: the exact component
ledgers show that these only re-express cardinality.

### Lower-bound track

| Residue | Current lower coverage |
|---|---|
| `n=3k` | Finite bases plus the uniform symbolic residue-zero construction for large `k` |
| `n=3k+1` | Uniform symbolic residue-one construction |
| `n=3k+2`, `k≤6` | Explicit constructions through `n=20` |
| `n=3k+2`, `k≥7` | Missing |

Therefore the only missing lower family is stable residue two from `n=23`
onward.

Before another candidate is formalized, it must pass these proof gates:

1. No cell contains three forced vertices.
2. No cell contains diagonally opposite forced vertices.
3. Every induced forced component is a straight interval.
4. Every interval-star is a tree.
5. The global incidence graph of interval-stars is a forest.
6. Every successor adds exactly `6k+10` forced vertices.
7. The successor interface is stable under `k → k+1`.
8. No bounded dual face is isolated.
9. No nontrivial symbolic face set has empty dual boundary.
10. A uniform acyclicity or dual-connectivity proof exists before Lean coding.

A useful next abstraction is a comb-gluing theorem: a union of straight
interval-star trees is acyclic when their physical intersections are uniquely
owned and their incidence multigraph is a forest. The construction problem can
then be posed as finding a periodic interval family of cardinality
`3k²+7k` with a tree-shaped incidence graph.

### Formula-first assembly

Once the two absolute bounds are proved:

```lean
theorem maxPreserved_eq_diagonalFormulaP_unconditional
    (n : Nat) (hn : 3 ≤ n) :
    maxPreserved n n = diagonalFormulaP n :=
  Nat.le_antisymm
    (maxPreserved_le_diagonalFormulaP n hn)
    (diagonalFormulaP_le_maxPreserved n hn)
```

Then expose the currently private formula recurrence and derive:

```lean
theorem diagonalRecurrence_proved : DiagonalRecurrence where
  three := maxPreserved_three_three
  four := maxPreserved_four_four
  five := maxPreserved_five_five
  step := by
    intro n hn
    rw [maxPreserved_eq_diagonalFormulaP_unconditional n (by omega)]
    rw [maxPreserved_eq_diagonalFormulaP_unconditional (n - 3) (by omega)]
    exact diagonalFormulaP_recurrence n hn
```

### Proven state to preserve

- `maxPreserved_eq_maxForcedAcyclic`
- Exact crop signatures and labelled quotient admissibility
- Public tooth-cut certificates and bounded grid deletions
- Sequential tooth surgery and final-state normalization
- Exact endpoint-fiber sharing accounting
- Sixteen-crop indexing and incidence sums
- Conditional sixteen-crop upper interface
- Abstract channel-forest pruning
- Split outer ports and boundary-sector equivalence
- Merger/internal-or-component factorization
- Carrier-pruned root embeddings
- Exact bases `P(3)=4`, `P(4)=8`, `P(5)=11`
- Residue-one reverse-frame and construction bounds
- Finite residue-two construction scores through `n=20`
- Full Lean build currently passes without `sorry`

### Disproved routes: do not repeat

| Candidate | Exact failure |
|---|---|
| Monotone Four-Crop unit-resource charging | One owner may have three independent cycle defects |
| Abstract branch slots as deletion capacity | De-forcing an interior forced branch vertex need not remove forced-forced edges |
| Raw exact residue-two pump | The `n=23` successor has an isolated dual face |
| Existing seam-balanced repair | It creates a persistent two-face cut |
| Cap-balanced repair | It creates two isolated top faces for every positive pump depth |
| Full-row stripe bridges | The first bridge creates an immediate forced unit-cell cycle |
| Residue-zero `(N-1)²` crop | Every corner crop loses far too many forced vertices |
| Monotone residue-one one-frame extension | Its sharp maximum gain is `k+2`, below the required `2k` |
| Two persistent boundary caps plus row combs | The interval-star incidence graph contains `K_{2,k+1}` cycles |

### Priority after context compaction

1. Define `GridChannelContourRealization`.
2. Prove its unconditional existence.
3. Derive the universal waste bound.
4. Prove the two residue-two profile exclusions.
5. Finish the absolute upper formula.
6. Design and prove a new stable residue-two interval/incidence-tree family.
7. Finish the absolute lower formula.
8. Prove the exact formula directly.
9. Derive `DiagonalRecurrence` as a corollary.

## What Phase 3 actually delivered

In the **n ≥ m** asymptotic regime, with constructions verified by an
independent checker (numbers in *italics* updated by Phase 4):

| m | construction | optimal in n ≥ m regime |
|---|--------------|------------------------|
| 1 | `tree_m1` (path) | 49/49 |
| 2 | `tree_m2` (ladder) | 49/49 |
| 3 | `tree_m3_witness` (period 3) | 48/48 |
| 4 | `tree_m4_double_spine` (period 1) | 47/47 |
| 5 | `tree_m5_witness` (three-spine + period-3 hybrid) | *46/46 (Phase 4)* |
| 6 | `tree_m6_witness` (period 4) | 11/11 — only `n ≡ 0 (mod 4)` implemented |
| 7 | `tree_m7_witness` (period 1) | 24/24 |
| 8 | `tree_m8_witness` (period-7 hybrid, n ∈ {20, 34, 48}) | *3/3 (Phase 4)* |

After Phase 4, m ∈ {1, 2, 3, 4, 5, 7} have full-residue constructive LBs
matching the conjectured `P(m, n)`. For m = 6, only `n ≡ 0 (mod 4)` is
implemented (other residues mechanically extractable but tedious). For
m = 8, the period-7 motif is now explicit at `n − 20 ∈ 14ℤ_{≥0}` (a
1-in-14 residue subset of `n ≥ 20`).

## Strategic re-plan after Phase 4

Phase 4 produced enough new evidence to substantially revise what
"closing in on the closed formula" looks like. Three findings drive the
revision:

1. **Conjecture A is now confirmed at four data points** (m ∈ {1, 4, 7, 10}
   tight, m ∈ {2, 3, 5, 6, 8, 9} not tight). It is the strongest empirical
   regularity we have, and proving it would yield the first **theorem of
   the form `α_m as a function of m`**, valid for an infinite family.

2. **The original diagonal formula is false in residue two.** The original
   Conjecture C in `analysis/conjectures.md` was:
   ```
   P(n, n) = ⌊n²/3⌋ + n + C(n mod 3),  n ≥ 4,
   ```
    It is verified exactly at every `n = 4..15`, but an exact frontier
    computation proves `P(17,17)=110`, one below its prediction. The revised
    residue-two candidate is `P(3k+2,3k+2)=3k^2+7k` for `k>=5`, with the old
    value `3k^2+7k+1` retained only for `1<=k<=4`. Explicit matching
    constructions are available for every `n ≡ 1 (mod 3)`, every
    `n ≡ 0 (mod 3)`, and residue-two `n=17,20`; no target-count `n=23`
    construction is known. The asymptotic density is still expected to be
   `lim P(n,n)/n² = 1/3` — i.e. the basic UB **is** asymptotically tight
   on the diagonal, contradicting the previous "α-on-the-diagonal ≈ 0.42"
    reading. Residue two and the universal induced-edge decycling lower bound
    remain open.

3. **The bitpacked DP scales further than thought**: P(11,11)=49 in
   ~1.5 min, P(12,12)=58 in ~9 min, P(13,13) needs ~hour budget. So
   "Phase 5a" (a better square solver) was over-estimated as
   "weeks-of-work" — careful tuning may unlock n = 14, 15 within the
   existing solver, or a moderate rewrite (e.g. parallelization, better
   pruning, or a strip-DP) could push to n ≥ 20.

Current work can proceed in parallel: prove Conjecture A (Phase 5), continue
the harder per-m families (Phase 6), and finish the now-advanced diagonal proof
(Phase 7). Lean formalization is already active rather than a final-only phase.

## Phase 4 — transfer matrix + Karp's max-mean cycle (DONE)

Two complementary methods were implemented:

1. **Karp's max-mean cycle on the column-state transfer graph**
   (`src/transfer.rs`): rigorous, but feasible only for `m ≤ 6` due to
   state-space size (m=7 has 32 957 states / 39 M edges and exceeds the
   Karp time/memory budget; m=8 was not enumerated).
2. **Witness-DP gain-sequence period detection** (`src/motif.rs`):
   strong empirical evidence by extracting per-column full-degree counts
   from an optimal witness and detecting periodicity. Scales to `m ≤ 10`.

Where both apply (m ∈ {3, 4, 5, 6}) they agree exactly. See
`analysis/proofs_upper.md` for the full per-`m` table.

### Outcomes

| m | basic UB α | Phase 4 α | gap closed |
|---|-----------:|----------:|:-----------|
| 3 | 5/3 | 4/3 | ✓ rigorously (Karp) |
| 4 | 2 | 2 | already tight |
| 5 | 7/3 | 2 | ✓ rigorously (Karp); construction now closes the n ≡ 1 (mod 3) residue |
| 6 | 8/3 | 5/2 | ✓ rigorously (Karp) |
| 7 | 3 | 3 | already tight |
| 8 | 10/3 | 22/7 | ✓ empirically (witness-period); construction at n ∈ {20, 34, 48} |

Construction coverage now matches the conjectured `P(m, n)` exactly for
m ∈ {1, 2, 3, 4, 5, 7} on **all** n ≥ m, and for m = 6 (n ≡ 0 mod 4)
and m = 8 (specific n) where checked.

### Open items deferred from Phase 4

- Karp on m = 7, 8: need Howard's policy iteration or another
  memory-friendly max-mean cycle algorithm. The Howard's draft in this
  branch had a correctness bug and was reverted.
- m = 6 residues n mod 4 ∈ {1, 2, 3}: mechanical boundary derivation
  per residue, not yet encoded in `check_constructions.py`.
- m = 8 general n: only n − 20 ∈ 14ℤ_{≥0} implemented.

## Phase 5 — Conjecture A as a theorem (`α_m = (m+2)/3 ⇔ m ≡ 1 mod 3`)

**Goal**: Promote Conjecture A (in `analysis/conjectures.md`) from
"empirically observed at m ∈ {1, 4, 7, 10}" to a fully proven theorem
for the infinite family `m = 3k + 1, k ≥ 0`. This produces the first
non-trivial closed-form formula for `α_m` valid for an entire residue
class.

**Why this next**: Conjecture A is the structural heart of the data.
All other per-m phenomena hinge on whether m sits on the "tight" or
"non-tight" branch. A proof here unlocks compact closed forms for the
m ≡ 1 (mod 3) infinite family and clarifies what's special about the
other two residues.

### What's needed

The basic UB `α_m ≤ (m+2)/3` is **already algebraically proved** in
`lean/GridGraphs/Bounds.lean` (modulo the operational connection
deferred to Phase 8). So we need only the **matching lower bound**:
an explicit periodic-period-1 column motif, valid for every
m ≡ 1 (mod 3), achieving gain `(m+2)/3 = k + 1` per column for
m = 3k + 1.

### Subtasks

1. **5.1** Decode `tree_m4_double_spine`, `tree_m7_witness`, and the
   m = 10 witness gain-period-1 motif (extracted by
   `cargo run -- motif 10 25`) into a uniform parametric column
   pattern. The m = 4 and m = 7 patterns are already encoded; m = 10
   must be added to `analysis/check_constructions.py`.
2. **5.2** State the parametric pattern in m = 3k + 1: a single column
   pattern parameterized by k that, when repeated, yields gain k + 1
   per column. Verify it for k = 0, 1, 2, 3 (m = 1, 4, 7, 10) using
   the existing checker.
3. **5.3** Prove that the parametric pattern is a valid spanning tree
   for arbitrary k. The verification must address (i) edge count
   m·n − 1, (ii) acyclicity, (iii) connectedness, (iv) the per-column
   gain identity. The proof is purely combinatorial and amenable to
   either pen-and-paper exposition (`analysis/proofs_5.md`) or Lean
   formalization (deferred to Phase 9).
4. **5.4** Conjecture B (period q_m = 1 ⇔ m ≡ 1 mod 3) follows from
   5.3 since the construction is itself period 1, so q_m ≤ 1; combined
   with the basic UB tightness, Conjecture B is also implied.
5. **5.5** Test predictions at m = 13, 16 via the witness-DP
   gain-period detector (no new solver needed; current DP scales to
   m ≤ 12 squarewise but to m ≤ 16 if n is small).

**Effort**: weeks. The big question is whether step 5.3 yields a
clean inductive structure on k (likely yes given the period-1
behavior).

## Phase 6 — Per-m closed forms for `m ≡ 0, 2 (mod 3)`

For m ≡ 0 (mod 3), data shows q_m = 2, 2 for m = 6, 9 and q_3 = 3.
For m ≡ 2 (mod 3), q_m = 1, 3, 7 for m = 2, 5, 8 (no simple pattern).
**Goal**: characterize α_m, q_m as functions of m for m ≡ 0 and m ≡ 2
(mod 3), at least for the m ≤ 12 range where DP is feasible.

### Subtasks

1. **6.1** Compute `α_m, q_m` rigorously for m ∈ {7, 8, 9, 11, 12} via
   either:
   - a fast max-mean cycle implementation that handles m = 7, 8
     state spaces (Howard's done correctly, or value iteration
     with sparse adjacency), or
   - the witness gain-period method extended to m = 11, 12 (cheap;
     probably already gives correct answers).
2. **6.2** Look for a uniform construction for m ≡ 0 (mod 3):
   m = 3, 6, 9 with α = 4/3, 5/2, 7/2. Hypothesize a parametric
   period-2 motif that scales with m and verify.
3. **6.3** For m ≡ 2 (mod 3), the pattern is more erratic
   (α_2 = 1, α_5 = 2, α_8 = 22/7). Establish whether α_11, α_14 follow
   a pattern, or whether each m ≡ 2 (mod 3) requires its own ad-hoc
   construction.
4. **6.4** Update `analysis/check_constructions.py` with the new
   parametric constructions; close the m = 6 (n%4 ∈ {1, 2, 3}) and
   m = 8 (general n) gaps that Phase 4 left open.
5. **6.5** Document in `analysis/proofs_5_6.md` (or extend
   `analysis/proofs_upper.md`).

**Effort**: weeks to months. The m ≡ 2 (mod 3) case may not admit a
uniform formula, in which case Phase 6 succeeds on m ≡ 0 and partially
on m ≡ 2.

## Phase 7 — Diagonal `P(n, n)`: prove the revised formula

> **Historical detail.** This section records the evolution of Phase 7 and
> remains useful for references and negative results. Its older execution
> orders are superseded by **Current diagonal critical path (authoritative)**
> near the top of this document.

The original Conjecture C is disproved at `n=17`. The authoritative
residue-two candidate is now

```text
P(3k+2,3k+2) = 3k²+7k+1,  1 <= k <= 4,
P(3k+2,3k+2) = 3k²+7k,    k >= 5.
```

For `k>=5`, this is equivalent to a minimum non-full set

```text
q_plus(k) = |U| = 6k²+5k+4.
```

The old target `q_old(k)=6k²+5k+3` remains useful only as an intermediate
universal bound whose equality must be excluded.

| n | k | revised target `|U|` | status |
|---:|---:|---:|---|
| 17 | 5 | 179 | globally exact; two exact searches exclude 178 |
| 20 | 6 | 250 | valid construction; 249 not globally excluded |
| 23 | 7 | 333 | no construction and no matching upper bound |
| 26+ | 8+ | `6k²+5k+4` | both directions open |

The proof has two independent infinite-family obligations. The construction
track must produce target-count connected duals for every `k>=5`. The universal
track must prove every admissible `U` has at least `q_plus(k)` vertices. Neither
track can be replaced by larger exact square searches on laptop hardware.

### Sub-phases

#### 7a — Safer/faster solver to push the empirical horizon

**Current status: enough data. Stop pushing n for now.** Exact diagonal data
now reaches n = 15 and supports Conjecture C. Since the forced-edge witness
method still grows exponentially, running n = 16, 17, ... is no longer the
highest-value next step. The proof effort should now focus on the structural
decycling theorem in `analysis/proofs_diagonal.md`.

Current solver: P(11, 11) ~ 1.5 min, P(12, 12) ~ 9 min, P(13, 13)
> 30 min. A previous 14x14 attempt can exhaust laptop memory if run
with full parallel expansion. To test Conjecture C at
`n ∈ {13, 14, 15, 16}` we need solver modes that scale safely to those
sizes. Options, in increasing depth of work:
1. **Laptop-safe exact/target search**. Use `LOWMEM=1` to force
   streaming layer expansion and target search for larger unresolved
   prediction as a feasibility target. `TARGET` uses only conservative
   remaining-vertex pruning; `PRUNE=1` remains a heuristic accelerator and
   should not be used for certification. A reached target gives a
   construction at that value; a missed target is not by itself the exact
   optimum unless paired with a complete upper-bound argument.
2. **Beam search with bounded memory**. The current DP has a `BEAM=N`
   env var; tune to find a beam that recovers the true optimum on n ≤ 12
   and apply to n = 13, 14. Result is a **lower bound only** (beam may
   miss the true optimum). Bounded-beam runs at n = 14 were stable at 76,
   but a later forced-edge witness completed the conjectured value 77.
   The n = 15 beam lower bound was 87, but forced-edge witness completion
   later certified the conjectured value 88.
3. **Forced-edge upper-bound DP**. `fullub M N` computes the maximum
   cardinality of a vertex set whose forced-edge graph is acyclic, a
   rigorous upper bound formalized in Lean (`GridGraphs.Forced`). It gives
   `fullub 14 14 = 77` and `fullub 15 15 = 88`. Streaming
   `fullub-witness` completed both upper-bound sets to spanning trees,
   proving `P(14,14)=77` and `P(15,15)=88`.
4. **Better pruning**. The current `PRUNE=1` heuristic uses
   degree-budget potential. A 2D potential (using the 4-cycle hitting
   set bound on remaining vertices) could prune harder. A target-safe
   degree/deficiency-capacity pruning pass was tested on 12x12 and 13x13;
   it only prunes in the final columns and does not materially reduce the
   plateau, so the next safe pruning attempt needs genuinely two-dimensional
   constraints rather than more one-dimensional degree packing. Days of work.
5. **Rewrite as ILP/SAT**. Model the spanning-tree constraint with
   acyclicity-by-arborescence and full-degree as a count target.
   OR-Tools / Gurobi can sometimes handle these efficiently. 1–2 weeks.
6. **Distributed bitpacked DP**. Partition the column-state space by
   high bits of the canonical labeling and run shards in parallel.
   1–2 weeks; useful for any large m, n.

**Recommended order**: do not extend the exact computational horizon. Exact
optimization above n=15 is explicitly out of scope. Finish the residue-zero
phase-connectivity proof, find the stateful residue-two defect, and prove the
full induced-edge decycling lower bound.

#### 7b — Constructive matching lower bound for the diagonal formula

See `analysis/proofs_diagonal.md` for the current reduction. The diagonal
problem is now split into a forced-edge/decycling upper bound and explicit
residue-specific constructions for the non-full set `U`. The local `2x2` cell-hitting
condition has been formalized in Lean but is computationally too weak, so the
proof must use the full forest/decycling condition.

Current constructive status:

1. **7b.1 — residue one complete.** `residue_one_pattern(3k+1)` is an
   explicit exact family, checked through n=120 in the combined regression
   sweep. Its count and forced-forest structure are understood.
2. **7b.2 — residue zero family found.** Cached exact witnesses cover
   n=6,9,12,15,18,21. For every `n=3k>=21`,
   `residue_zero_phase_pattern(n)` gives the exact conjectured count. It
   reproduces the cached n=21 witness exactly and passes construction checks
   through n=120, with a separate stress check at n=300.
3. **7b.3 — residue-zero proof scaffold.** Ordinary rows `R_a`, seam rows
   `S_a`, and the recurrence
   `B_(k+1) = R_(k-2) S_(k-2) B_k R_k` give the cardinality identity
   `|U|=6k²-3k+2`. The U-U dual has the predicted unicyclic edge count.
   Connectivity reduces to a finite `B_7` frontier certificate and six local
   extension transitions; see `analysis/PHASE_PATTERN.md`.
4. **7b.4 — residue-two target construction.** Exact searches and a connected
   179-U witness prove `P(17,17)=110`. A separate connected 250-U unicyclic
   witness gives `P(20,20)>=150`. The affine pump is symbolically certified but
   has `|U|=6k²+6k-1`, one additional surplus per pump, so it is not the target
   family. The construction obligations are:
   - register canonical `n=17` and `n=20` bases with independent replay;
   - find a 333-U `n=23` witness or a direct symbolic target-cost transition;
   - determine the finite control graph linking the A17, B20, and later states;
   - prove every transition adds exactly `12k+11` U vertices and preserves the
     rooted dual topology;
   - prove cap closure and hence generate every `k>=5`.

   Visible frontier masks and partitions are insufficient because hidden
   slab-only components are common. A viable construction state must retain
   ordered ports, hidden attachments, OUT rooting, rank/cycle data, affine cost,
   and cap phase. Larger undifferentiated products are not the next step: the
   B20 exact product already grows from 21,365 to 1,701,918 states in one row.
   Detailed negative scopes and heuristic evidence remain in
   `analysis/AFFINE_RESIDUE2.md`, `analysis/RESIDUE2_TERMINAL_B_STATE.md`, and
   `analysis/RESIDUE2_STATE_TRANSFER.md`.

Exact frontier optimization now covers n=16 and n=17. Checks at larger widths
remain explicit candidate construction and verification.

#### 7c — Matching upper bound for the diagonal

The upper-bound problem is now a standalone induced-edge decycling theorem.
For `U` = non-full vertices, `G(n,n) - E(G[U])` must be a forest. Equivalently
in planar-dual language, the dual edges corresponding to `U-U` primal edges
must connect all grid cells to the exterior face. The desired upper bound is a
minimum-size theorem for such `U`.

Residue two requires the following dependency-ordered obligations:

1. **7c.1 — normalize the reduction. Complete.** Lean theorem
   `gridDualCycleSeparation` proves that connectivity of the dual graph formed
   by `U-U` edges implies `G-E(G[U])` is a forest. The preserving-tree endpoint
   is `exists_isTree_preserving_compl_of_uuDual_connected_grid`.
2. **7c.2 — prove the old baseline.** Establish
   `|U|>=q_old(k)=6k²+5k+3` with a width-independent inequality, potential, or
   finite transition certificate covering every legal pattern.
3. **7c.3 — exclude equality.** Show that every hypothetical old-target path
   for `k>=5` accumulates an OUT attachment debt greater than its terminal merge
   capacity. Equivalently, derive a sharpened potential proving
   `|U|>=q_old(k)+1` directly.
4. **7c.4 — prove coverage.** The old contiguous packet-carrier claim is false:
   an exact optimal `n=11` path has a transient silent support gap. The primary
   replacement is an ordered annulus state. Known feasible witnesses through
   `n=20` have at most four repeated port components, three cyclic runs per
   component, and nine compressed runs. These constants are observations, not
   a theorem. Prove comparable uniform bounds, closure, and right-congruence.
5. **7c.5 — fallback coverage route.** If ordered annulus complexity is
   unbounded, use a hull-carrier grammar that permits silent packets and retains
   long-range rooted attachment identity. Do not develop both abstractions
   indefinitely; falsify annulus boundedness first.
6. **7c.6 — finite certificate.** Enumerate or symbolically prove every state
   transition, record cost/rank/cycle/debt deltas, solve the sharp min-plus
   potential, and emit an independently checkable certificate with initial and
   terminal conditions.
7. **7c.7 — finite bases.** Determine the control period before computing new
   exact bases. The exact `n=17` result may suffice for a one-state induction;
   `n=20`, `n=23`, or later bases are required only if the proved control graph
   has additional initial phases.
8. **7c.8 — theorem assembly and Lean.** State the revised piecewise theorem,
   separate global results from scoped and heuristic evidence, and formalize the
    stable argument only after the informal construction and upper bound close.

The old-baseline reduction now has two additional exact forms. For a dual
spanning tree, if `N_j` counts primal vertices incident with exactly `j` chosen
cotree edges, then `Q+S=2N_1+N_2`; the universal first step is
`2N_1+N_2>=n+2`. In the choice-free forced-forest form, with `F=V\U`,
`H=G-E(G[U])`, and component counts `c_F,c_H`,

```text
K(U)=Q_U+c_F+c_H-n-2.
```

Thus 7c.2 is exactly `Q_U+c_F+c_H>=n+7` in residue two. These identities are
proved and regression-checked in
`analysis/residue_two_obligation5_components.py`; the geometric component
inequality remains open. This is the preferred proof target before resuming a
larger annulus computation.

The row-language route has also been audited. The four-term expression
`-3U+row+2faces-2debt` is the exact negative accumulated curvature, not a
coercive potential: every transition has zero slack and a connected terminal
has value `-K`. It cannot prove terminal constant five without a separate
minimum-accepting-weight theorem. The new exact first-defect monitor finds no
one-hull codec defect at `n=5`; at `n=8`, first face-cut width two costs
curvature eight, three above the minimum. All codec-valid completable edges pass
a bounded streaming topology and local-counter certificate independent of
`advance_row`. Symbolic soundness is complete for admitted words;
arbitrary-word closure and arbitrary-width coverage remain open.

The first held-out width is exact as well: a two-channel `n=11` product finds
no face-cut defect at the 72-U curvature-five optimum, and finds the first
defect at 73 U, curvature eight. The three-unit first-defect gap therefore holds
completely at `n=8,11`, but remains unproved at arbitrary width.

The symbolic transition product now has a true width-independent component
bound: at most seven actual and seven expected components survive a packet cut.
Malformed row shapes and irreversible target-partition fan-out are rejected.
This closes the former unbounded-state bug, but arbitrary-word completeness is
not yet formalized.

Potential synthesis also has a sharper boundary. Repeatable negative packet
self-loops rule out scalar cut-state potentials. Exact `n=5,8` algebra rules out
atom sums, adjacent-bigram word weights, and the finite-parser state-only model;
the latter has an exact `-1>=0` Farkas certificate. The next proof must add
justified transition context or prove the component inequality directly, not
fit another cumulative accounting term.

The proposed post-defect merge-capacity proof is also closed negatively. Exact
`n=8,11` defect witnesses discharge every unit of current debt, so a second
carrier does not force a lost future merge. Any universal first-defect theorem
must charge prefix/creation curvature plus cap weight. Large incoming-history
products are paused after a memory-limit failure; finite-parser regeneration
now requires explicit `--allow-large-lp` opt-in.

The immediate upper-bound experiment is the annulus coverage lemma, not another
scalar strip inequality. Exact `n=5,8` scalar-optimum censuses already show why:
edge-maximizing states waste rank in cycles and sealed components, while
rank-maximizing states remain disconnected. Ordered attachment topology is the
missing channel; see `analysis/concentric_connectivity_profile.json` and
`analysis/concentric_layer_rank_census.json`.

Current coverage progress is exact but finite. Complete equality censuses cover
all 242 optimum `n=5` patterns and all 704 optimum `n=8` patterns with no
`4/3/9` port-signature violation. An exact product-frontier query also covers
the centered side-3 prefix of every connected 72-U `n=11` pattern and finds no
violation after 78,285,124 transitions.

The streaming monitor and exact backward threshold minimization now complete
centered side 5 as well, with no violation, 96,819,952 transitions, and about
274 MiB peak RSS. Side 7 still exceeds the 6 GiB gate while constructing its
exact local language; `annulus_side7_threshold_automaton_shards.json` specifies
a collision-safe 256-way external repartition, but no side-7 result is claimed.
The affine A23 surplus control falsifies `4/3/9` as a general topological bound,
so the theorem target is now bounded reduced branch cost under curvature-five
extremality, not bounded raw port-word size.

The finite potential has also sharpened. A six-feature cap/merge state gives an
exact terminal-constant-five certificate on all 588 complete n5/n8 equality
transitions and is consistent with fixed n11/n14 and affine n17 paths. It does
not provide width coverage or the extra unit. At n17 the missing discriminator
is positive terminal unpayable debt for every 178-U survivor versus zero for the
179-U control. The next upper-bound obligation is to propagate that debt flag
through a covered low-curvature hull language.

Construction-side, all net-minus-two exchanges around the fixed connected
335-U n23 control are now exactly negative through order three: the order-three
census checks all 1,198,144 addition triples and all 15,057 admissible
five-removal tuples. A target witness must therefore change phase globally, not
be a low-order repair of that control. The exact packet charge algebra still
permits the desired `12k+11` recurrence: widen every mutable row by one
zero-charge packet and insert three rows of total charge three. Finding the
rooted-attachment schedule is the remaining construction problem.

The first focused realizations of that schedule have now been exhausted. Both
`A^5 H^3 A^15` and `A^8 H^3 A^12`, with independent radius-one moving seams and
all 65 bounded basic charge-one HOLD rows, remain two-component joins in both
consistent diagonal phases. Direct width-six P2/P5 compositions from A17 are
also exact negatives. The next construction language must add nonbasic phase
packets, radius-two rewrites at the missing attachment cut, mixed cap phases, or
a different control rather than another basic schedule product.

The first localized nonbasic enlargement is also exact negative. Full binary
three-cell packets and radius-two rewrites on the two missing-attachment rows,
with main, anti, and mixed bottom-cap phases, still leave all eight named
families at best profile `[2,1]`. Further construction work must move the
nonbasic phase across additional rows or change the cap/control itself.

The Lean planar bridge is complete. `gridCycleRowRayParity` proves odd-face
existence and parity preservation across every non-cycle edge using finite
row-ray counts. It yields unconditional `gridDualCycleSeparation`, induced-edge
decycling, and a preserving spanning tree from any connected U-U dual.

The side-7 external computation is resumable but incomplete. Exact phases 0
through 41 are committed only as ignored local workspace; phase 41 contains
134,474,412 records. No side-7 theorem or certificate is claimed until phases
42 through 49, backward minimization, and the global product all complete.

The generic completion step is no longer open. Lean theorem
`SimpleGraph.isAcyclic_extends_to_isTree` extends any forced forest inside a
finite connected graph, and
`exists_isTree_preserving_of_forcedEdgeGraph_isAcyclic` packages this as a
tree preserving every forced vertex.

**Historical execution order**: normalize the revised target and bases;
discover the target-cost residue-two construction control; prove the old
universal baseline; establish ordered-annulus coverage; prove the extra
attachment-debt unit; certify exactly the finite bases required by the
resulting control graph; then assemble and formalize the theorem. The current
formula-first order is given in the authoritative section above.

## Phase 8 — Lean formalization of `P(m, n) ≤ basicUB m n` ✅ **DONE**

Built in `lean/GridGraphs/Spanning.lean`. The headline theorem
`preserved_le_basicUB` states: for every spanning subtree `T` of
`gridGraph m n` (with `m, n ≥ 1`), `numPreserved m n T ≤ basicUB m n`.

### What was actually built

1. **8.1** ✅ `IsSpanningSubtree G T : T ≤ G ∧ T.IsTree`. Convenience
   accessors `.le`, `.isTree`, `.isAcyclic`, `.isConnected`.
2. **8.2** ✅ Tree edge count `IsSpanningSubtree.card_edgeFinset`
   (`#T.edgeFinset + 1 = |V|`) and degree sum
   `IsSpanningSubtree.sum_degrees` (`∑ v, T.degree v = 2(|V| − 1)`),
   from mathlib's `IsTree.card_edgeFinset` and
   `sum_degrees_eq_twice_card_edges`.
3. **8.3** ✅ `vertexDeficiency m n T v` (in `Defs.lean`),
   `numPreserved m n T` (filtered Finset count), `isPreserved`.
4. **8.4** ✅ `total_deficiency`: `∑ v, vertexDeficiency m n T v = D m n`.
5. **8.5** ✅ `vertexDeficiency_le_three` plus per-class refinements
   `vertexDeficiency_le_one_of_corner`, `vertexDeficiency_le_two_of_border`.
6. **8.6** ✅ `preserved_le_basicUB`: the headline theorem.
7. **8.7** ✅ `lean/STATUS.md`, `lean/EVIDENCE.md`, `lean/README.md`
   updated.

### Key insight enabling the proof

The grid graph was identified with the box product:
```
gridGraph m n = pathGraph m □ pathGraph n
```
(`gridGraph_eq_boxProd` in `Defs.lean`). This let us inherit connectivity
from `connected_boxProd` and `pathGraph_connected`, and the per-vertex
degree decomposition `(gridGraph m n).degree v = (pathGraph m).degree v.1
+ (pathGraph n).degree v.2` from `degree_boxProd`. The actual proof was
substantially shorter than originally estimated (~700 lines, ~1 day of
work) once this identification was found.

### Refined upper bound (sub-phase 8.refined)

`preserved_le_refinedUB` is **not** yet proved but the per-class deficiency
caps are all in place. The remaining work is the piecewise arithmetic for
`refinedUB`'s definition. Estimated effort: ~2–3 hours.

## Phase 9 — Lean formalization of constructions and Conjecture A (long-term)

Once Phase 5 produces the m = 3k + 1 parametric construction (with
informal proof) and Phase 8 the basic UB theorem, Lean can finally
state the **first proven theorem of the form**:

> ∀ k ≥ 0, ∃ asymptotic constant `α_{3k+1} = k + 1` such that
> `P(3k+1, n) = (k+1)·n + O_k(1)`.

Subsequent Lean goals (in order):
1. **9.1** Formalize the m = 3k + 1 construction as a Lean term and
   verify it (combinatorial induction on k).
2. **9.2** Combine with the Phase 8 basic UB theorem to prove the
   matching upper bound.
3. **9.3** State Conjecture A as a theorem and prove the "if" direction
   (the construction case). The "only if" direction (m ≢ 1 mod 3 ⇒
   strict gap) is harder and may need to wait for Phase 6 results.
4. **9.4** Per-m formalizations for m ∈ {3, 5, 6, 8} (the non-tight
   widths) — depends on Phase 6 producing clean per-m formulas.

**Effort**: indefinite, multi-month per item.

## Open problems

Aggregated from the various analysis files. A fresh agent picking up this
project should know about all of these:

### Resolved (Phase 4)

1. **m = 5 at n ≡ 1 (mod 3)**: ✓ — `tree_m5_period3_motif` uses the
   "fully preserved interior column" trick.
2. **m = 8 motif**: ✓ partially — `tree_m8_witness` encodes the
   period-7 motif at `n ∈ {20, 34, 48}`. Generalizing to all residues
   mod 7 is mechanical but not yet done.
3. **Matching upper bounds for m ∈ {3, 5, 6}**: ✓ — Karp's max-mean
   cycle delivers rigorous matching UBs. m = 8 matched empirically
   only (state space too large for current Karp implementation).

### Open

4. **Conjecture A**: Is α_m = (m+2)/3 ⇔ m ≡ 1 (mod 3) for all m? Empirically
   true at m ∈ {1, 4, 7, 10}. **Phase 5**.
5. **α_m for m ≡ 0, 2 (mod 3)**: We have data points but no formula.
   Phase 6.
6. **Revised diagonal closed form**: the original Conjecture C fails at
   `n=17`; the authoritative piecewise formula is stated in Phase 7. The exact
   bases `P(3)=4`, `P(4)=8`, and `P(5)=11` are formalized. Constructive
   families cover residues 0 and 1 and residue two through `n=20`; stable
   residue two and the matching universal upper bound remain open. **Phase 7**.
7. **m = 6 at n ≢ 0 (mod 4)**: not yet encoded; Phase 4 found the
   period-4 interior motif but residue-specific boundaries remain.
   Subset of Phase 6.
8. **m = 8 generalization**: only `n ∈ {20, 34, 48}` implemented.
   Subset of Phase 6.
9. **Diagonal planar counting in Lean**: forced-edge necessity, forest
   extension, preserving-tree completion, and the connected-U-U-dual to
   forced-acyclic bridge are formalized. The missing theorem is now the
   grid-specific pruned-channel realization needed to prove the universal
   `W≥n+2` resource inequality. **Phase 7c**.

## Verification quickstart

### Empirical data summary (post-Phase 4)

- Per-m closed-form conjectures verified up to n = 35 for m ∈ {6, 7, 8}
  (`data/extended_long.csv`).
- Diagonal sequence `P(n, n)` for `n = 1..12` (`data/diagonal.csv`):
  `1, 2, 4, 8, 11, 16, 22, 27, 34, 42, 49, 58`.
- Wide-m exploration `P(m, n)` for `m ∈ {9, 10, 11, 12}, n ≤ 30`
  (`data/wide_m.csv`).
- α_m confirmed for m = 9 (= 7/2) and m = 10 (= 4) via gain-period
  detection.

### Quickstart commands

A fresh agent should run these to confirm the current state:

```bash
# 1. Rust solver + analysis tests (11 tests including Phase 4 regressions)
cargo test --release
# Expected: "test result: ok. 11 passed; 0 failed"

# 2. Lean formal proofs (sorry-free)
cd lean && lake build && cd ..
# Expected: "Build completed successfully"

# 3. Construction checker (n ≥ m regime, m ∈ {1..8})
python3 analysis/check_constructions.py
# Expected (in summary, Phase 4 updated):
#   m=1 trivial path                                49      49
#   m=2 ladder                                      49      49
#   m=3 period-3 witness                            48      48
#   m=4 double-spine                                47      47
#   m=5 (three-spine + period-3 hybrid)             46      46   ← Phase 4 fixed n%3==1
#   m=6 period-4 witness (n%4==0 only)              11      11
#   m=7 period-1 witness                            24      24
#   m=8 period-7 witness (n in {20, 34, 48})         3       3   ← Phase 4 added

# 4. Diagonal parametric constructions, including residue-zero phase family
python3 analysis/check_diagonal_patterns.py 120
# Expected: every printed row has status True; includes n=21,24,...,120

# 5. Phase 4 alpha verification (m ≤ 6 in seconds; m=6 takes ~40 s)
cargo run --release -- alpha 5
# prints "alpha=2"  (matches recurrences.md)

# 6. (Optional) inspect the optimal tree and detect period
cargo run --release -- motif 8 35
# prints ASCII grid + "alpha = 22/7" via gain-sequence period

# 7. (Optional) regenerate the empirical data
CSV=1 cargo run --release -- compare 8 20 > data/extended.csv

# 8. (Optional) inspect the optimal tree at any (m, n)
cargo run --release -- witness 5 21
# prints "# m=5 n=21 value=43 transposed=false edges=104" + the edge list
```

If all four primary commands pass, the repo is in a good state. Any
discrepancy should be investigated before starting a new phase.

## Phase dependency notes

- Phase 4 (DONE) depended on Phase 3.
- Phase 5 (Conjecture A) builds on the Phase 3 / Phase 4 explicit
  constructions for m = 4, 7, 10; independent of Phases 6, 7.
- Phase 6 (per-m for m ≢ 1 mod 3) is independent of Phase 5 but
  benefits from a faster max-mean cycle algorithm (potentially shared
  with Phase 4 follow-up).
- Phase 7 (diagonal Conjecture C) is largely independent. Residue-zero and
  residue-one constructions are available; residue two and the universal
  counting theorem can proceed in parallel with Phases 5/6.
- Phase 8 (Lean basicUB) is independent of Phases 5, 6, 7 (it
  formalizes the basic UB which is already algebraically proved).
- Phase 9 (Lean formalization of constructions / Conjecture A) depends on
  Phase 5 for the construction. Phase 8's operational connection is complete;
  diagonal formalization additionally needs the Phase 7c planar-dual lemma.
