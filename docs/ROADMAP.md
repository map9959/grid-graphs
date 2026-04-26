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
| `analysis/check_constructions.py` | Independent verifier of explicit spanning trees |
| `analysis/extract_patterns.py` | Phase 4 helper: decode per-column edge patterns from a witness |
| `analysis/render_witness.py`, `analysis/motif_search.py` | Motif inspection scratchpads |
| `src/transfer.rs`, `src/transfer_util.rs` | Phase 4 column-state transfer matrix + Karp's max-mean cycle |
| `src/motif.rs` | Phase 4 witness gain-sequence period detection and ASCII visualizer |
| `lean/GridGraphs/Defs.lean`, `lean/GridGraphs/Bounds.lean` | Lean 4 + mathlib formalization (bound expressions, deficiency identity) |
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
| 7 | Diagonal `P(n, n)`: prove Conjecture C | Pending; exact data through n = 15 supports closed form | `analysis/conjectures.md`, `analysis/proofs_diagonal.md` |
| 8 | Lean formalization of `P(m, n) ≤ basicUB m n` | Pending | — |
| 9 | Lean formalization of per-`m` constructions and Conjecture A | Pending (multi-month) | — |

### What Phase 3 actually delivered

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

2. **The diagonal `P(n, n)` admits a clean closed form** (Conjecture C in
   `analysis/conjectures.md`):
   ```
   P(n, n) = ⌊n²/3⌋ + n + C(n mod 3),  n ≥ 4,
   ```
    verified at every `n = 4..14`. The asymptotic density is
   `lim P(n,n)/n² = 1/3` — i.e. the basic UB **is** asymptotically tight
   on the diagonal, contradicting the previous "α-on-the-diagonal ≈ 0.42"
   reading. Testing the conjecture at n ≥ 13 requires either a faster
   solver or a smarter analysis.

3. **The bitpacked DP scales further than thought**: P(11,11)=49 in
   ~1.5 min, P(12,12)=58 in ~9 min, P(13,13) needs ~hour budget. So
   "Phase 5a" (a better square solver) was over-estimated as
   "weeks-of-work" — careful tuning may unlock n = 14, 15 within the
   existing solver, or a moderate rewrite (e.g. parallelization, better
   pruning, or a strip-DP) could push to n ≥ 20.

The revised roadmap re-prioritizes accordingly: **first** prove
Conjecture A (Phase 5), **then** the harder per-m families and
diagonal closed form (Phases 6, 7), **finally** Lean formalization.

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

## Phase 7 — Diagonal `P(n, n)`: verify and prove Conjecture C

`analysis/conjectures.md`'s original **Conjecture C** is:
```
P(n, n) = ⌊n²/3⌋ + n + C(n mod 3),  n ≥ 4,
```
where `C(1) = -1, C(0) = C(2) = -2`. Verified exactly at every
n = 4..15. The n = 13, 14, and 15 values were certified by the
forced-edge upper-bound DP plus completed spanning-tree witnesses. The
next unresolved case is n = 16.

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

**Recommended order**: do not extend the computational horizon immediately.
Instead, decode the n = 13, 14, 15 non-full sets `U`, prove a parametric
period-3 construction, and prove the full induced-edge decycling lower bound.

#### 7b — Constructive matching lower bound for the diagonal formula

See `analysis/proofs_diagonal.md` for the current reduction. The diagonal
problem is now split into a forced-edge/decycling upper bound and an explicit
period-3 construction for the non-full set `U`. The local `2x2` cell-hitting
condition has been formalized in Lean but is computationally too weak, so the
proof must use the full forest/decycling condition.

The Phase 4 column motifs already give P(m, n) ≥ α_m·n + O(1) for
fixed m. For squares, we need a 2D construction whose density
approaches 1/3 with the correct linear correction.

Hypothesis: a **diagonally-tiled period-3 pattern**, where each 3×3
block is the m=3 period-3 motif rotated and tiled, achieves the
asymptotic density. Subtasks:
1. **7b.1** Build a candidate 3×3 (or 6×6) tile and verify density
   ≥ 1/3 by hand on small `n × n` grids.
2. **7b.2** Verify boundary effects yield the `+n + C` correction.
3. **7b.3** Check the construction against `data/diagonal.csv` at
   n ≤ 12.

#### 7c — Matching upper bound for diagonal

The upper-bound problem is now a standalone induced-edge decycling theorem.
For `U` = non-full vertices, `G(n,n) - E(G[U])` must be a forest. Equivalently
in planar-dual language, the dual edges corresponding to `U-U` primal edges
must connect all grid cells to the exterior face. The desired upper bound is a
minimum-size theorem for such `U`.

Subtasks:
1. **7c.1** Prove the planar-dual equivalence informally: `G - E(G[U])` is a
   forest iff the dual graph formed by `U-U` edges connects all faces.
2. **7c.2** Decode the n = 13, 14, 15 `U` witnesses into a period-3 strip
   pattern plus residue-specific boundary patches.
   The `n ≡ 1 (mod 3)` pattern is now explicit in
   `analysis/diagonal_patterns.py` and verified by dual connectivity for
   n = 4, 7, 10, 13, 16. The stronger checker
   `analysis/check_diagonal_patterns.py` verifies the same family through
   n = 40 by completing the forced forest to a spanning tree. The proof note
   now states this as Proposition L1 and isolates the generic forest-completion
   lemma needed to convert valid `U` patterns into spanning trees.
   Simple count-matching extensions for the other two residues were tested and
   rejected because their dual graphs are disconnected; see
   `analysis/proofs_diagonal.md`.
3. **7c.3** Prove a strip-counting lower bound for any `U` whose dual edges
   connect all faces. This is the core remaining combinatorial theorem.
4. **7c.4** Move the stable theorem into Lean after the informal proof is
   settled.

**Effort**: 7a is done for now. 7b/7c are the main work; expect weeks for the
informal construction/counting proof and substantially longer for Lean.

## Phase 8 — Lean formalization of `P(m, n) ≤ basicUB m n` (formerly Phase 6)

Build the operational layer in Lean to convert the empirical certification
of the basic upper bound into a machine-checked theorem.

**Effort**: 2–4 weeks.
**Yield**: the principal upper bound moves from "empirically true for
m, n ≤ 12" to "proven for all m, n".
**Risk**: mathlib's `SimpleGraph.IsAcyclic` and spanning-tree API may
need extension for the combinatorial sums; non-trivial library
contributions may be required.

### Subtasks

1. **8.1** Define `IsSpanningTree (T : SimpleGraph (GridVertex m n)) :
   Prop` capturing acyclicity + connectedness + spanning + subgraph of
   `gridGraph m n`.
2. **8.2** Define `vertexDeg T v : ℕ` and prove
   `∑ v, vertexDeg T v = 2 * (m * n − 1)` for any spanning tree.
3. **8.3** Define `numFullDegree T : ℕ` and `vertexDeficiency T v : ℕ`,
   plus the obvious lemma `numFullDegree T = card {v | vertexDeficiency T
   v = 0}`.
4. **8.4** Prove the global identity `∑ v, vertexDeficiency T v = D m n`
   (combines 8.2 with `Defs.lean::degSumGrid` and the proven
   `deficiency_closed_form`).
5. **8.5** Prove the per-vertex deficiency cap: for any non-full-degree
   vertex `v`, `vertexDeficiency T v ≤ deg_G v − 1` (i.e. ≤ 3, 2, 1 for
   interior, border, corner respectively).
6. **8.6** Conclude `P m n ≤ basicUB m n` via deficiency packing
   (combining 8.4, 8.5, and `ceilDiv3_mul_ge` already proved in
   `Bounds.lean`).
7. **8.7** Update `lean/STATUS.md`, `lean/EVIDENCE.md`, `lean/README.md`
   to reflect the theorem.

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
6. **Conjecture C** (diagonal closed form): `P(n, n) = ⌊n²/3⌋ + n + C(n%3)`
   for n ≥ 4. Verified exactly at n = 4..15; n = 16 is the next open
   case. **Phase 7**.
7. **m = 6 at n ≢ 0 (mod 4)**: not yet encoded; Phase 4 found the
   period-4 interior motif but residue-specific boundaries remain.
   Subset of Phase 6.
8. **m = 8 generalization**: only `n ∈ {20, 34, 48}` implemented.
   Subset of Phase 6.
9. **Lean operational connection**: `P(m, n) ≤ basicUB m n` is empirically
   true (`m, n ≤ 12` exhaustively verified) but not Lean-proved.
   **Phase 8**.

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

# 4. Phase 4 alpha verification (m ≤ 6 in seconds; m=6 takes ~40 s)
cargo run --release -- alpha 5
# prints "alpha=2"  (matches recurrences.md)

# 5. (Optional) inspect the optimal tree and detect period
cargo run --release -- motif 8 35
# prints ASCII grid + "alpha = 22/7" via gain-sequence period

# 6. (Optional) regenerate the empirical data
CSV=1 cargo run --release -- compare 8 20 > data/extended.csv

# 7. (Optional) inspect the optimal tree at any (m, n)
cargo run --release -- witness 5 21
# prints "# m=5 n=21 value=43 transposed=false edges=104" + the edge list
```

If all three primary commands pass, the repo is in a good state. Any
discrepancy should be investigated before starting a new phase.

## Phase dependency notes

- Phase 4 (DONE) depended on Phase 3.
- Phase 5 (Conjecture A) builds on the Phase 3 / Phase 4 explicit
  constructions for m = 4, 7, 10; independent of Phases 6, 7.
- Phase 6 (per-m for m ≢ 1 mod 3) is independent of Phase 5 but
  benefits from a faster max-mean cycle algorithm (potentially shared
  with Phase 4 follow-up).
- Phase 7 (diagonal Conjecture C) is largely independent. 7a can run
  in parallel with 5/6. 7b/7c may benefit from Phase 5 motifs as
  building blocks.
- Phase 8 (Lean basicUB) is independent of Phases 5, 6, 7 (it
  formalizes the basic UB which is already algebraically proved).
- Phase 9 (Lean formalization of constructions / Conjecture A) depends
  on Phase 5 (for the construction) and Phase 8 (for the operational
  connection).
