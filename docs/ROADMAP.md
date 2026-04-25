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
| 4 | Matching upper bounds via Karp's max-mean cycle | **Done for m ≤ 6 rigorously, m ≤ 8 empirically** | `analysis/proofs_upper.md`, `src/transfer.rs`, `src/motif.rs` |
| 5 | Square asymptotics (5a solver, 5b tile, 5c LP UB) | Pending — **recommended next** | — |
| 6 | Lean formalization of `P(m, n) ≤ basicUB m n` | Pending | — |
| 7 | Lean formalization of explicit constructions | Pending (multi-month) | — |

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

## Recommended next: Phase 5 — square asymptotics

Phase 4 established the asymptotic slope `α_m` rigorously for `m ≤ 6` via
Karp's max-mean cycle on the column-state transfer graph and empirically
(via witness gain-sequence period detection) for `m ≤ 8`. See
`analysis/proofs_upper.md` for the per-`m` table.

The natural next direction is **square asymptotics**: estimating
`lim P(n, n) / n²`. Basic UB caps it at `1/3`; empirical ratio at
`n = 10` is `0.42`. Sub-phase 5b (periodic 2D tile constructions) is
the cheapest entry point; 5c (joint LP relaxation for tighter UBs) is
exploratory.

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

## Phase 5 — square asymptotics

`P(n, n) / n²`. Basic UB caps it at `1/3`; empirical ratio at `n = 10` is
`0.42`. Three sub-phases of varying depth.

### 5a — Better solver for `P(n, n)`, `n > 10`
The current bitpacked DP has `m ≤ ~10`. To extend square data we need a
new solver: e.g. branch-and-bound with the existing bound functions, or an
ILP/MILP via OR-Tools/Gurobi. **Weeks of work.**

### 5b — Periodic 2D tile constructions
Design 3×3 or 4×4 motifs achieving full-degree density above `1/2`,
prove tileability with consistent boundary, conclude
`lim P(n, n) / n² ≥ ρ`. **Days of work**, uncertain whether `ρ` improves
on the trivial spine construction.

### 5c — Tighter UB combining 4-cycle hitting set and deficiency
Currently the basic UB on squares is `(1/3) n² + O(n)` (trivially). A 4-
cycle hitting set bound says interior preserved vertices ≤ `(3/4) I` per
unit-square obstruction. Combining gives `(7/12) n² + O(n)` — already
weaker. Need an LP relaxation of the joint constraints; solve for small
`n`, observe the asymptotic. **Open**, exploratory.

**Recommended ordering within Phase 5**: 5b before 5a because it's cheaper
and might match observed densities directly.

## Phase 6 — Lean formalization of `P(m, n) ≤ basicUB m n`

Build the operational layer in Lean to convert the empirical certification
of the basic upper bound into a machine-checked theorem.

**Effort**: 2–4 weeks.
**Yield**: the principal upper bound moves from "empirically true for
m, n ≤ 9" to "proven for all m, n".
**Risk**: mathlib's `SimpleGraph.IsAcyclic` and spanning-tree API may
need extension for the combinatorial sums; non-trivial library
contributions may be required.

### Subtasks

1. **6.1** Define `IsSpanningTree (T : SimpleGraph (GridVertex m n)) :
   Prop` capturing acyclicity + connectedness + spanning + subgraph of
   `gridGraph m n`.
2. **6.2** Define `vertexDeg T v : ℕ` and prove
   `∑ v, vertexDeg T v = 2 * (m * n − 1)` for any spanning tree.
3. **6.3** Define `numFullDegree T : ℕ` and `vertexDeficiency T v : ℕ`,
   plus the obvious lemma `numFullDegree T = card {v | vertexDeficiency T
   v = 0}`.
4. **6.4** Prove the global identity `∑ v, vertexDeficiency T v = D m n`
   (combines 6.2 with `Defs.lean::degSumGrid` and the proven
   `deficiency_closed_form`).
5. **6.5** Prove the per-vertex deficiency cap: for any non-full-degree
   vertex `v`, `vertexDeficiency T v ≤ deg_G v − 1` (i.e. ≤ 3, 2, 1 for
   interior, border, corner respectively).
6. **6.6** Conclude `P m n ≤ basicUB m n` via deficiency packing
   (combining 6.4, 6.5, and `ceilDiv3_mul_ge` already proved in
   `Bounds.lean`).
7. **6.7** Update `lean/STATUS.md`, `lean/EVIDENCE.md`, `lean/README.md`
   to reflect the theorem.

## Phase 7 — Lean formalization of explicit constructions (long-term)

Once Phase 3 produced explicit per-`m` constructions and Phase 6 the upper
bound, the natural next Lean target is:

> for each fixed `m ∈ {3, 4, 5, 6, 7, 8}`, formalize the explicit
> construction as a Lean term and prove it achieves the conjectured count.

This produces machine-checked theorems for `P(m, n)` for `m ≤ 8`, all
`n ≥ m`. **Effort**: indefinite; depends on Phase 6 foundations. Multi-month.

## Open problems

Aggregated from the various analysis files. A fresh agent picking up this
project should know about all of these:

1. **m = 5 at n ≡ 1 (mod 3)**: ✓ resolved by Phase 4 — `tree_m5_period3_motif`
   uses the "fully preserved interior column" trick.
2. **m = 6 at n ≢ 0 (mod 4)**: not yet encoded; Phase 4 found the
   period-4 interior motif but residue-specific boundaries remain.
3. **m = 8 motif**: ✓ resolved by Phase 4 — `tree_m8_witness` encodes
   the period-7 motif at `n ∈ {20, 34, 48}`. Generalizing to all
   residues mod 7 (let alone all n ≥ 13) is straightforward but
   tedious.
4. **Matching upper bounds for m ∈ {3, 5, 6}**: ✓ resolved by Phase 4
   — Karp's max-mean cycle delivers rigorous matching UBs. `m = 8`
   matched empirically only.
5. **Square asymptotics**: `lim P(n, n)/n²` is unknown. Basic UB gives
   `≤ 1/3`, empirical at n=10 is `≈ 0.42`. Phase 5.
6. **Lean operational connection**: `P(m, n) ≤ basicUB m n` is empirically
   true (`m, n ≤ 9` exhaustively verified) but not Lean-proved. Phase 6.

## Verification quickstart

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

- Phase 4 (DONE) depended on Phase 3 (uses the same DP + verified
  motifs as cross-checks).
- Phase 5 is independent of Phases 4, 6, 7.
- Phase 6 is independent of Phase 4 (it formalizes the basic UB which
  is already algebraically proved).
- Phase 7 depends on Phase 6 (operational connection) and benefits from
  Phase 4 (clean motifs for the construction side).
