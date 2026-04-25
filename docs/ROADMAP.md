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
| `analysis/check_constructions.py` | Independent verifier of explicit spanning trees |
| `analysis/render_witness.py`, `analysis/motif_search.py` | Motif inspection scratchpads |
| `lean/GridGraphs/Defs.lean`, `lean/GridGraphs/Bounds.lean` | Lean 4 + mathlib formalization (bound expressions, deficiency identity) |
| `lean/STATUS.md`, `lean/EVIDENCE.md` | Lean-side status and lemma index |

## Status

| Phase | Title | Status | Reference |
|-------|-------|--------|-----------|
| 1 | Per-`m` closed-form conjectures | **Done** | `analysis/recurrences.md`, `analysis/conjectures.md` |
| 2 | OEIS / prior-art lookup | **Done** | `analysis/oeis.md` |
| 3 | DP backtracking → motif extraction (constructive LBs) | **Done (mostly)** | `analysis/proofs_m345.md`, `src/witness.rs` |
| 4 | Matching upper bounds via Karp's max-mean cycle | Pending — **recommended next** | — |
| 5 | Square asymptotics (5a solver, 5b tile, 5c LP UB) | Pending | — |
| 6 | Lean formalization of `P(m, n) ≤ basicUB m n` | Pending | — |
| 7 | Lean formalization of explicit constructions | Pending (multi-month) | — |

### What Phase 3 actually delivered

In the **n ≥ m** asymptotic regime, with constructions verified by an
independent checker:

| m | construction | optimal in n ≥ m regime |
|---|--------------|------------------------|
| 1 | `tree_m1` (path) | 49/49 |
| 2 | `tree_m2` (ladder) | 49/49 |
| 3 | `tree_m3_witness` (period 3) | 48/48 |
| 4 | `tree_m4_double_spine` (period 1) | 47/47 |
| 5 | `tree_m5_witness` (three-spine) | 31/46 — off by 1 only at `n ≡ 1 (mod 3)` |
| 6 | `tree_m6_witness` (period 4) | 11/11 — only `n ≡ 0 (mod 4)` implemented |
| 7 | `tree_m7_witness` (period 1) | 24/24 |
| 8 | not implemented | — |

For m ∈ {1, 2, 3, 4, 7}, the constructive LB matches the conjectured `P(m, n)`
exactly in the n ≥ m regime. For m ∈ {5, 6}, the LB is partial. For m = 8,
no closed-form construction was extracted: the witness-DP output has a
period-7 macro-pattern that resisted hand transcription. Phase 4 is expected
to resolve all three open cases simultaneously.

## Recommended next: Phase 4 — transfer matrix + Karp's max-mean cycle

For each fixed `m`, build the column transition graph from the DP (states =
canonical `(labels, degs)` tuples, edges = single-column fills weighted by
the per-column gain in full-degree count), then compute the maximum-mean
cycle. The mean cycle weight equals `α_m` rigorously, and the cycle itself
specifies the optimal periodic motif — providing both the matching upper
bound to the Phase 3 lower bounds and the explicit motif for hard cases
(m = 5, 8 in particular).

### Why Phase 4 next

1. **Closes the m = 5 residue gap** at n ≡ 1 (mod 3). The current
   three-spine ansatz is off by 1; Karp's cycle extraction picks up the
   "preserved interior column" trick we observed in optimal witness output.
2. **Extracts the m = 8 motif** that we couldn't read off by hand.
3. **Promotes per-`m` conjectures to theorems** for any width where the
   max-mean cycle's weight matches the Phase 3 LB.
4. **Reuses existing DP infrastructure**: state enumeration is already
   done implicitly by `src/main.rs`'s forward sweep.

### Subtasks (do all m ∈ {3, 4, 5, 6, 7, 8})

1. **4.1** Add a `src/transfer.rs` module that, given `m`, runs a forward
   DP for one column to enumerate every reachable canonical `(labels,
   degs)` state. Save as `Vec<State>` with stable indices.
2. **4.2** For each state `s`, simulate one full column-fill from `s` and
   collect the set of `(s', gain)` outgoing transitions. Emit as a
   directed weighted graph `Vec<(usize, usize, i32)>` (edges with gains).
3. **4.3** Implement Karp's max-mean-cycle algorithm
   (`O(|V| · |E|)` time, well within budget at `m ≤ 8`).
4. **4.4** Run for `m ∈ {3, 4, 5, 6, 7, 8}`. For each `m`:
   - Compute `α_m` from the cycle's mean weight.
   - Confirm it matches the rational `α_m` from `analysis/recurrences.md`.
   - Extract the optimal cycle (sequence of states) and translate each
     transition to a column-fill pattern.
5. **4.5** For each `m`, verify the cycle starts from the initial state
   and that boundary columns (first and last) contribute the expected
   constant to the closed form. This is needed to lift the *asymptotic*
   slope theorem to an *exact* closed-form theorem.
6. **4.6** For m ∈ {5, 8} (and any other widths where Phase 3's LB was
   incomplete), encode the extracted motif as a closed-form Python
   builder in `analysis/check_constructions.py` and verify it produces
   `P(m, n)` exactly for n in the verified range.
7. **4.7** Add a Rust regression test: for each `m ∈ {3, ..., 8}`,
   the computed `α_m` from Karp's algorithm equals the conjectured rational.
8. **4.8** Write up in `analysis/proofs_upper.md` with the per-`m`
   transition-graph sizes, the optimal cycles, and the resulting theorems
   (asymptotic slope + closed form + matching upper bound).

### Definition of done

- `α_m` rationally computed and verified by Karp for m ∈ {3, ..., 8}.
- Closed-form constructions in `check_constructions.py` for all m ∈ {3, ..., 8}
  in the n ≥ m regime, including the previously-failing m = 5 (n ≡ 1 mod 3)
  and m = 8.
- Each closed form is a **theorem** (LB by construction, UB by max-mean cycle)
  for the asymptotic slope, optionally also for the exact value.

### Risks

- State enumeration may produce thousands of states for m = 8; check that
  Karp's `O(V·E)` runs in seconds (it should — m = 8 frontier-state count
  is bounded by Bell(8) · 4^8 ≈ 1.7 × 10^7, but reachability prunes this
  dramatically).
- Phase-alignment: the optimal cycle may not start from the DP's initial
  state. Closed-form theorems require explicitly handling the "boundary
  transient" before the cycle locks in.

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

1. **m = 5 at n ≡ 1 (mod 3)**: optimum is `2n + 2` but our three-spine
   construction gives `2n + 1`. Optimal witness uses a "fully preserved
   interior column" cluster that doesn't fit the three-spine ansatz.
   Phase 4 should resolve.
2. **m = 6 at n ≢ 0 (mod 4)**: only `n ≡ 0 (mod 4)` is implemented.
   Other residues need per-residue boundary corrections. Phase 4 should
   resolve.
3. **m = 8 motif**: the period-7 macro-structure is too complex to
   transcribe by hand. Phase 4 should resolve.
4. **Matching upper bounds for m ∈ {3, 5, 6}**: even where Phase 3's LB
   is tight, the proven UB (`basicUB` from Lean) is loose by `Θ(n)`. To
   make per-`m` formulas into theorems, we need matching UBs — Phase 4
   delivers this through Karp's algorithm.
5. **Square asymptotics**: `lim P(n, n)/n²` is unknown. Basic UB gives
   `≤ 1/3`, empirical at n=10 is `≈ 0.42`. Phase 5.
6. **Lean operational connection**: `P(m, n) ≤ basicUB m n` is empirically
   true (`m, n ≤ 9` exhaustively verified) but not Lean-proved. Phase 6.

## Verification quickstart

A fresh agent should run these to confirm the current state in ~30 seconds:

```bash
# 1. Rust solver + analysis tests (8 tests)
cargo test --release
# Expected: "test result: ok. 8 passed; 0 failed"

# 2. Lean formal proofs (sorry-free)
cd lean && lake build && cd ..
# Expected: "Build completed successfully"

# 3. Construction checker (n ≥ m regime, m ∈ {1..7})
python3 analysis/check_constructions.py
# Expected (in summary):
#   m=1 trivial path                                49      49
#   m=2 ladder                                      49      49
#   m=3 period-3 witness                            48      48
#   m=4 double-spine                                47      47
#   m=5 three-spine                                 46      31   ← 15 misses at n%3==1, off by 1
#   m=6 period-4 witness (n%4==0 only)              11      11
#   m=7 period-1 witness                            24      24

# 4. (Optional) regenerate the empirical data
CSV=1 cargo run --release -- compare 8 20 > data/extended.csv

# 5. (Optional) inspect the optimal tree at any (m, n)
cargo run --release -- witness 5 21
# prints "# m=5 n=21 value=43 transposed=False edges=104" + the edge list
```

If all three primary commands pass, the repo is in a good state. Any
discrepancy should be investigated before starting a new phase.

## Phase dependency notes

- Phase 4 depends on Phase 3 (uses the same DP + verified motifs as
  cross-checks).
- Phase 5 is independent of Phases 4, 6, 7.
- Phase 6 is independent of Phase 4 (it formalizes the basic UB which is
  already algebraically proved).
- Phase 7 depends on Phase 6 (operational connection) and benefits from
  Phase 4 (clean motifs for the construction side).
