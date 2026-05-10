# Empirical and Formal Evidence

This document collects the **formally proven** Lean lemmas in this project, the
**empirical** results from the Rust DP solver in `../src/`, and how they
correspond.

## Problem statement

The **grid graph** `G(m, n)` has `m × n` vertices arranged in an orthogonal
grid; each vertex is adjacent to the (up to four) vertices immediately above,
below, left, and right of it. A **spanning tree** of `G(m, n)` is a connected
acyclic subgraph containing every vertex. A vertex `v` is **full-degree** in a
spanning tree `T` if `deg_T(v) = deg_G(v)` — equivalently, every grid edge
incident to `v` is retained by `T`. Write `P(m, n)` for the maximum number of
full-degree vertices over all spanning trees of `G(m, n)`. The goal of the
project is to determine `P(m, n)` (or constrain it tightly) and ideally
exhibit a tree achieving it. ("Full-degree" and "preserved" are used
interchangeably in this codebase, following `docs/DERIVATION.md`.)

## Formally Proven (Lean 4 + mathlib, zero `sorry`s in active code)

A complete `lake build` succeeds (`lake build` exit 0) and a syntactic check
confirms there are no `sorry`/`admit` tokens in tactic position anywhere in the
project. All claims below are checked by the Lean kernel.

### `GridGraphs/Defs.lean`

Definitions (no proofs needed): `numVerts`, `numHoriz`, `numVert`, `numEdges`,
`degSumGrid`, `degSumTree`, `deficiency`, `numCorners`, `numBorderNonCorner`,
`numInterior`, `GridVertex`, `adjacent`, `gridGraph`.

The grid graph itself is a real `SimpleGraph (Fin m × Fin n)` with proven
symmetry and irreflexivity (loopless), at `Defs.lean:112`.

| Lemma | Statement | Location |
|-------|-----------|----------|
| `numEdges_eq` | `numEdges m n = m*(n-1) + n*(m-1)` | `Defs.lean:19` |
| `succ_mul_succ_sub_one` | `(a+1)*(b+1) - 1 = a*b + a + b` | `Defs.lean:33` |
| `deficiency_succ_succ` | `deficiency (m+1) (n+1) = 2*m*n` | `Defs.lean:40` |
| **`deficiency_closed_form`** | **`deficiency m n = 2 * (m-1) * (n-1)`** | `Defs.lean:63` |
| **`verts_partition`** | **`numCorners + numBorderNonCorner + numInterior = m * n`** | `Defs.lean:211` |

The grid graph also carries `Fintype`, `DecidableEq`, and `DecidableRel` instances at `Defs.lean:103,106,151`, so `(gridGraph m n).degree` is a real (computable) function. `gridDegree`, `isPreserved`, `vertexDeficiency`, and `numPreserved` are now defined in terms of mathlib's `SimpleGraph.degree` (no longer stubs).

### `GridGraphs/Bounds.lean` — algebraic bound expressions

Definitions: `D`, `I`, `ceilDiv3`, `basicUB`, `refinedUB`, `lowerB` matching the
formulas in `docs/DERIVATION.md`.

| Lemma | Statement | Location |
|-------|-----------|----------|
| `ceilDiv3_mul_ge` | `3 * ceilDiv3 x ≥ x` | `Bounds.lean:55` |
| `ceilDiv3_mul_le` | `3 * ceilDiv3 x ≤ x + 2` | `Bounds.lean:64` |
| `ceilDiv3_mono` | `x ≤ y → ceilDiv3 x ≤ ceilDiv3 y` | `Bounds.lean:71` |
| `ceilDiv3_three_mul` | `ceilDiv3 (3*k) = k` | `Bounds.lean:76` |
| **`D_eq_deficiency`** | **`D m n = deficiency m n`** (bridges the algebraic and operational defs) | `Bounds.lean:91` |
| `D_expand` | `D + 2m + 2n = 2 m n + 2` (m, n ≥ 1) | `Bounds.lean:99` |
| `D_le_three_mn` | `D m n ≤ 3 m n` (m, n ≥ 1) | `Bounds.lean:109` |
| `basicUB_le_mn` | `basicUB m n ≤ m * n` | `Bounds.lean:122` |
| `ceilDiv3_D_le_mn` | `ceilDiv3 (D m n) ≤ m n` (m, n ≥ 1) | `Bounds.lean:126` |
| `D_4n` | `D 4 n = 6 * (n - 1)` | `Bounds.lean:136` |
| **`basicUB_4n`** | **`basicUB 4 n = 2*n + 2`** (n ≥ 1) | `Bounds.lean:141` |
| `I_4n` | `I 4 n = 2 * (n - 2)` (n ≥ 3) | `Bounds.lean:153` |
| **`refinedUB_4n`** | **`refinedUB 4 n = 2*n + 1`** (n ≥ 3) | `Bounds.lean:161` |
| `refinedUB_lt_basicUB_4n` | `refinedUB 4 n + 1 = basicUB 4 n` (n ≥ 3) | `Bounds.lean:179` |
| **`lowerB_le_basicUB`** | **`m + n − 1 ≤ basicUB m n`** (m, n ≥ 1) | `Bounds.lean:186` |
| **`refinedUB_le_basicUB`** | **`refinedUB m n ≤ basicUB m n`** (m, n ≥ 1) | `Bounds.lean:205` |

### `GridGraphs/Forced.lean` — forced edges

| Lemma | Statement | Location |
|-------|-----------|----------|
| `forcedEdgeGraph` (def) | the subgraph of all `G`-edges incident to some `F`-vertex | `Forced.lean:27` |
| `preservesIncidentEdges` (def) | edge-containment formulation of full-degree | `Forced.lean:43` |
| `forcedEdgeGraph_le_of_preserves` | preserved → forced edges lie in `T` | `Forced.lean:48` |
| **`forcedEdgeGraph_isAcyclic_of_preserves`** | **forced-edge graph of preserved set in acyclic `T` is acyclic** | `Forced.lean:58` |
| `grid_forcedEdgeGraph_isAcyclic_of_preserves` | grid specialisation | `Forced.lean:73` |

### `GridGraphs/Diagonal.lean` — induced-edge decycling and cell hitting

| Lemma | Statement | Location |
|-------|-----------|----------|
| `IsInducedEdgeDecyclingSet` (def) | `forcedEdgeGraph G Uᶜ` acyclic | `Diagonal.lean:22` |
| `forcedEdgeGraph_compl_adj_iff` | `Uᶜ`-forced graph = grid edges not internal to `U` | `Diagonal.lean:27` |
| `compl_isInducedEdgeDecyclingSet_of_preserves` | `Fᶜ` is decycling for any preserved `F` | `Diagonal.lean:47` |
| `fourCycle_has_unforced_edge` | every acyclic 4-cycle has a `U-U` boundary edge | `Diagonal.lean:57` |
| `gridGraph_cell_adj_top` etc. | the four boundary edges of every cell are grid edges | `Diagonal.lean:130–145` |
| `cell00_ne_cell11`, `cell01_ne_cell10` | diagonal disequalities | `Diagonal.lean:148,155` |
| **`grid_cell_has_unforced_edge`** | **every grid 2×2 cell has at least one `U-U` boundary edge** | `Diagonal.lean:164` |
| `grid_cell_has_unforced_corner` | every cell contains at least one corner outside `F` | `Diagonal.lean:180` |
| `preserved_set_cell_corner` | spanning-subgraph form of the cell-hitting condition | `Diagonal.lean:195` |
| `connected_graph_has_spanning_tree` | wrapper around mathlib's `Connected.exists_isTree_le` | `Diagonal.lean:214` |

### `GridGraphs/ResidueOne.lean` — residue-1 diagonal `U` cardinality

For `n = 3k + 1` (square grid `n × n`), the residue-1 lower-bound construction
`residue_one_pattern` from `analysis/diagonal_patterns.py` (see Proposition L1
in `analysis/proofs_diagonal.md`) is encoded as a `Finset` and its cardinality
is proven exactly.

| Lemma | Statement | Location |
|-------|-----------|----------|
| `isInUResidueOne` (def) | predicate carving out the four row-classes of `U` | `ResidueOne.lean:44` |
| `uResidueOne` (def) | the construction as a `Finset (GridVertex (3k+1) (3k+1))` | `ResidueOne.lean:57` |
| `uResidueOne_card_sum` | row decomposition via `Finset.card_eq_sum_card_fiberwise` | `ResidueOne.lean:112` |
| `row_col_count` | per-row column count: 1 / 3k / 3k+1 / 0 by row class | `ResidueOne.lean:150` |
| `card_rows_sparse` | `k` sparse-anchor rows | `ResidueOne.lean:231` |
| `card_rows_dense` | `2k − 1` dense rows | `ResidueOne.lean:273` |
| `card_rows_full` | `1` final dense row (only `r = 3k − 1`) | `ResidueOne.lean:380` |
| `card_rows_empty` | `1` bottom empty row (only `r = 3k`) | `ResidueOne.lean:395` |
| **`uResidueOne_card`** | **`|uResidueOne k| = 6 * k^2 + k + 1`** for `k ≥ 1` | `ResidueOne.lean:416` |
| `q` (def) | the conjectured diagonal closed form from `analysis/proofs_diagonal.md` | `ResidueOne.lean:497` |
| `uResidueOne_card_eq_q` | `|uResidueOne k| = q (3k + 1)` | `ResidueOne.lean:509` |

### `GridGraphs/Tests.lean` — small-grid sanity tests

A regression suite of `decide`-evaluated `example`s pinning Lean values
of `D`, `basicUB`, `refinedUB`, `lowerB`, the vertex-class counts, and
`uResidueOne k` cardinalities to specific small-grid values matching
`lean/results-empirical.csv`. Any regression in the bound expressions or
vertex counts breaks `lake build`.

### `GridGraphs/Spanning.lean` — operational upper bound `P(m,n) ≤ basicUB m n`

Phase 8 from `docs/ROADMAP.md`. Bridges the algebraic bound expressions to
the operational quantity `numPreserved m n T` for a spanning subtree `T`.

| Lemma | Statement | Location |
|-------|-----------|----------|
| `gridGraph_eq_boxProd` | `gridGraph m n = pathGraph m □ pathGraph n` | `Defs.lean` |
| `gridGraph_connected` | `(gridGraph m n).Connected` for `m, n ≥ 1` | `Defs.lean` |
| `pathGraph_degree_interior` etc. | path-graph degree at interior / endpoints | `Spanning.lean:49–137` |
| `gridGraph_degree` | `(gridGraph m n).degree v = (pathGraph m).degree v.1 + (pathGraph n).degree v.2` | `Spanning.lean:155` |
| `gridGraph_degree_le_four` | every grid vertex has degree ≤ 4 | `Spanning.lean:173` |
| `gridGraph_degree_corner` / `_border` / `_interior` | per-class closed forms (2/3/4) | `Spanning.lean:201,218,247` |
| `pathGraph_card_edgeFinset` | `#(pathGraph k).edgeFinset = k − 1` | `Spanning.lean:262` |
| `gridGraph_card_edgeFinset` | `2 * #(gridGraph m n).edgeFinset = 2 * numEdges m n` | `Spanning.lean:353` |
| `IsSpanningSubtree` (def) | `T ≤ G ∧ T.IsTree` | `Spanning.lean:388` |
| `IsSpanningSubtree.degree_le` | `T.degree v ≤ G.degree v` | `Spanning.lean:401` |
| `IsSpanningSubtree.card_edgeFinset` | `#T.edgeFinset + 1 = Fintype.card V` | `Spanning.lean:407` |
| `IsSpanningSubtree.sum_degrees` | `∑ v, T.degree v = 2 * (Fintype.card V − 1)` | `Spanning.lean:413` |
| `sum_gridGraph_degree` | `∑ v, (gridGraph m n).degree v = 2 * numEdges m n` | `Spanning.lean:425` |
| **`total_deficiency`** | **`∑ v, vertexDeficiency m n T v = D m n` for spanning subtrees** | `Spanning.lean:434` |
| `tree_degree_pos` | `T.degree v ≥ 1` for `m * n ≥ 2` | `Spanning.lean:491` |
| **`vertexDeficiency_le_three`** | **per-vertex cap of 3 for `m, n ≥ 2`** | `Spanning.lean:534` |
| `vertexDeficiency_le_one_of_corner` | corner cap of 1 | `Spanning.lean:544` |
| `vertexDeficiency_le_two_of_border` | border (non-corner) cap of 2 | `Spanning.lean:556` |
| **`preserved_le_basicUB`** | **`numPreserved m n T ≤ basicUB m n` for spanning subtrees** | `Spanning.lean:571` |
| `forall_spanning_subtree_preserved_le_basicUB` | ∀-quantified form | `Spanning.lean:701` |

The headline `preserved_le_basicUB` connects the algebraic bound
expressions of `Bounds.lean` to the operational `numPreserved` quantity,
formalising the empirical bound `P(m, n) ≤ basicUB m n` that
`results-empirical.csv` documents for `m, n ≤ 10`.

### What is **not** formally proven (deferred)

The following theorems are still open in Lean. The total-deficiency identity,
per-vertex caps, and `preserved_le_basicUB` are now **proven** (Phase 8
done — see `Spanning.lean` above).

- For any spanning subtree `T`, `numPreserved(T) ≤ refinedUB m n`. The
  ingredients (per-class caps `vertexDeficiency_le_one_of_corner`,
  `_le_two_of_border`, `_le_three`) are all proved; the arithmetic for
  `refinedUB`'s piecewise definition is the remaining work.
- There exists a spanning tree achieving `numPreserved ≥ m + n − 1`. The
  "double-comb" lower bound construction. Combined with `preserved_le_basicUB`,
  this would close the basic sandwich `lowerB m n ≤ P(m, n) ≤ basicUB m n`.
- **Forest-extension lemma**: any forest `F ≤ G` in a finite connected graph
  `G` extends to a spanning tree of `G`. Combined with `uResidueOne_card`
  and an acyclicity argument, this would give
  `maxPreserved (3k+1) (3k+1) ≥ (3k+1)^2 − (6k^2 + k + 1)`,
  i.e. the residue-1 half of Conjecture C from `docs/ROADMAP.md`. The
  intermediate step (proving the forced-edge graph of `(uResidueOne k)ᶜ` is
  acyclic) is currently empirical only — verified by
  `analysis/check_diagonal_patterns.py` for every `n = 3k + 1` in `[4, 40]`.

What we **do** have is the algebraic infrastructure (`D_expand`,
`refinedUB_le_basicUB`, `lowerB_le_basicUB`, the 4×n closed forms) that is a
prerequisite for these connecting theorems, plus empirical verification (below)
that the bound functions are valid against ground truth `P(m,n)` from DP for all
`1 ≤ m, n ≤ 10`.

---

## Empirical Evidence (Rust DP, exhaustive on small grids)

`cargo test --release` from the repo root (`../`):

```
running 5 tests
test analysis::tests::trivial_bounds_hold_small ... ok
test analysis::tests::refined_expected_4xn_pattern ... ok
test analysis::tests::monotonicity ... ok
test analysis::tests::lower_bounds_valid_small ... ok
test analysis::tests::refined_never_worse_and_valid ... ok

test result: ok. 5 passed; 0 failed; 0 ignored; 0 measured
```

Concretely, `refined_never_worse_and_valid` verifies, for every `1 ≤ m, n ≤ 9`,
that `actual P(m,n) ≤ refinedUB(m,n) ≤ basicUB(m,n)`, where `actual` is computed
by the exhaustive DP in `src/main.rs`. `refined_expected_4xn_pattern` verifies
`basicUB(4, n) = 2n+2` and `refinedUB(4, n) = 2n+1` for `2 ≤ n ≤ 10` — exactly
the closed forms proven in Lean as `basicUB_4n` and `refinedUB_4n`.

### Full table for `1 ≤ m, n ≤ 10`

Generated by `CSV=1 cargo run --release -- compare 10 10` and saved at
`lean/results-empirical.csv`. Every row satisfies
`LB_simple ≤ P(m,n) ≤ refinedUB ≤ basicUB`.

| m | n | P(m,n) | LB_simple = max(m,n) | basicUB | refinedUB | basicUB − P |
|---|---|--------|----------------------|---------|-----------|-------------|
| 1 | 1 | 1 | 1 | 1 | 1 | 0 |
| 1 | 2 | 2 | 2 | 2 | 2 | 0 |
| 1 | 3 | 3 | 3 | 3 | 3 | 0 |
| 1 | 4 | 4 | 4 | 4 | 4 | 0 |
| 1 | 5 | 5 | 5 | 5 | 5 | 0 |
| 1 | 6 | 6 | 6 | 6 | 6 | 0 |
| 1 | 7 | 7 | 7 | 7 | 7 | 0 |
| 1 | 8 | 8 | 8 | 8 | 8 | 0 |
| 1 | 9 | 9 | 9 | 9 | 9 | 0 |
| 1 | 10 | 10 | 10 | 10 | 10 | 0 |
| 2 | 1 | 2 | 2 | 2 | 2 | 0 |
| 2 | 2 | 2 | 2 | 3 | 3 | 1 |
| 2 | 3 | 3 | 3 | 4 | 4 | 1 |
| 2 | 4 | 4 | 4 | 6 | 5 | 2 |
| 2 | 5 | 5 | 5 | 7 | 6 | 2 |
| 2 | 6 | 6 | 6 | 8 | 7 | 2 |
| 2 | 7 | 7 | 7 | 10 | 8 | 3 |
| 2 | 8 | 8 | 8 | 11 | 9 | 3 |
| 2 | 9 | 9 | 9 | 12 | 10 | 3 |
| 2 | 10 | 10 | 10 | 14 | 11 | 4 |
| 3 | 1 | 3 | 3 | 3 | 3 | 0 |
| 3 | 2 | 3 | 3 | 4 | 4 | 1 |
| 3 | 3 | 4 | 3 | 6 | 5 | 2 |
| 3 | 4 | 6 | 4 | 8 | 7 | 2 |
| 3 | 5 | 7 | 5 | 9 | 8 | 2 |
| 3 | 6 | 8 | 6 | 11 | 10 | 3 |
| 3 | 7 | 10 | 7 | 13 | 11 | 3 |
| 3 | 8 | 11 | 8 | 14 | 13 | 3 |
| 3 | 9 | 12 | 9 | 16 | 14 | 4 |
| 3 | 10 | 14 | 10 | 18 | 16 | 4 |
| 4 | 1 | 4 | 4 | 4 | 4 | 0 |
| 4 | 2 | 4 | 4 | 6 | 5 | 2 |
| 4 | 3 | 6 | 4 | 8 | 7 | 2 |
| 4 | 4 | 8 | 4 | 10 | 9 | 2 |
| 4 | 5 | 10 | 5 | 12 | 11 | 2 |
| 4 | 6 | 12 | 6 | 14 | 13 | 2 |
| 4 | 7 | 14 | 7 | 16 | 15 | 2 |
| 4 | 8 | 16 | 8 | 18 | 17 | 2 |
| 4 | 9 | 18 | 9 | 20 | 19 | 2 |
| 4 | 10 | 20 | 10 | 22 | 21 | 2 |
| 5 | 1 | 5 | 5 | 5 | 5 | 0 |
| 5 | 2 | 5 | 5 | 7 | 6 | 2 |
| 5 | 3 | 7 | 5 | 9 | 8 | 2 |
| 5 | 4 | 10 | 5 | 12 | 11 | 2 |
| 5 | 5 | 11 | 5 | 14 | 13 | 3 |
| 5 | 6 | 13 | 6 | 16 | 16 | 3 |
| 5 | 7 | 16 | 7 | 19 | 18 | 3 |
| 5 | 8 | 17 | 8 | 21 | 21 | 4 |
| 5 | 9 | 19 | 9 | 23 | 23 | 4 |
| 5 | 10 | 22 | 10 | 26 | 26 | 4 |
| 6 | 1 | 6 | 6 | 6 | 6 | 0 |
| 6 | 2 | 6 | 6 | 8 | 7 | 2 |
| 6 | 3 | 8 | 6 | 11 | 10 | 3 |
| 6 | 4 | 12 | 6 | 14 | 13 | 2 |
| 6 | 5 | 13 | 6 | 16 | 16 | 3 |
| 6 | 6 | 16 | 6 | 19 | 19 | 3 |
| 6 | 7 | 19 | 7 | 22 | 22 | 3 |
| 6 | 8 | 21 | 8 | 24 | 24 | 3 |
| 6 | 9 | 23 | 9 | 27 | 27 | 4 |
| 6 | 10 | 26 | 10 | 30 | 30 | 4 |
| 7 | 1 | 7 | 7 | 7 | 7 | 0 |
| 7 | 2 | 7 | 7 | 10 | 8 | 3 |
| 7 | 3 | 10 | 7 | 13 | 11 | 3 |
| 7 | 4 | 14 | 7 | 16 | 15 | 2 |
| 7 | 5 | 16 | 7 | 19 | 18 | 3 |
| 7 | 6 | 19 | 7 | 22 | 22 | 3 |
| 7 | 7 | 22 | 7 | 25 | 25 | 3 |
| 7 | 8 | 25 | 8 | 28 | 28 | 3 |
| 7 | 9 | 28 | 9 | 31 | 31 | 3 |
| 7 | 10 | 31 | 10 | 34 | 34 | 3 |
| 8 | 1 | 8 | 8 | 8 | 8 | 0 |
| 8 | 2 | 8 | 8 | 11 | 9 | 3 |
| 8 | 3 | 11 | 8 | 14 | 13 | 3 |
| 8 | 4 | 16 | 8 | 18 | 17 | 2 |
| 8 | 5 | 17 | 8 | 21 | 21 | 4 |
| 8 | 6 | 21 | 8 | 24 | 24 | 3 |
| 8 | 7 | 25 | 8 | 28 | 28 | 3 |
| 8 | 8 | 27 | 8 | 31 | 31 | 4 |
| 8 | 9 | 30 | 9 | 34 | 34 | 4 |
| 8 | 10 | 34 | 10 | 38 | 38 | 4 |
| 9 | 1 | 9 | 9 | 9 | 9 | 0 |
| 9 | 2 | 9 | 9 | 12 | 10 | 3 |
| 9 | 3 | 12 | 9 | 16 | 14 | 4 |
| 9 | 4 | 18 | 9 | 20 | 19 | 2 |
| 9 | 5 | 19 | 9 | 23 | 23 | 4 |
| 9 | 6 | 23 | 9 | 27 | 27 | 4 |
| 9 | 7 | 28 | 9 | 31 | 31 | 3 |
| 9 | 8 | 30 | 9 | 34 | 34 | 4 |
| 9 | 9 | 34 | 9 | 38 | 38 | 4 |
| 9 | 10 | 38 | 10 | 42 | 42 | 4 |
| 10 | 1 | 10 | 10 | 10 | 10 | 0 |
| 10 | 2 | 10 | 10 | 14 | 11 | 4 |
| 10 | 3 | 14 | 10 | 18 | 16 | 4 |
| 10 | 4 | 20 | 10 | 22 | 21 | 2 |
| 10 | 5 | 22 | 10 | 26 | 26 | 4 |
| 10 | 6 | 26 | 10 | 30 | 30 | 4 |
| 10 | 7 | 31 | 10 | 34 | 34 | 3 |
| 10 | 8 | 34 | 10 | 38 | 38 | 4 |
| 10 | 9 | 38 | 10 | 42 | 42 | 4 |
| 10 | 10 | 42 | 10 | 46 | 46 | 4 |

Aggregate statistics over the 100 rows above:
- All rows satisfy `LB_simple ≤ P(m,n) ≤ refinedUB ≤ basicUB`.
- 19 rows have `P(m,n) = refinedUB` (refined bound is tight).
- Maximum gap `basicUB − P` is 4; mean gap is 2.38.
- The 4×n family confirms the proven Lean closed forms: for every n ∈ {1..10},
  `basicUB(4,n) = 2n+2` and (for n ≥ 3) `refinedUB(4,n) = 2n+1`.

---

## How the formal and empirical layers connect

The Lean proofs now cover **both** the algebraic bound expressions
(`basicUB`, `refinedUB`, `lowerB`, with their identities, monotonicity, and
ordering) **and** the operational connection
`P(m, n) ≤ basicUB m n` via `Spanning.lean`. Concretely, for any spanning
subtree `T` of `gridGraph m n`:

```
preserved_le_basicUB : numPreserved m n T ≤ basicUB m n
```

is now a Lean theorem (Phase 8 of `docs/ROADMAP.md`). The empirical layer
in this file (the `1 ≤ m, n ≤ 10` table) was previously the *only* layer
asserting this inequality; it is now also formally proved.

What remains:
- The matching upper bound `numPreserved ≤ refinedUB m n` (the per-class
  deficiency caps in `Spanning.lean` are proved; the piecewise arithmetic
  is the only remaining work).
- The matching lower bound `lowerB m n ≤ maxPreserved m n` (would require
  the explicit "double-comb" construction).
- The diagonal residue-1 lower bound (depends on the forest-extension lemma
  and acyclicity of the `(uResidueOne k)ᶜ`-forced graph).
