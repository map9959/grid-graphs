# Proof Status

This file is the authoritative ledger of what is and isn't formally proven in
the Lean project. Last verified by `lake build` (exit 0) on the current
commit.

A grep over the active `*.lean` sources confirms **zero `sorry` and zero
`admit` tokens in tactic positions** anywhere in the project.

For an annotated walkthrough of every lemma plus an empirical comparison
against ground-truth `P(m,n)` from the Rust DP, see `EVIDENCE.md`.

## Problem

This project analyzes the **full-degree spanning tree problem** on grid
graphs. The grid graph `G(m, n)` has `m × n` vertices in an orthogonal grid,
with edges between vertices that are immediately adjacent horizontally or
vertically. Given a spanning tree `T ⊆ G(m, n)`, a vertex `v` is *full-degree*
(synonymously, *preserved*) if `deg_T(v) = deg_G(v)`. We write `P(m, n)` for
the maximum number of full-degree vertices over all spanning trees of
`G(m, n)`.

The Lean lemmas listed below formalize the algebraic bound *expressions*
`basicUB`, `refinedUB`, `lowerB` and the deficiency identity
`D(m, n) = 2(m-1)(n-1)` that constrain `P(m, n)`. The operational connection
(`P(m, n) ≤ basicUB m n`, an explicit construction reaching `lowerB m n`,
etc.) is in the deferred-work list.

## Proved (sorry-free)

### `GridGraphs/Defs.lean`
- `numEdges_eq`: `numEdges m n = m*(n-1) + n*(m-1)`.
- `succ_mul_succ_sub_one`: `(a+1)*(b+1) - 1 = a*b + a + b`.
- `deficiency_succ_succ`: `deficiency (m+1) (n+1) = 2*m*n`.
- `deficiency_closed_form`: `deficiency m n = 2*(m-1)*(n-1)`.
- `gridGraph`: a real `SimpleGraph (Fin m × Fin n)` with proven `symm` /
  `loopless` fields.
- `Fintype (GridVertex m n)`, `DecidableEq (GridVertex m n)`, and
  `gridGraph_decidableRel`: instances enabling `(gridGraph m n).degree`.
- `gridDegree m n v := (gridGraph m n).degree v`: the actual grid-graph
  degree, replacing the previous stub.
- `isPreserved m n T v`: `T.degree v = (gridGraph m n).degree v` for a
  decidable subgraph `T`. Replaces the `True`-stub.
- `vertexDeficiency m n T v`: `(gridGraph m n).degree v - T.degree v`.
- `numPreserved m n T`: cardinality of the preserved-vertex `Finset`.
- `verts_partition`: `numCorners m n + numBorderNonCorner m n + numInterior m n = m * n`.
  Pure arithmetic case-analysis on the `{0, 1, ≥2}` shape of `m, n`.

### `GridGraphs/Bounds.lean`
- Definitions of `D`, `I`, `ceilDiv3`, `basicUB`, `refinedUB`, `lowerB` matching
  `docs/DERIVATION.md`.
- `ceilDiv3_mul_ge`, `ceilDiv3_mul_le`, `ceilDiv3_mono`, `ceilDiv3_three_mul`:
  basic algebraic properties of integer ceiling division by 3.
- `D_eq_deficiency`: bridges the algebraic `D` and the operational
  `deficiency` from `Defs.lean`.
- `D_expand`, `D_le_three_mn`: polynomial expansion and a useful upper bound
  for `D` when `m, n ≥ 1`.
- `basicUB_le_mn`, `ceilDiv3_D_le_mn`: range bounds.
- `D_4n`, `basicUB_4n`, `I_4n`, `refinedUB_4n`, `refinedUB_lt_basicUB_4n`:
  closed forms on the `4 × n` family. These match the Rust regression test
  `refined_expected_4xn_pattern`.
- `lowerB_le_basicUB`: `m + n − 1 ≤ basicUB m n` (`m, n ≥ 1`).
- `refinedUB_le_basicUB`: `refinedUB m n ≤ basicUB m n` (`m, n ≥ 1`). Matches
  the Rust assertion in `refined_never_worse_and_valid`.

### `GridGraphs/Forced.lean`
- `forcedEdgeGraph G F`: the graph of all `G`-edges incident to at least one
  vertex of `F`.
- `preservesIncidentEdges G T v`: edge-containment formulation of a vertex being
  full-degree/preserved in `T` relative to `G`.
- `forcedEdgeGraph_le_of_preserves`: if every vertex of `F` preserves all
  incident `G`-edges in `T`, then `forcedEdgeGraph G F ≤ T`.
- `forcedEdgeGraph_isAcyclic_of_preserves`: if `T` is acyclic, then the forced
  graph of any such `F` is acyclic.
- `forcedEdgeGraph_isAcyclic_of_preserves_tree`: same corollary for `T.IsTree`.
- `grid_forcedEdgeGraph_isAcyclic_of_preserves`: grid-graph specialization of
  the acyclicity lemma.

### `GridGraphs/Diagonal.lean`
- `IsInducedEdgeDecyclingSet G U`: the named condition that deleting all
  edges internal to `U` leaves a forest, represented as acyclicity of
  `forcedEdgeGraph G Uᶜ`.
- `forcedEdgeGraph_compl_adj_iff`: the forced graph of `Uᶜ` consists exactly
  of the `G`-edges that are not internal to `U`.
- `compl_isInducedEdgeDecyclingSet_of_preserves`: the complement of any
  preserved/full-degree set in an acyclic graph is an induced-edge decycling
  set.
- `fourCycle_has_unforced_edge`: in any acyclic forced-edge graph, a genuine
  4-cycle must have at least one unforced boundary edge, i.e. an edge whose
  two endpoints both lie outside the full-degree set.
- `cell00`, `cell01`, `cell11`, `cell10`: the four vertices of a grid unit
  cell, indexed by `Fin (m-1) × Fin (n-1)`.
- `gridGraph_cell_adj_top`/`_right`/`_bot`/`_left`: the four boundary edges
  of any grid unit cell are `gridGraph` edges.
- `cell00_ne_cell11`, `cell01_ne_cell10`: the two diagonal disequalities,
  needed to invoke `fourCycle_has_unforced_edge` on a cell.
- `grid_cell_has_unforced_edge`: every grid unit cell in an acyclic forced-edge
  graph has at least one boundary edge whose endpoints both lie outside the
  full-degree set.
- `grid_cell_has_unforced_corner`: vertex-form corollary—every grid unit cell
  contains at least one corner outside the full-degree set.
- `preserved_set_cell_corner`: spanning-subgraph specialisation—the set of
  full-degree vertices in any acyclic subgraph misses at least one corner of
  every unit cell.
- `connected_graph_has_spanning_tree`: any finite connected graph has a
  spanning tree subgraph (wrapper around mathlib's `Connected.exists_isTree_le`).

### `GridGraphs/Spanning.lean` — refined upper bound (Phase 8.refined)
- `isCornerVertex`, `isBorderVertex`, `isInteriorVertex`: vertex-class
  predicates with decidability instances.
- `vertexClass_trichotomy`: every grid vertex is exactly one of corner /
  border / interior.
- `vertexDeficiency_le_of_corner`/`_of_border`/`_of_interior`: per-class
  deficiency caps (≤ 1 / ≤ 2 / ≤ 3) restated using the new predicates.
- `interior_card_eq`: the number of interior vertices in `Fin m × Fin n`
  equals `I m n`.
- **`preserved_le_refinedUB`**: for any spanning subtree `T`,
  `numPreserved m n T ≤ refinedUB m n`. Closes Phase 8.refined.
- `forall_spanning_subtree_preserved_le_refinedUB`: ∀-quantified form.

### `GridGraphs/ForestExtension.lean`
- **`SimpleGraph.isAcyclic_extends_to_isTree`**: any acyclic subgraph
  `F ≤ G` of a finite connected graph extends to a spanning tree of `G`.
  Generalises mathlib's `Connected.exists_isTree_le` (which is the case
  `F = ⊥`). Reusable mathlib-style lemma; key input for converting the
  diagonal residue-1 forced forest to a spanning tree.

### `GridGraphs/DoubleComb.lean`
- `lBendForcedAdj` / `lBendForced`: the L-bend forced subgraph adjacency
  and `SimpleGraph` definition. Forces top-row + left-column preservation.
- `lBendForced_le_gridGraph`: the L-bend forced subgraph is contained in
  `gridGraph m n`.
- `topSpineColumnsAdj` / `topSpineColumns`: the simpler spanning-tree
  candidate (top row + every column).
- `topSpineColumns_le_gridGraph`: subgraph of `gridGraph`.
- `topSpineColumns_reachable_in_column`, `topSpineColumns_reachable_top_row`,
  `topSpineColumns_reachable_from_origin`: reachability lemmas.
- `topSpineColumns_preconnected`, `topSpineColumns_connected`: the
  candidate graph is connected for `m, n ≥ 1`.
- `topSpineColumns_degree_top`, `topSpineColumns_preserves_top_row`:
  every top-row vertex is preserved in `topSpineColumns m n`.
- **Deferred**: the IsTree proof (via edge count and
  `isTree_iff_connected_and_card`), the headline `lowerB_le_maxPreserved`,
  and the L-bend acyclicity argument that would yield the full `m + n − 2`
  lower bound. The infrastructure (definitions, connectedness,
  preservation lemma) is in place.

### `GridGraphs/Tests.lean`
- `decide`-based regression checks pinning Lean definitions of `D`,
  `basicUB`, `refinedUB`, `lowerB`, the vertex-class counts, and
  `uResidueOne k` cardinalities to specific small-grid values that match
  the Rust DP empirical data in `lean/results-empirical.csv`. A regression
  in any bound expression breaks the build.

### `GridGraphs/Spanning.lean` — operational upper bound `P(m, n) ≤ basicUB m n`

This module bridges the algebraic bound expressions in `Bounds.lean` to
the operational quantity `numPreserved m n T` for a spanning subtree `T`,
formalising Phase 8 of `docs/ROADMAP.md`.

**Box-product identification (Defs.lean):**
- `gridGraph_eq_boxProd`: `gridGraph m n = pathGraph m □ pathGraph n`.
- `gridGraph_connected`: connectivity for `m, n ≥ 1`, inherited from
  `pathGraph_connected` and `connected_boxProd`.

**Path-graph and grid-graph degree:**
- `pathGraph_degree_interior`, `pathGraph_degree_left_end`,
  `pathGraph_degree_right_end`, `pathGraph_degree_one`: closed forms.
- `gridGraph_degree`: `(gridGraph m n).degree v
    = (pathGraph m).degree v.1 + (pathGraph n).degree v.2`,
  via `degree_boxProd`.
- `gridGraph_degree_le_four`: every grid vertex has degree ≤ 4.
- `gridGraph_degree_corner` / `_border` / `_interior`: per-class closed
  forms (`= 2`, `= 3`, `= 4`) for `m, n ≥ 2`.
- `pathGraph_card_edgeFinset`: `#(pathGraph k).edgeFinset = k − 1`.
- `gridGraph_card_edgeFinset`: `2 * #(gridGraph m n).edgeFinset = 2 * numEdges m n`.

**Spanning-subtree predicate:**
- `IsSpanningSubtree G T`: `T ≤ G ∧ T.IsTree`.
- `IsSpanningSubtree.le`, `.isTree`, `.isAcyclic`, `.isConnected`,
  `.degree_le`, `.card_edgeFinset`, `.sum_degrees`: convenience accessors
  packaging the mathlib facts.

**Total deficiency identity:**
- `sum_gridGraph_degree`: `∑ v, (gridGraph m n).degree v = 2 * numEdges m n`.
- `total_deficiency`: `∑ v, vertexDeficiency m n T v = D m n` for any spanning
  subtree `T`.

**Per-vertex deficiency caps:**
- `tree_degree_pos`: `T.degree v ≥ 1` whenever `m * n ≥ 2`.
- `vertexDeficiency_le_three`: cap of 3 (basic).
- `vertexDeficiency_le_one_of_corner`: corner vertex cap of 1.
- `vertexDeficiency_le_two_of_border`: border (non-corner) vertex cap of 2.

**Headline operational upper bound:**
- **`preserved_le_basicUB`**: for any spanning subtree `T` of `gridGraph m n`,
  `numPreserved m n T ≤ basicUB m n`. Phase 8 from `docs/ROADMAP.md`.
- `forall_spanning_subtree_preserved_le_basicUB`: ∀-quantified form.

### `GridGraphs/ResidueOne.lean`
- `isInUResidueOne k r c`: predicate defining the residue-1 non-full set
  `U` of the `(3k+1) × (3k+1)` grid (cf. `analysis/diagonal_patterns.py`'s
  `residue_one_pattern`).
- `uResidueOne k : Finset (GridVertex (3*k+1) (3*k+1))`: the corresponding
  `Finset`.
- `uResidueOne_card`: `|uResidueOne k| = 6 * k^2 + k + 1` for `k ≥ 1`.
  This is the cardinality half of Proposition L1 from
  `analysis/proofs_diagonal.md`. The acyclicity / forest-extension half
  (proving the forced-edge graph of `(uResidueOne k)ᶜ` extends to a
  spanning tree achieving `n² − |U|` full-degree vertices) is **not** in
  this file; it depends on the still-open dual-equivalence and
  forest-extension theorems documented in `analysis/proofs_diagonal.md`.
- `q n`: the conjectured diagonal closed-form `q`-formula.
- `uResidueOne_card_eq_q`: the proven cardinality equals `q (3k + 1)`.
  Cross-link to `analysis/proofs_diagonal.md` and
  `analysis/check_diagonal_patterns.py`, which empirically verifies the
  forest-extension half of L1 for every `n = 3k+1` in `[4, 40]`.

## Not proved (deferred — see notes)

These statements would connect the bound *expressions* in `Bounds.lean` to the
operational quantity `maxPreserved m n` = `P(m, n)`, the maximum number of
full-degree vertices over all spanning trees of `gridGraph m n`. Each
requires building a real spanning-tree predicate and a per-vertex degree
function on the tree:

- The headline lower-bound theorem `lowerB m n ≤ maxPreserved m n` (i.e.
  there exists a spanning subtree with `numPreserved ≥ m + n − 2`). The
  L-bend forced subgraph is defined and shown to be a subgraph of the
  grid graph in `DoubleComb.lean`; its acyclicity proof and the
  forest-extension application remain.
- Cardinality consequence of the forced-edge lemma: `P(m,n)` is bounded above by
  the maximum cardinality of a vertex set whose forced-edge graph is acyclic.
- Diagonal counting theorem: any induced-edge decycling set `U` in the square
  grid has at least the conjectured residue-class cardinality.
- Parametric diagonal lower-bound construction realizing the conjectured count.
- Forest-extension lemma preserving a specified forced forest while completing
  to a spanning tree. `connected_graph_has_spanning_tree` proves existence of
  some spanning tree in a connected graph, but not yet one containing all forced
  edges. This is the key remaining input for converting the proven
  `uResidueOne_card` into the operational lower bound on `P(3k+1, 3k+1)`.
- `lower_bound_construction`: an explicit "double-comb" spanning tree achieving
  `numPreserved ≥ m + n − 1`.
- The diagonal lower bound `maxPreserved (3k+1) (3k+1) ≥ (3k+1)^2 − (6k^2 + k + 1)
  = 3k^2 + 5k`, depending on the forest-extension lemma above to convert
  `uResidueOne_card` into a concrete spanning tree.

The previous version of this file claimed these were proven; in fact
`Bounds.lean` shipped them with `sorry` against a placeholder
`PreservedCount := 0`. That dishonest scaffolding has been removed.

## Empirical (Rust DP, ground truth)

`cargo test --release` from the repo root runs 5 tests that exhaustively
verify, for `1 ≤ m, n ≤ 9` (and the 4×n family up to `n = 10`), that

```
LB_simple ≤ P(m,n) ≤ refinedUB ≤ basicUB
```

where `P(m,n)` is the exact maximum, computed by the DP in `src/main.rs`.

The full `1 ≤ m, n ≤ 10` table (CSV at `lean/results-empirical.csv`) is
reproduced in `EVIDENCE.md`. All 100 rows respect the bound chain; 19 rows
have `P = refinedUB` (refined bound is tight); the average gap
`basicUB − P` is 2.38.

## Next Steps

1. Complete the double-comb lower bound: prove `topSpineColumns m n` has
   exactly `mn − 1` edges (via degree-sum), then conclude `IsTree` via
   `isTree_iff_connected_and_card`. Then state the headline existence
   theorem: `∃ T, IsSpanningSubtree (gridGraph m n) T ∧ n ≤ numPreserved`.
   This gives a partial lower bound (matching the `LB_simple = max(m, n)`
   column of the empirical CSV).
2. Stronger lower bound `m + n − 2` via the L-bend forced subgraph plus
   `isAcyclic_extends_to_isTree`. Requires proving the L-bend is acyclic.
3. Acyclicity of the residue-1 forced-edge graph (the hard half of
   Proposition L1 in `analysis/proofs_diagonal.md`). Combined with
   `isAcyclic_extends_to_isTree` and `uResidueOne_card`, this would yield
   the formal diagonal residue-1 lower bound.
