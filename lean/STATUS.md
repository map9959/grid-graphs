# Proof Status

This file is the authoritative ledger of what is and isn't formally proven in
the Lean project. The last successful full build was on Lean 4.24.0-rc1.

Toolchain update, 2026-09-05: Lean and mathlib are pinned to 4.33.1. The
boundary/test dependency chain has been ported and
`lake build GridGraphs.BoundaryFiveConstruction GridGraphs.Tests` passes (8,732
jobs). Further graph, contour, and construction modules exposed by full builds
were also ported and checked individually. Full-library validation now runs in
the background without a time limit, at the user's request. Its log and final
exit status are `/tmp/opencode/grid-graphs-library-verification.log` and
`/tmp/opencode/grid-graphs-library-verification.exit` for the first pass, which
finished with exit 1. All reported modules subsequently passed direct source
checks. Fixed-entry kernel `decide` replay replaces broad simplification in
the existing certificates for sides 8,9,11,12,14,15,17,18,20; no certificate
data or theorem statements changed. The fresh unrestricted pass uses
`/tmp/opencode/grid-graphs-library-verification-retry.log` and
`/tmp/opencode/grid-graphs-library-verification-retry.exit`.
No full-library success is claimed yet. The historical ledger
below is not a claim that every module has been rechecked on 4.33.1. No global
backward flags or proof placeholders were added.

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

The Lean lemmas listed below formalize the operational spanning-tree bounds,
the cotree incidence-waste ledger, and the exact forced-forest component
reduction, in addition to the algebraic bound expressions.

## Proved (sorry-free)

### Improved Residue-Two Staircase (Lean 4.33.1)

`ResidueTwoStaircase.lean` defines the actual family in ambient coordinates,
proves disjointness of its centers, placement in the twice-cropped square, and
the exact inner count `3s^2+(s+1)/2` for s>=2.

`ResidueTwoStaircaseForest.lean` proves the interval forests and all required
physical support intersections, then glues the baseline and added stars to the
canonical frame. Its `Ffull_isAcyclic` is unconditional for s>=2. The final
`residueTwo_le_maxPreserved` proves

```text
3k^2+6k+2+k/2 <= maxPreserved (3k+2) (3k+2),    k>=3.
```

The only hypothesis is the stated arithmetic range. No missing connectivity
or attachment assumption is hidden in this result. This improves the affine
bound for k>=8 but does not prove the conjectured optimum.

### Canonical Boundary-Five Extension (2026-09-05, Lean 4.33.1)

`BoundaryFiveFrame.lean` defines the actual five-hole boundary pattern. It
proves exact support, unique next-ring spokes, the isolated vertex `(1,2)`,
and unconditional `Houter_isAcyclic` and `support_isTree`. The full ambient
graph still includes isolated deep vertices; only its support is one tree.

`BoundaryFiveAttachment.lean` proves `Houter_sup_isAcyclic_iff`: for any inner
graph J with all edges in the once-cropped square, its union with the frame
is a forest iff J is a forest and no J-component joins two distinct attachment
vertices. Isolated and unattached components are permitted.

`BoundaryFiveConstruction.lean` instantiates the iff with a concrete preserved
set A in the twice-cropped square, proves the extension cardinality
`4n-9+A.card`, and transfers it to `maxPreserved`. Its
`residueTwo_le_maxPreserved` remains conditional on an actual A of size
`3k^2-5k+1` and the proved interface's acyclicity/attachment hypotheses.
No target-count family A is defined or asserted to exist.

All three modules and the regression tests pass together (8,732 jobs).
The frame, attachment iff, count, and bound-transfer axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound`. The arbitrary-b=5 normalization
and the Q reformulation on a separate smaller vertex type remain partly
paper-level; they are not needed to use this canonical lower construction.

### `GridGraphs/BoundaryFiveEquality.lean` (2026-09-05, Lean 4.33.1)

- `boundaryDeficiencySum_compl_eq_five_corners_and_card`: for n>=6 and feasible
  F with complement boundary deficiency five, all corners are in F and exactly
  five boundary vertices are outside F.
- `boundaryDeficiencySum_compl_eq_five_witness_decomposition`: four independent
  corner witnesses plus one extra boundary vertex, with its neighbor restriction.
- `boundaryDeficiencySum_compl_eq_five_unique_perimeter_edge`: exactly one
  unordered perimeter edge has both endpoints outside F.
- `boundaryDeficiencySum_compl_eq_five_no_boundary_distance_two`: for n>=7,
  same-side vertices two grid steps apart cannot both lie outside F.
- `boundaryDeficiencySum_compl_eq_five_next_ring_notMem`: for n>=7 the entire
  next ring lies outside F, including its corners.

The module is imported by the root and tests. Targeted builds pass on 4.33.1;
all five axiom audits report only `propext`, `Classical.choice`, and `Quot.sound`.
The canonical frame and attachment results are now checked as above. The full
arbitrary-configuration normalization and deep-square Q reformulation remain
partly paper-level.

### `GridGraphs/BoundaryFiveBudget.lean` (2026-09-05)

- `five_le_boundaryDeficiencySum_compl`: every feasible forced set on a square
  of side at least five has complement boundary deficiency at least five.
- `induced_components_le_three_mul_add_six`: a feasible set of cardinality
  `3*k^2+7*k` on side `3*k+2` has at most `3*k+6` induced components.
- `not_feasible_target_of_four_mul_le_components`: excludes at least `4*k`
  induced components at that target for `k>=7`.
- `not_feasible_target_of_four_mul_add_one_le_components`: excludes at least
  `4*k+1` induced components at that target for `k>=6`.

The module is imported by the root library. `Tests.lean` includes symbolic
specializations at sides 23 and 20; no grid enumeration is involved. Targeted
build and full `LEAN_NUM_THREADS=2 timeout 90s lake build` passed (7,521 jobs).
The four axiom audits report only `propext`, `Classical.choice`, and `Quot.sound`.
The budget module has also been rechecked on 4.33.1. Equality geometry and
next-ring exclusion, the canonical frame, and its two-way attachment criterion
are now formalized as above. The scope limits for the full peeling statement
are recorded in `analysis/BOUNDARY_FIVE_PEELING.md`.

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

### Incidence waste and component ledgers
- `GridGraphs/IncidenceWaste.lean` defines `supportFinset`, `newSupport`,
  `lostSupport`, and `incidenceWaste` for finite simple graphs.
- `incidenceWaste_add_twice_card_edges` proves
  `W + 2|E| = 3|support|` under the degree-three cap.
- `incidenceWaste_exchange_balance` and `incidenceWaste_int_delta` prove the
  exact arbitrary equal-edge exchange formula, including shared endpoints and
  multi-edge exchanges.
- `GridGraphs/ForestLedger.lean` proves
  `|E(H)| + c(H) = |V(H)|` for every finite acyclic simple graph.
- `GridGraphs/ForcedForestLedger.lean` instantiates this identity for the
  ambient forced forest and for the induced graph on the forced-vertex subtype.
- `GridGraphs/ComponentReduction.lean` proves restricted handshaking and the
  exact subtraction-free component identity. Its square `U`-form is
  `square_grid_component_reduction_compl`.
- `grid_prefix_component_ledger` gives the exact subtraction-free row-prefix
  charge identity; the remaining universal bound is the terminal
  boundary/component inequality, not an unidentified additive potential.
- `GridGraphs/CotreeWaste.lean` identifies the support and degrees of
  `gridGraph m n \ T` with non-preserved vertices and deficiencies, and proves
  `W + D + 3*numPreserved = 3mn`.
- `diagonal_cotree_incidenceWaste_ge_iff_preserved_bound` formally identifies
  the open diagonal waste bound with the full-degree spanning-tree bound.
- `GridGraphs/TreeComponentBridge.lean` proves that the full-vertex forced
  graph attached to a cotree support is acyclic and that its square component
  charge is exactly `incidenceWaste + 2`.

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
- `grid_tree_cotree_support_row_or_column_coverage`: the cotree support of a
  square grid spanning tree meets every row or meets every column. Missing one
  of each would contradict the complete supported-side theorem at their
  intersection cell. Axis coverage alone does not prove universal waste; the
  direct run-incidence route still needs a cycle-rank/projection inequality.
- `grid_cell_has_unforced_corner`: vertex-form corollary—every grid unit cell
  contains at least one corner outside the full-degree set.
- `preserved_set_cell_corner`: spanning-subgraph specialisation—the set of
  full-degree vertices in any acyclic subgraph misses at least one corner of
  every unit cell.
- `connected_graph_has_spanning_tree`: any finite connected graph has a
  spanning tree subgraph (wrapper around mathlib's `Connected.exists_isTree_le`).

### `GridGraphs/GridDual.lean`
- `GridFace`, `HorizontalGridEdge`, `VerticalGridEdge`: explicit rectangular
  grid faces and oriented primal-edge coordinates.
- `horizontalDualEndpoints`, `verticalDualEndpoints`: the two faces across each
  primal edge, matching the executable Python dual convention.
- `uuDualGraph U`: the dual graph generated by primal edges internal to `U`.
- `uuDualGraph_adj_iff`: exact adjacency characterization with both primal
  endpoints in `U`.
- `hasDualEndpoints_iff`: transports same-side predicates across unordered dual
  endpoints.
- `gridGraph_adj_exists_coordinate_edge`: every abstract `gridGraph` adjacency
  is represented by a horizontal or vertical coordinate edge, up to endpoint
  orientation.
- `cycleComplementDualGraph c`: face graph using exactly the primal edges not
  traversed by `c`; `cycleInteriorFaces c` is the finite set of faces not
  reachable from `out` in this graph.
- `out_not_mem_cycleInteriorFaces`,
  `horizontal_mem_cycleInteriorFaces_iff_of_not_mem_edges`, and its vertical
  counterpart: the unreachable-face set excludes `out` and is unchanged across
  every primal edge outside the cycle.
- `horizontal_not_mem_forcedCycle_edges` and its vertical counterpart: a U-U
  edge cannot be traversed by a walk in the forced graph of `Uᶜ`.
- `reachable_mem_iff_of_respectsCut`, `not_connected_of_respectsCut`: a walk
  cannot cross a respected vertex cut, so a connected graph cannot respect a
  nontrivial cut.
- `GridCycleEnclosesBoundedFace`: enclosure proposition at the reachability
  layer; `gridCycleRowRayParity` proves it via explicit row-ray parity.
- `rowRayCrossingEdges`, `FaceRowRayOdd`: explicit finite leftward-ray crossing
  count and its oddness predicate (`out` has parity zero).
- `walkCutCrossings`, `even_walkCutCrossings_iff`, and
  `even_walkCutCrossings_of_isClosed`: a walk crosses a Boolean vertex cut
  evenly exactly when its endpoints lie on the same side; every closed walk
  therefore has even cut-crossing count.
- `gridRowPrefixSide`, `gridColumnPrefixSide`,
  `even_gridRowPrefix_crossings`, and `even_gridColumnPrefix_crossings`: grid
  row/column prefix specializations of closed-walk cut parity.
- `gridCycle_even_incident_edges`: every vertex has even incidence count in a
  grid cycle's edge list, via mathlib's trail incidence theorem.
- `gridCycleRowRayParity`: every simple grid cycle has an odd face, and every
  unused horizontal or vertical primal edge has incident faces of equal
  row-ray parity. The proof identifies trail `countP` filters with explicit
  `rowRayCrossingEdges` cardinalities and handles all grid boundaries.
- `cycleComplementDualGraph_respects_faceRowRayOdd` and
  `gridCycleEnclosesBoundedFace_of_rowRayParity`: parity is invariant along
  complement-dual walks, so an odd face is unreachable from `out`.
- `gridPrimalCycleFaceCut_of_cycleEnclosesBoundedFace`: constructs the required
  finite face cut from unreachable faces and proves all U-U same-side clauses.
- `gridPrimalCycleFaceCut_of_rowRayParity`: direct parity-to-face-cut reduction.
- `uuDualGraph_respectsCut`: the horizontal/vertical same-side conditions imply
  that the U-U dual respects the face cut.
- `gridDualCycleSeparation_of_primalCycleFaceCut`: sorry-free reduction of the
  finite cycle-face-cut proposition to `GridDualCycleSeparation`.
- `gridDualCycleSeparation_of_cycleEnclosesBoundedFace`: direct composition from
  the enclosure proposition to `GridDualCycleSeparation`.
- `gridDualCycleSeparation_of_rowRayParity`: direct composition from the sole
  row-ray arithmetic proposition to `GridDualCycleSeparation`.
- `gridDualCycleSeparation`: unconditional rectangular-grid primal/dual cycle
  separation.
- `isInducedEdgeDecyclingSet_of_uuDual_connected` and
  `exists_isTree_preserving_compl_of_uuDual_connected`: proved conditional
  theorem chain from cycle separation to a preserving spanning tree.
- `exists_isTree_preserving_compl_of_uuDual_connected_grid`: unconditional
  preserving-tree endpoint from U-U dual connectivity and grid connectivity.

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
- `q n`: the revised piecewise candidate diagonal `q`-formula.
- `uResidueOne_card_eq_q`: the proven cardinality equals `q (3k + 1)`.

### Operational maximum and diagonal constructions
- `GridGraphs/MaxPreserved.lean` defines the finite spanning-subtree set,
  `preservedScore`, and the operational maximum `maxPreserved m n`.
- Every witness is bounded by `maxPreserved`; every universal tree bound bounds
  it; and a maximizing tree exists for nonempty grids.
- `maxPreserved_le_basicUB` and `maxPreserved_le_refinedUB` connect the existing
  operational upper bounds to the maximum.
- `ForcedMaximum.lean` defines `maxForcedAcyclic`, the maximum cardinality of a
  vertex set whose complete incident-edge graph is acyclic, and proves
  `maxPreserved = maxForcedAcyclic` on every nonempty grid. Thus constructions
  and upper bounds may work directly with forced forests without choosing a
  spanning tree.
- `WidthFourLower.lean` proves that the two outer rows of a `4 x n` grid force
  two disjoint acyclic combs and therefore give `2n` preserved vertices.
  `WidthFourExact.lean` proves the matching checkerboard-waste upper bound and
  the unconditional exact theorem `maxPreserved 4 n = 2n` for every `n>=2`.
- `GridGraphs/ResidueOneDual.lean` proves
  `uuDualGraph_uResidueOne_connected`, forced-complement acyclicity, and a
  preserving spanning-tree witness for every `k>=1`.
- `GridGraphs/ResidueOneMax.lean` proves the unconditional lower bound
  `3k^2+5k <= maxPreserved (3k+1) (3k+1)` and the exact residue-one value
  conditional only on the universal incidence-waste bound.
- `GridGraphs/ResidueZero.lean` encodes the recursive phase family for `k>=7`
  and proves its exact cardinality `6k^2-3k+2`.
- `ResidueZeroTransitions`, `ResidueZeroWord`, `ResidueZeroFrontier`, and
  `ResidueZeroCaps` prove the six symbolic transition classes and their local
  frontier/cap attachment lemmas.
- `ResidueZeroBase`, `ResidueZeroPersistent`, and the slab/bridge/local-geometry
  modules prove the explicit `B_7` base, persistent successor step, dual
  connectivity, and the unconditional target lower bound for every `k>=7`.
- `ConstructionCertificate.lean` supplies the reusable ranked-parent
  connectivity certificate and its generic `maxPreserved` consequence.
- `FiniteDiagonalConstructions.lean` and the width-specific finite modules
  prove target lower bounds at `n=3,5,6,8,9,11,12,14,15,17,18,20`, using
  explicit row masks, parent/rank tables, and symbolic U-U dual edges.
- `GridGraphs/DiagonalUpper.lean` proves all four residue-wise operational upper
  bounds from the named waste/equality exclusions.
- `PerimeterWaste.lean` proves unconditionally that cotree incidence waste is
  at least three in residue one and at least four in residues zero and two,
  together with the resulting improved `maxPreserved` upper bounds.
- `LinearWaste.lean` proves the exact four-side decomposition of boundary
  deficiency and reduces `W>=n` to `n+2 <= fourSideComponentRank`; this final
  growing component-rank inequality remains open.
- `DiagonalUpperResidue.lean` replaces the global upper assumptions by minimal
  residue-local requirements. In residues one and two, a linear `W>=n` theorem
  automatically upgrades to `W>=n+2` by the exact cotree congruence.
- `ChannelContourRouting.lean` routes exits separately and merger slots plus
  roots jointly into the exact contour ledger. `ChannelMergerResources.lean`
  now composes its internal-edge/preserved-component factorization directly
  with this routing theorem. `GridChannelContourRealization.lean` packages the
  complete realization interface and proves that any realization gives
  `W>=n+2`. Direct boundary exits are separated from continuing demands, so an
  empty continuing forest is allowed when cotree support covers every vertex.
- `CanonicalShoreGerms.lean` constructs the `n+3` distinct side-labelled
  boundary germs, classifies support-based direct exits, and embeds them into
  actual split outer ports. `GridShoreChannelForest.lean` now constructs the
  unique immediate-supershore parent forest. `CanonicalShoreContinuation.lean`
  constructs retained inward tree edges and launched shores.
- `CanonicalShoreForest.lean` constructs the launched ancestor closure with
  private demand leaves, proves every merger-excess slot has a distinct
  physical child, and jointly embeds merger-child and maximal-root attachment
  edges into the spanning tree.
- `CanonicalChannelRealization.lean` packages a conditional exit-free
  prototype and proves `CanonicalTerminalResources` would yield `W>=n+2`. The
  condition is equivalent to the cardinal bound from `MergerSlot + roots` into
  internal support-support tree edges plus preserved components, but it is not
  universal because the prototype discards supported boundary exits met after
  launch.
- Edgewise noninternal-terminal injectivity is not a valid remaining target:
  distinct selected tree edges may meet the same support-free component. The
  remaining channel theorem must retain later split-outer exits and globally
  route first terminal events into unused boundary sectors, internal
  support-support tree edges, and preserved components without reuse.
- The stronger claim that every collision of current canonical roots can be
  discharged afterward is also false. An explicit `3 x 3` tree has two
  maximal-shore roots at distinct tree edges entering the same support-free
  component, no internal support-support tree edge, and no later exit in the
  exit-free prototype. A valid construction must assign actual split-outer
  ports and truncate before those maximal roots are formed.
- `TerminalCarrierQuotientRouting.lean` formalizes the exact collision ledger.
  For an injectively labelled family of physical terminal tree edges, internal
  tokens reserve their physical internal edges and one representative per
  noninternal carrier class reserves its component. Only labelled duplicate
  carrier contacts remain. `PhysicalTreeTokenQuotientRouting.resourceEmbedding`
  reconstructs the complete terminal resource embedding from a complementary
  embedding of those collisions, and
  `nonempty_physicalTreeTokenQuotientRouting_iff_card_le` gives its exact finite
  capacity criterion. The canonical forest is specialized by
  `CanonicalTerminalCollisionRouting`; no universal existence is claimed.
- `GridOuterPortContour.lean` refines every split outer port to the unique local
  clockwise tree-contour turn crossing its outward stub. The refined occurrence
  retains the crossed direction, so two corner incidences remain distinct.
- `GridExpandedContour.lean` expands the contour to every vertex/compass slot,
  proves explicit successor/predecessor inverses, proves first-return
  compression to the old dart contour, and proves the expanded permutation is
  one cycle for every nontrivial spanning square-grid tree.
- `ParentForestFirstStop.lean` and `MarkedCycleFirstStop.lean` formalize shared
  first-stop restriction. The latter proves that private starts are exactly all
  leaves, reached marks are exactly all roots, and merger slots inject into
  unmarked starts even when start paths share suffixes.
- `CanonicalExpandedContourForest.lean` launches all canonical demands on the
  expanded cycle. Direct demands start at their supported outward slot and
  continuing demands at their retained inward slot. Starts are injective,
  every orbit reaches a marked outer port, and reached exits embed injectively
  into actual split outer ports.
- `CanonicalExpandedCollisionRouting.lean` maps expanded merger slots to
  distinct unsupported canonical inward tree edges and packages both strict and
  port-aware quotient routings. The audit theorem
  `canonicalExpandedJointCollisionRouting_iff_incidenceWaste_ge` proves that
  the preferred residual routing is exactly equivalent to `W>=n+2`; it is not
  an independent geometric hypothesis. Row/column axis choice cannot change
  this deficit. A proof now requires a localized Hall relation that handles
  bare component-attachment branches nonlocally.
- Expanded merger ownership is now canonical and local to its stop interval;
  the earlier cardinality-chosen embedding remains only as a generic fallback.
  `RankedCarrierQuotient.lean` likewise selects the first contact with each
  component in expanded-contour order and retains later contacts as ordered
  collision labels.
- `LocalizedHallRouting.lean` proves the exact finite Hall equivalence and a
  disjoint-owner specialization. The remaining geometry must supply owner
  neighborhoods and one inequality per owner fiber.
- `RankedTransitionOwnership.lean` packages occurrence-indexed transition
  chains with strictly decreasing rank. Every state reaches a terminal
  occurrence with unchanged debt provenance; equal geometric transition labels
  are deliberately not quotiented when chains reconverge.
- `ReconvergenceLens.lean` identifies merger slots with occurrence-level lenses,
  selects the nearest later merger on each shared suffix, and proves strict
  stop-distance rank decrease, parent-forest well-foundedness, monotone origin
  provenance, strict containment of finite origin-occurrence regions, and a
  common reached marked stop along every parent edge.
  `CanonicalReconvergenceLens.lean` specializes this to the expanded grid
  contour: canonical collision occurrences embed into lenses, lenses retain
  injective physical tree-edge tokens, and parent lenses reach the same split
  outer cotree port. It also identifies the exact binary merger children as the
  private start at the merger slot and the distinct expanded-contour predecessor.
  Direct and shared branch germs distinguish retained darts, outer stubs, and
  in-place turns without inventing primal edges; edge-valued branch darts are
  distinct.
- `GridExpandedContourTrace.lean` projects every finite expanded-contour
  interval to an honest retained-tree walk by erasing in-place turns, and proves
  exact ordered dart and edge traces. Canonical lenses now expose shared-
  predecessor, shared-suffix, and conditional direct-inward walks with exact
  endpoints. Enclosed planar regions and laminarity remain open: retained-tree
  walks cannot themselves form a nontrivial cycle, so an offset/collar contour
  realization with boundary stubs is required.
- `GridExpandedContourCollar.lean` embeds expanded slots injectively as sector
  points in a fourfold rectangular collar and realizes every successor as a
  two-edge grid walk. Segment midpoints are injective and disjoint from all slot
  points; finite trace support is exact, and every slot-injective interval gives
  a collar `Walk.IsPath`. A complete-orbit `IsCycle` still needs the final
  undirected trail/closing-edge lemma, and a lens region still needs a second
  closing collar arc.
- The collar cycle and corrected planar hierarchy are now complete.
  `spanningTreeCollarCycle_isCycle` realizes the full contour orbit;
  `inwardShoreCollarCycle` closes a retained inward shore with an explicit
  edge-corridor chord and has a nonempty interior-face carrier. Because raw
  first-stop parents need not be geometrically nested, planar parents are the
  unique minimal strict supershores after orienting darts away from their common
  reached outer-port root. `canonicalUpperU1Default` packages occurrence
  assignment, laminar/disjoint regions, ranked parents, roots, and outer
  rank-zero degeneracies. U1 is complete using concrete shore-vertex regions.
- U2 defines actual exposed split-port, internal-edge, and selected free-
  component-contact resources. `CanonicalUpperU2ExposedOwnership` gives unique
  first owners and global injective forgetful embeddings; distinct owner fibers
  are disjoint. No capacity or matching theorem is hidden in this layer.
- U3 now has finite regional debt, passed-transition, and owned-resource types,
  exact sigma/cardinality ledgers, root cancellation, and a generic telescoping
  theorem. Leaves are discharged. Ranked first-difference shell traversal
  reduces the open local theorem to unary slot classification and genuine
  multi-child reconvergence; passed transitions retain origin multiplicity.
- The original all-crossing passed-transition census is now explicitly rejected:
  it forms a debt/edge Cartesian product and overcounts unresolved debt. The
  corrected `PlanarLensDebtRouting` keeps one active state and one optional
  selected transition per original merger slot. Local debt is exactly
  `Fin (mergerExcessAt region)`, and genuine reconvergences inject those debts
  into distinct immediate-child interface lanes without counting the retained
  attachment edges as resources.
- `PlanarLensTransportLabel` now includes cotree transitions, interface lanes,
  and parentless root escapes. Unary propagation contracts, selected parent
  passes telescope exactly once, and the finite root-escape system terminates at
  an occurrence-labelled geometric event while preserving debt provenance.
  Event occurrence is not physical payment.
- `canonicalPlanarLensDebtRouting` now constructs the corrected routing
  unconditionally. Its active fiber at a region is exactly the original merger
  slots born below that region. The exact flow equivalence splits this fiber
  into local births and occurrences arriving from one unique immediate child.
  Local births use their canonical merger lanes, inherited occurrences use the
  final child lane, and parentless occurrences use provenance-preserving root
  escapes. Thus all nonroot interface/pass obligations are discharged.
- Every planar merger debt now has a sound physical launch independent of the
  rejected root escape. `planarLensOriginalDebtImmediateChildEmbedding`
  globally selects distinct child occurrences, and
  `planarLensOriginalDebtFirstStopMergerEmbedding` sends them to distinct
  first-stop merger tokens. `planarLensOriginalDebtFullPrunedLaunchEmbedding`
  then performs the exact carrier split: one ranked representative may use its
  raw component, while every later same-component token remains an
  occurrence-labelled `FullPrunedOrderedCollision` for continued routing.
- Given a `FullPrunedRegionalCertificate`,
  `planarLensOriginalDebtPhysicalEmbedding` completes this launch into genuine
  raw ports, retained internal edges, or raw components. Its representative
  and collision equations are proved, and
  `rootActiveDebtFiberPhysicalEmbedding` supplies the corresponding injective
  map on each canonical root active fiber. This is global physical transport;
  it deliberately does not claim that a selected resource is first-owned at
  the terminal planar root.
- `CanonicalUpperU3ActiveDebtCertificate` and
  `CanonicalUpperU3TransportCertificate` isolate the sole remaining upper
  construction: inject active debts regionwise into first-owned raw physical
  resources plus selected parent passes. Root passes are empty. The corrected
  telescope and Hall theorem are proved, so U4 is complete conditional on this
  U3 certificate. Universal terminal freshness would be circular because
  complete residual routing is already equivalent to `W>=n+2`.
- `UniversalPrimalContourRouting.lean` proves the clean conditional U4 endpoint:
  an explicit canonical-demand embedding into `PrimalContourResource` gives
  `n+4 <= fourSideComponentRank` and hence universal waste. No bare cardinal
  inequality is accepted as a routing premise.
- `GridCrosscutCycle.lean` now proves exact edge-list formulas for finite
  boundary walks and clockwise outer arcs. Collar port indices are explicit on
  all four sides, and `outerEdgeAtPosition_mem_clockwiseOuterArc_iff_openCyclicSector`
  identifies closure-arc edges with the original open cyclic sector. The
  outer-edge dual-face classification, alternating path intersection, and
  boundary component nonalternation are now proved. They complete C1-C4 but do
  not imply the global-core root Hall theorem.
- `OrderedMultiHull.lean` proves that pairwise laminar ordered occurrence hulls
  can have arbitrary simultaneous depth. Consequently the concrete two-hull
  defect cannot be repaired by assuming a fixed hull bound from planarity or
  laminarity alone.
- `BareCombTransition.lean` formalizes all four orientations of the bare-comb
  conservation move. Distinct gaps inject into internal support-support edges
  or labelled cotree transitions. Local debt is conserved, but transitions can
  propagate arbitrarily far and reconverge; no final-resource Hall theorem is
  yet proved.
- `GridCellBoundaryEdges.lean` provides labelled cell-side edges, exact primal
  and dual endpoints, cotree support and dual adjacency, and retained internal-
  resource versus cotree classification. It also proves that every cell of a
  grid spanning tree supplies an internal resource or an exact labelled cotree
  transition on one of its sides.
- Component-local ordinary-gap geometry is now unconditional.
  `ordinaryGapBoundaryCellWitness` selects a unit segment between consecutive
  spatial contacts using straight-component interval closure, and its opposite
  cell side is a labelled cotree transition. Mixed-side and repeated-side cases
  require no `BareComb` premise. Ordinary and duplicated-corner occurrences keep
  their labels, so coordinate-edge collisions do not collapse transport states.
- Every full-pruned ordered collision now canonically determines its enriched
  contact, raw component, component-contour collision, component-spatial gap,
  ordinary/corner occurrence, and omitted transition. The generic ranked-
  collision transport is proved in `RankedCarrierQuotient.lean`; C5 no longer
  assumes a component-gap assignment or geometric edge injectivity.
- `canonicalComponentOmittedEdgeTransportPlacement` gives every omitted
  occurrence an unconditional relocated placement in the corrected shore
  forest. It chooses the outermost crossed supershore and passes to its immediate
  parent, or chooses a maximal parentless supershore for root escape. The
  transport region is therefore derived rather than fixed incorrectly at the
  launch occurrence.
- `FullPrunedCarrierBlockGapAssignment` is now unconditional bookkeeping; it
  contains no injection into the corrected planar shore forest. Its component,
  spatial gap, and omitted edge are derived directly from each inward collision.
  The earlier injection target was false in the one-root contact-tree case:
  leaves are paid by roots plus branch excess, not by branch excess alone.
  The later component-split cotree-dual forest is retained as legacy audit/Euler
  scaffolding. Its component-copied continuation roots and branch excess are not
  independent physical payment.
- Full-pruned collisions are formally partitioned into disjoint inward- and
  outer-direct subtypes. Inward collisions have a canonical injective launch
  occurrence with the exact merger-slot equation. For an outer collision, the
  direct port equals the reached `lensOuterPort`, belongs to the reserved
  `exitEmbedding` range, and cannot inhabit `UnreservedCanonicalBoundaryPort`.
  This is a source partition, not a payment theorem; the grouped C5 construction
  must route only the inward residual source and leave reserved outer exits out
  of the residual resource pool.
- The collision partition is now an explicit equivalence
  `FullPrunedOrderedCollision ≃ FullPrunedInwardCollision ⊕
  FullPrunedOuterCollision`, with the corresponding cardinal identity. Outer
  collisions are not cancellation credits: their direct ports are reserved, so
  they remain obligations requiring separate residual routing. The sound grouped
  ledger keeps unreserved root ports, reserved inward-root routing, outer-
  collision routing, and branch ownership pairwise disjoint in the same genuine
  residual resource pool.
- The legacy component cotree-dual forest no longer uses only the one omitted
  transition selected by each inward collision.  Each raw-component fiber now
  has a provenance-preserving occurrence universe containing every component
  spatial-gap occurrence and a continuation occurrence for every genuine
  grid-cotree edge.  Selected starts map to their exact gap occurrence and
  embed as private leaves.
  Its tree-cotree boundary connectivity and root classification are proved.
  Global-core correction nevertheless supersedes it: copying that complete
  continuation universe into every component fiber duplicates the same physical
  boundary occurrence, so private roots and merger slots cannot be paid
  componentwise.
- `ComponentResolvedBoundaryGapHullExpansion` and
  `CanonicalGroupedResidualHullExpansion` are legacy Hall-strength witness
  propositions, not consequences of hull topology. The associated arbitrary
  first-separator/outer classifications and reserved-root launch type remain for
  build compatibility and audit only.
- The former corrected endpoint `CanonicalUpperU3RootHall` keeps one
  global escape core and original debt provenance. The concrete shared carrier
  is `FullPrunedSharedCotreeDualEdgeOccurrence` with
  `fullPrunedSharedCotreeDualForest`: selected gaps remain private provenance
  occurrences, but each actual continuation transition occurs once globally.
  `RootDebtCanUse` requires a reached raw resource and a first-owned witness at
  the same root. The exact blocker is Hall for `rootRawNeighborhood`:
  termination, nonalternation, and component quotienting do not prove freshness
  or injectivity. For `canonicalPlanarLensDebtRouting`, the theorem
  `canonicalUpperU3_activeGlobalHall_of_canonicalRootHall` proves that this root
  Hall statement alone implies active global Hall; the nonroot transport is no
  longer an input. However, the endpoint audit is now complete and rejects this
  root Hall statement as the final route: `rootDebtCanUse_eq_outerPort` proves
  that the current escape system never exposes internal edges or components,
  `canonicalRootRawNeighborhood_card_le_one` proves every canonical root
  neighborhood is empty or a singleton, and
  `canonicalUpperU3RootHall_activeFiber_card_le_one` proves Hall would force at
  most one accumulated debt per root. A replacement root transport must expose
  genuine internal-edge and raw-component events before applying Hall.
- The newer active C5 endpoint supersedes that root-Hall decomposition with the
  one-copy global shared cotree core and `SharedCanonicalGroupedResidualHall`.
  `SharedCanonicalGroupedResidualGeometry` reduces it classwise to reserved-port
  provenance routing, routing on the actual global merger slots, outer routing,
  and pairwise separation of the three selected images. Unused candidate
  neighborhoods may overlap; whole-neighborhood disjointness and singleton
  outer neighborhoods were stronger than composition requires. Earlier component-refined
  multiplicity quantified the product of every slot with every component below
  its branch vertex, although the grouped ledger contains only one demand per
  slot; nested combs show that stronger product is not the right obligation.
  The unresolved mathematical bridge is exactly downstream physical-union
  capacity for the real merger slots, including repeated same-component stops.
- `CheckerboardColorWaste.lean` proves exact black/white cotree degree and waste
  ledgers plus residue-two tight/near color normal forms.
  `CheckerboardContourMarks.lean` realizes those color wastes as actual color
  subtypes of `CotreeContourMark`.
- `CanonicalDemandPhase.lean` proves the `Fin 3` phase counts, six phase/color
  histograms by parity, and exact provenance sums over expanded-contour exits.
  `ResidueTwoColorCapacity.lean` derives tight anchor/color rigidity and the
  near-tight one-packet alternatives from any color-preserving anchored
  marking. No universal such marking or residue-two contradiction is claimed.
- `ChannelContourRouting.lean` now proves the corrected abstract pruning
  theorem `incidenceWaste_ge_of_prunedRootChannelRoutingWithDirectExits`.
  Later exits must be roots, demand vertices must be leaves, and only
  `MergerSlot + (roots \ exits)` consumes internal-edge/component resources.
  `GridChannelContourRealization.lean` uses this non-double-counting interface.
- `ConnectivityTransport.lean` proves that path-valued adjacency maps preserve
  connectivity when every target vertex attaches to the source image. The
  exact and affine residue-two step modules use this common abstraction.
- `ResidueTwoAffine.lean` proves the symbolic affine family has cardinality
  `6k^2+6k-1` and increment `12k+12`. `ResidueTwoAffineStep.lean` proves its
  `n=17` base connectivity and now discharges all old-edge transport and
  successor-face attachment obligations symbolically.
- `ResidueTwoAffineMax.lean` now records the exact construction deficit: the
  affine score plus `k-5` is the stable target, and one affine pump gains
  `6k+9` preserved vertices versus the required `6k+10`.
- The affine successor API now includes two symbolic occurrence embeddings:
  one moves the final old pumped block past the insertion and one keeps an old
  copy in the newly inserted position. `residueTwoAffineStepVertex_mem` proves
  every old `U` vertex survives under the moved-block embedding.
- `ResidueTwoAffineStep.lean` now proves old-face preimages and transports every
  interior or boundary old dual edge, including the genuine row/column seam
  paths, and attaches every face in the inserted slabs. Consequently
  `uResidueTwoAffine_dual_connected` holds for every `k>=5` without generated-
  board enumeration. `ResidueTwoAffineMax.lean` packages the unconditional
  lower bound `3k^2+6k+5 <= P(3k+2)`.
- `IntervalStarGluing.lean` proves that two forests sharing at most one active
  support vertex have acyclic union, lifts this to indexed leaf-elimination
  orders, and identifies the resulting graph with the forced graph of the union
  of all listed interval centers.
- `analysis/check_residue_two_counter_interval_surgery.py` verifies an abstract
  target-count edge-subdivision candidate: inserting one interval of length
  `k-5` between the affine root and boundary-spine branch gives `4k+1` nodes,
  target score `3k^2+7k`, a transported postorder, and step gain `6k+10`.
  Its two new attachment owners have no grid coordinates yet.
- `analysis/census_residue_two_counter_interval_geometry.py` completely rejects
  the candidate's declared natural corner grammar at `k=7,8,9`: all 7,912,264
  choices fail the unit-cell condition. This is a bounded falsification, not a
  global obstruction to the abstract surgery.
- `analysis/census_residue_two_affine_endpoint_extensions.py` rejects all `56`
  stable single-endpoint types transported from `k=7` through `k=9`. Although
  each proposed ray has the exact count recurrence, every type is geometrically
  obstructed by the grid boundary, old centers, a forbidden unit cell, or an
  affine component merge.
- `analysis/census_residue_two_endpoint_slide.py` derives exactly `20`
  constant-size leaf blockers from those endpoint failures and checks their
  four unit translations. All `80` chains fail. The remaining narrowed lower
  topology is a two-leaf hinge exchange based on the six multiple-intersection
  witnesses and one non-blocker-parent witness.
- `analysis/census_residue_two_two_leaf_hinge.py` derives only two legal leaf
  hinges from those seven witnesses; both fail by unit cells or overlap. The
  remaining five witnesses require a nonleaf spine operation.
- `analysis/census_residue_two_nonleaf_spine_bypass.py` rejects the five minimal
  projected-segment bypasses by a uniform count obstruction: distance two from
  spine to carrier forces the length-`k-5` bypass through a carrier-ray center.
  The next topology is an offset `k-7` core with two connector leaves.
- The remaining declared affine bypasses, neighboring-residue cap exchanges,
  safe-comb and periodic bulks through `6x6`, and bounded one/two/three-wall
  domain seams have all been completely classified and rejected. Periodic
  density-one-third bulks reduce to parallel rails with deficit `2k-2`; the best
  one-wall seam gains `6k+9`; bounded islands cannot simultaneously attain the
  target count and a singleton-owned incidence tree. The lower L2 gate remains
  open and is research blocked pending a genuinely nonlocal topology.
- Analytic calibration rules out the naive exact repair of the affine family.
  Every U vertex in a repeated `UU.` pump block closes a forced unit-cell cycle
  when promoted, and the `k=6` affine member has no valid single promotion.
  Any exact stable family must use a coordinated add/delete seam change or a
  different interval incidence tree, not independent affine promotions.
- The natural net-one endpoint exchange is locally impossible too: deleting one
  preserved spine endpoint and preserving the two adjacent `UU` vertices makes
  the second insertion close a forced unit square through the surviving spine
  endpoint. Existing complete `n=20` checks exclude all net-one affine repairs
  through three additions/four deletions. A further affine-based attempt must
  therefore coordinate at least four additions/five deletions across the
  middle and cap, but no symbolic rooted-interface schedule for that operation
  is known.
- `ResidueTwoExact.lean` defines a twenty-based pump with the exact target
  cardinality `6k^2+5k+4`, exact increment `12k+11`, and exact two-step
  increment `24k+34`. `ResidueTwoExactStep.lean` identifies the base with the
  proved `n=20` certificate. `ResidueTwoExactStep.lean` proves its first pumped
  member has an isolated checkerboard face, so this exact-count family is
  disconnected and cannot supply the tail.
- `ResidueTwoExactRepair.lean` formalizes a balanced seam add/delete repair with
  the same exact count. `RepairDisconnected.lean` proves every positive pump
  depth has a closed two-face dual component, so this repair is also invalid.
- `UniversalWasteBoundReduction.lean` proves `W>=n+2` is exactly equivalent to
  `n+4 <= fourSideComponentRank` on cotree supports.
- The residue-two equality and near-waste modules prove all cardinality,
  component-rank, row, and forced-acyclicity consequences of `W=n+2` and
  `W=n+5`. Their remaining obligations are respectively nonexistence of the
  tight attachment profile and a stable persistent-attachment-debt theorem.
- `ComponentAttachmentLedger.lean` proves the common exact attachment ledger
  and shows that cardinality plus acyclicity already fixes the two hypothetical
  residue-two ranks; excluding them requires additional geometry.
- `UniversalComponentRankPhase.lean` proves rank at least five universally and
  at least six outside residue one. `ResidueTwoStableDebtPorts.lean` proves
  every full component has a distinct crossing-edge witness and derives the
  corresponding component/port bounds; these do not yet force the extra stable
  debt unit.
- `CheckerboardComponent.lean` proves that the grid's two color classes give
  two acyclic center-star forests and establishes their exact ambient component
  ledger. Their component sum is the original two-component charge plus one
  isolated-component credit for every cotree-support vertex.
- `CheckerboardWaste.lean` proves that `W>=n+2` is exactly the subtraction-free
  checkerboard boundary inequality. `CheckerboardEquality.lean` further proves
  that checkerboard slack `q` is exactly waste `n+2+q`; in particular the two
  residue-two obstruction levels are checkerboard slack zero and three.
- `GridEdge.lean`, `GridDirection.lean`, and `TreeContour.lean` formalize the
  edge-labelled plane-grid tree contour. The clockwise contour successor is a
  finite permutation; bridge-shore cut balance proves each edge orientation is
  in the orbit of its reverse, and tree connectivity proves the permutation is
  one cycle.
- `ContourWaste.lean` proves the exact local/global split of waste into supported
  exterior sectors and supported tree returns. `ContourMarks.lean` realizes
  those terms as a finite type of cardinality exactly `incidenceWaste` and
  reduces `W>=n` to an explicit embedding `Fin n ↪ CotreeContourMark T`.
- `GridCotreePorts.lean` proves that every fundamental shore cut consists
  exactly of its attachment tree edge and distinct edge-labelled cotree ports.
  `GeometricContourMarks.lean` realizes return marks as actual contour darts,
  and `ShoreRouting.lean` gives the exact marks-or-ports lane-routing criterion.
  Cotree-port membership is convex along nested shores, and any injective
  discharge of a shore's ports to distinct outside marks now composes with its
  local routing to produce a genuine mark injection.
- `StraightForcedComponents.lean` proves the local three-corners obstruction:
  an acyclic forced graph cannot force three corners of one unit cell. This is
  the local mechanism preventing full-vertex components from making turns.
- `PrimalContourLedger.lean` eliminates the abstract return sum entirely:
  `W+1` is boundary deficiency on cotree support, plus tree edges internal to
  that support, plus the number of full-vertex components. Thus `W>=n` is
  exactly an `n+1` lower bound on this concrete three-term charge.
- `GridGraphs/DiagonalFormula.lean` defines `diagonalFormulaP` and proves
  `maxPreserved_eq_diagonalFormulaP` for every `n>=3` from four explicit
  hypotheses. Its strengthened `maxPreserved_eq_diagonalFormulaP_of_remaining`
  uses all completed constructions and assumes only the residue-two
  construction tail `n=3k+2`, `k>=7`.

## Not proved (deferred — see notes)

The operational maximum and its generic upper/lower APIs are now defined. The
remaining deferred statements are the structural theorems needed to discharge
the hypotheses of `maxPreserved_eq_diagonalFormulaP`:

- The headline lower-bound theorem `lowerB m n ≤ maxPreserved m n` (i.e.
  there exists a spanning subtree with `numPreserved ≥ m + n − 2`). The
  L-bend forced subgraph is defined and shown to be a subgraph of the
  grid graph in `DoubleComb.lean`; its acyclicity proof and the
  forest-extension application remain.
- Arbitrary-width target-count residue-two construction from `n=23` onward.
- Universal incidence-waste bound, its equality classification, and exclusion
  of the residue-two `W=n+5` class for `k>=5`.
- `lower_bound_construction`: an explicit "double-comb" spanning tree achieving
  `numPreserved ≥ m + n − 1`.

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

1. Do not target an unconditional `FullPrunedRegionalCertificate`: exhaustive
   `3 x 3` analysis found a spanning tree with one ranked collision and three
   residual resources globally, but no residual resource first-owned by its
   only inward shore. Thus the structure's `terminal_owned` field is false for
   that tree despite surplus cardinal capacity.
2. Prove the universal bound through a weaker global routing or direct geometric
   inequality that permits ownership exchange across regions. The completed
   occurrence-preserving launch and three-pool adapter remain valid conditional
   tools, but cannot be instantiated by the rejected regional certificate.
3. The maximum-only summed four-crop rank inequality and its weaker balanced-crop
   consequence are also rejected by explicit maximum `9 x 9` witnesses. The
   straight-carrier axial-gap strengthening fails at `n=10`. These routes must
   not be reused without materially different hypotheses.
4. Global insertion-circuit localizations were also falsified. Owner-labelled
   fundamental paths have unbounded edge and angle-sector congestion. The
   minimum-reflex strengthening fails for an inclusion-maximal `9 x 9` forced
   forest even after independently minimizing each owner's circuit. Generic
   graphic-matroid submodularity gives an upper bound on omitted bundles, in the
   opposite direction from the required support lower bound.
- A sound global alternating-exchange layer is now implemented. It includes
  finite matching augmentation and deficient closures, exact automatic owners
  of reserved ports/edges/components, one-copy shared-hull continuation,
  displaced-owner adjacency, ordered outer traversal, reverse-root traversal,
  retained-edge pass-through, and component-contact tree-basis exchange. The
  unified `PhysicalSaturationTransitionSystem` preserves each initiating source
  occurrence while raw resources remain one-copy physical objects.
- The completed executable saturation model exhausts every `3 x 3` and `4 x 4`
  spanning tree, both axes, every grouped-source subset, and every spatial-gap
  bijection with no Hall failure. Targeted/random trees through `8 x 8` also
  show no failure. This is finite falsification evidence, not a proof.
- The exact remaining theorem is the arbitrary-width no-deficient-closure
  statement for the physical saturation neighborhood. Connectivity and total
  component balance do not imply Hall, and the total source/resource cardinal
  consequence is already equivalent to universal waste. A proof must therefore
  establish genuine expansion for every alternating-closed source subset.
3. Invent and formalize a genuinely nonlocal stable residue-two lower family;
   the declared bounded affine-repair grammars are exhausted.
