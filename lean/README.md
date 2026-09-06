# Lean Formalization: Grid Graph Preservation Bounds

A Lean 4 + mathlib project formalizing combinatorial identities and bound
expressions from `docs/DERIVATION.md` for the m×n grid graph.

## Problem

The **grid graph** `G(m, n)` has `m × n` vertices arranged in a rectangular
grid; each vertex is adjacent to the (up to four) vertices immediately above,
below, left, and right of it. A **spanning tree** `T` of `G(m, n)` is a
connected acyclic subgraph that contains every vertex. A vertex `v` is
**full-degree in `T`** if `deg_T(v) = deg_G(v)` — equivalently, every edge of
`G` incident to `v` is retained in `T`.

The problem this project analyzes is:

> Find a spanning tree `T` of `G(m, n)` that maximizes the number of
> full-degree vertices, and/or determine that maximum.

Write `P(m, n)` for that maximum. The Rust DP in `../src/main.rs` computes
`P(m, n)` exactly for moderate `m, n`; the Lean code formalizes algebraic
identities and bound expressions (basic and refined upper bounds, conservative
lower bound) that constrain `P(m, n)`.

In this codebase a "full-degree" vertex is also called "preserved", following
the terminology in `docs/DERIVATION.md`; the two terms are interchangeable.

## Source Layout

`GridGraphs.lean` remains the aggregate entry point. Modules are grouped by
subject rather than by proof status:

| Directory under `GridGraphs/` | Contents |
|---|---|
| `Core/` | Grid definitions, spanning trees, bounds, and optimization model |
| `Forests/` | Generic forest, cut, parent, and first-stop machinery |
| `Geometry/` | Grid edges and duals, boundary cycles, crosscuts, and contours |
| `Accounting/` | Waste and component ledgers, boundary and equality obstructions |
| `Routing/` | Channels, Hall conditions, physical resources, and ownership |
| `Surgery/` | Cropping, insertion, exchanges, and repair arguments |
| `Constructions/` | Shared construction certificates and gluing tools |
| `Results/` | Exact small cases, formula assembly, and recurrence statements |
| `Tests/` | `Regression.lean` and explicit counterexamples |

`Constructions/` has `BoundaryFive/`, `Finite/`, `ResidueZero/`, `ResidueOne/`,
and `ResidueTwo/` subfolders. Failed construction attempts remain with their
families; directory placement is not a claim that a theorem is proved.

Module paths changed, but public declaration namespaces did not. For example:

```lean
import GridGraphs.Constructions.ResidueTwo.ResidueTwoStaircaseForest

#check GridGraphs.ResidueTwoStaircase.residueTwo_le_maxPreserved
```

Use `import GridGraphs` for the aggregate or a specific nested module for a
small dependency set. There are no old-path compatibility wrappers. The five
previously unimported modules remain outside the aggregate import closure;
check them explicitly when verifying every source file. See `STATUS.md` for
current verification rather than inferring it from this directory structure.

## Key Modules

- `GridGraphs/Core/Defs.lean`: Vertex/edge counts, deficiency, vertex-class
  partition, and the simple graph `gridGraph m n` itself (a real
  `SimpleGraph (Fin m × Fin n)` with proven `symm` and `loopless`).
  Includes `Fintype` / `DecidableEq` / `DecidableRel` instances and real
  `gridDegree` / `isPreserved` / `vertexDeficiency` / `numPreserved`
  definitions built on `SimpleGraph.degree`.
- `GridGraphs/Core/Bounds.lean`: Algebraic bound expressions `D`, `I`, `ceilDiv3`,
  `basicUB`, `refinedUB`, `lowerB`, and their `sorry`-free properties.
- `GridGraphs/Core/Forced.lean`: Forced-edge subgraph of full-degree vertices;
  forced-edge acyclicity from a spanning tree.
- `GridGraphs/Geometry/Diagonal.lean`: Induced-edge decycling sets, complement-of-
  preserved is decycling, every grid 4-cycle has an unforced boundary edge,
  cell-adjacency lemmas, and the cell-hitting corner condition.
- `GridGraphs/Geometry/GridDual.lean`: Explicit grid faces, primal/dual edge endpoint
  maps, executable U-U dual graph, and the conditional theorem chain reducing
  dual-certified constructions to the remaining cycle-separation proposition.
- `GridGraphs/Constructions/ResidueOne/ResidueOne.lean`: Residue-1 diagonal `U` construction
  (`uResidueOne k`) with proven cardinality `6 * k^2 + k + 1` (Proposition L1
  cardinality from `analysis/proofs_diagonal.md`).
- `GridGraphs/Core/Spanning.lean`: `IsSpanningSubtree` predicate, total-deficiency
  identity, per-vertex deficiency caps (≤ 1 / ≤ 2 / ≤ 3 for corner / border /
  interior), and the headline operational upper bounds
  `preserved_le_basicUB` and `preserved_le_refinedUB`.
- `GridGraphs/Forests/ForestExtension.lean`: the standalone, generic forest
  extension lemma `isAcyclic_extends_to_isTree`.
- `GridGraphs/Accounting/IncidenceWaste.lean`: support incidence waste and exact arbitrary
  equal-edge exchange accounting.
- `GridGraphs/Accounting/ForestLedger.lean`: generic finite-forest edge/component ledger.
- `GridGraphs/Accounting/CotreeWaste.lean`: identifies grid cotree support with
  non-preserved vertices and proves the exact cotree waste identity.
- `GridGraphs/Accounting/ForcedForestLedger.lean` and
  `GridGraphs/Accounting/ComponentReduction.lean`: exact forced-forest and induced-forest
  component reductions.
- `GridGraphs/Accounting/TreeComponentBridge.lean`: exact equality between square cotree
  incidence waste and the forced-forest component charge.
- `GridGraphs/Core/MaxPreserved.lean`: finite operational definition of `P(m,n)` and
  maximum/witness/universal-bound APIs.
- `GridGraphs/Constructions/ResidueOne/ResidueOneDual.lean` and `ResidueOneMax.lean`: complete
  residue-one dual connectivity, preserving construction, and lower bound.
- `GridGraphs/Constructions/ResidueZero/`: recursive phase construction, exact
  cardinality, and the symbolic arbitrary-width construction proofs.
- `GridGraphs/Constructions/ResidueTwo/ResidueTwoStaircaseForest.lean`: the
  unconditional improved lower bound `3k^2+6k+2+k/2`, for k>=3. This does not
  attain the conjectured stable target at all widths.
- `GridGraphs/Results/DiagonalUpper.lean` and `DiagonalFormula.lean`: residue-wise
  conditional upper bounds and assembly of the proposed exact formula from
  four named structural/construction hypotheses.
- `GridGraphs/Constructions/DoubleComb.lean`: the L-bend forced subgraph and the
  simpler `topSpineColumns` spanning-tree candidate, with connectedness
  and top-row preservation. The IsTree proof and headline lower-bound
  theorem are deferred.
- `GridGraphs/Tests/Regression.lean`: `decide`-based regression checks pinning Lean
  values of bound expressions and vertex counts to known Rust DP outputs.
- `GridGraphs.lean`: Aggregate import.
- `STATUS.md`: Detailed proof-status ledger.
- `EVIDENCE.md`: Annotated lemma index plus empirical comparison against
  ground-truth `P(m,n)` from the Rust DP for all `1 ≤ m, n ≤ 10`.
- `results-empirical.csv`: Regenerated Rust output backing `EVIDENCE.md`.

## Headline Proven Lemmas (zero `sorry`)

- `deficiency_closed_form`: `deficiency m n = 2 * (m-1) * (n-1)`.
- `D_eq_deficiency`: the algebraic `D` matches the operational `deficiency`.
- `verts_partition`: the corner / border-non-corner / interior counts sum to `m * n`.
- `basicUB_4n` / `refinedUB_4n`: closed forms `2n+2` / `2n+1` for the 4×n
  family, matching the Rust regression test `refined_expected_4xn_pattern`.
- `refinedUB_le_basicUB`: the refined bound never exceeds the basic bound.
- `lowerB_le_basicUB`: the conservative lower bound never exceeds the basic
  upper bound (sanity of the bound chain).
- `forcedEdgeGraph_isAcyclic_of_preserves`: the forced-edge graph of any
  full-degree set in an acyclic spanning subgraph is acyclic.
- `grid_cell_has_unforced_edge`: every grid unit cell in an acyclic forced-
  edge graph has an unforced boundary edge.
- `preserved_set_cell_corner`: spanning-subgraph form—every 2×2 cell
  contains at least one corner outside the full-degree set.
- `uResidueOne_card`: for `k ≥ 1`, the residue-1 diagonal `U` construction
  has `|U| = 6 * k^2 + k + 1`. Cardinality half of Proposition L1; the
  acyclicity and forest-extension results are also documented in `STATUS.md`.
- `gridGraph_eq_boxProd`: the grid graph is the box product
  `pathGraph m □ pathGraph n` (enabling free connectivity / degree
  decomposition from mathlib).
- `gridGraph_connected`: connectivity of the grid graph for `m, n ≥ 1`.
- `total_deficiency`: `∑ v, vertexDeficiency m n T v = D m n` for any
  spanning subtree `T`.
- `vertexDeficiency_le_three`: per-vertex cap of 3 deficiency in any
  spanning subtree. Per-class refinements (≤ 1 / ≤ 2) for corner / border
  vertices.
- **`preserved_le_basicUB`** and **`preserved_le_refinedUB`**: the
  operational connection of both algebraic upper bounds to
  `numPreserved m n T` for any spanning subtree.
- **`SimpleGraph.isAcyclic_extends_to_isTree`**: any acyclic subgraph of
  a finite connected graph extends to a spanning tree. Standalone,
  generic, mathlib-style.
- **`incidenceWaste_exchange_balance`**: exact support accounting for every
  equal-edge graph exchange, including multi-edge exchanges.
- **`grid_cotree_incidenceWaste_identity`**:
  `W + D + 3*numPreserved = 3mn` for every grid spanning subtree.
- **`square_grid_component_reduction_compl`**: exact subtraction-free square
  component identity corresponding to `Q_U+c_F+c_H`.
- **`square_grid_tree_component_bridge`**: the tree-cotree accounting languages
  agree exactly, with component charge equal to incidence waste plus two.
- **`uuDualGraph_uResidueOne_connected`** and
  **`residueOne_le_maxPreserved`**: unconditional infinite residue-one
  construction theorem.
- **`maxPreserved_eq_diagonalFormulaP`**: exact formula assembly for all
  `n>=3` from the remaining named hypotheses.

See `STATUS.md` for the full list and `EVIDENCE.md` for line-numbered
references plus empirical evidence.

## Deferred (not yet proven in Lean)

The operational maximum and basic/refined upper bounds are proved. The exact
diagonal formula remains conditional on the universal waste theorem, equality
classification, residue-two tail exclusion, and missing construction cases.
Residues zero and one have matching constructions, while their general exactness
still needs upper bounds. The improved arbitrary-width residue-two family is
proved, but the target-count family and sharp upper exclusions remain open.

## Build Instructions

```bash
cd lean
lake update     # fetch mathlib (already pinned in lake-manifest.json)
lake build      # build the project; should print "Build completed successfully"
```

To open in VS Code, open the `lean/` folder with the Lean 4 extension.

## Sorry-free Verification

```bash
grep -rE '^\s*(sorry|admit)\s*$|by sorry|by admit|:= sorry|:= admit' \
  GridGraphs/ GridGraphs.lean
# Expected output: nothing.
```
