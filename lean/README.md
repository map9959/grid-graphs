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

The latest 2026-09-06 U1/U3/L2 snapshot passed strict cached verification on Lean/mathlib
4.33.1: **8,941 jobs, exit 0, zero errors and zero warnings**. It contains
**234 modules under `GridGraphs/`** (84,372 lines), plus the 179-line aggregate
root: 235 library source files and 84,551 lines in total. All **163 public
theorems** in the audited BoundarySix, CarrierLayers, CarrierLayerBound, and
staircase ComponentLedger and RailRepair modules passed with axiom lists
contained in `{propext, Classical.choice, Quot.sound}`: the previous 72+31+44
were rerun alongside all 16 new public theorems; one is axiom-free.
Root and Regression import both new modules, ConcentratedGaps and CoveredDeficit.
New regressions passed unchanged: a length-four interval on a 9x9 board bounds
occupancy two rows away by seven; k=5 shadow-cost threshold 49 implies f<=110.
Previous lower/upper and missing-side checks also passed. No proof or test
files were edited in this verification pass.
See `STATUS.md` and `EVIDENCE.md` for coverage, logs, and the 11 existing
modules exceeding 1,000 lines.
ConcentratedGaps and CoveredDeficit are 297 and 244 lines, with 7 and 9 public
theorems. The previous OneExcessSeparated, CoveredBoundary, and RailRepair
Geometry, Forest, and Score are respectively 303, 276, 141, 97, and 146 lines, with 6, 7, 9, 6,
and 16 public theorems, all below 1,000 lines. The audit is not library-wide:
six legacy `native_decide` uses remain in the three separately built
counterexample tests, outside these 163 audited results.

Before extending a Lean file over 1,000 lines, split it into focused modules;
sub-subfolders are encouraged. Keep changed modules warning-free. The former
large `Results/SmallDiagonalExact.lean` is now an aggregate over its
`SmallDiagonalExact/` subfolder, with the largest proof file at 708 lines.

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
- `GridGraphs/Accounting/CarrierLengthBound.lean`: unconditional square upper bound
  `P(n)<=n*(n*n+4*n-6)/(3*n+1)` for n>=5, from preserved-component lengths.
- `GridGraphs/Accounting/BoundaryStratifiedCarrierBound.lean`: stronger numerator-minus-seven
  bound for n>=7, from boundary/deep carrier separation and the b>=6 ledger.
- `GridGraphs/Accounting/BoundarySix/`: boundary-six decomposition, next-ring
  uniqueness, boundary balance, and carrier bounds. `Upper.lean` proves the
  unconditional `P(3k+2)<=3k^2+7k+(2k+2)/3` for k>=5.
- `GridGraphs/Geometry/GridLayers.lean`: generic `IsNextRing` predicate.
- `GridGraphs/Accounting/CarrierLayerBound.lean` and `CarrierLayers/`: global
  layer injections, pure boundary carrier bounds, radial-side packing, and
  stable counterexample reductions. For feasible F on side 3k+2, k>=5,
  `MissingSideSharp.lean` proves **f<=T+1 for any missing open side**,
  T=3k^2+7k, independently of pure-carrier count p. Missing means no pure
  carrier meets that side, not no preserved vertices. The missing-side
  boundary bound is b>=2k+3; no maximality or connectivity is assumed beyond
  forced-graph acyclicity. In particular p<=3 implies f<=T+1.
  `RadialNearTightExclusion.lean` excludes the former two-excess three-carrier
  profile; MissingSideSharp extends this to every missing side. All feasible
  f>=T+2 sets cover all four open sides with distinct physical pure carriers,
  hence p>=4. The one-excess and all-sides-covered branches remain open.
- `GridGraphs/Accounting/CarrierLayers/RadialOneExcess.lean`: for k>=5, p<=3,
  f>=T+1, proves f=T+1 and exact natural slack `a+d+e=3` with
  `r=k+2+a`, `c=1+d`, `b=2k+3+e`. For q missing-side roots, m=k-q satisfies
  m<=e+1 and p<=a+m+2. Root saturation r=q+p makes distinct empty-block
  middles ambient isolates, giving c>=k-q+1 and m<=d. No distinct inward
  carriers are assumed for different blocks; this is not a sharp exclusion.
- `GridGraphs/Accounting/ResidueTwoCounterexampleProfile.lean` and
  `GridGraphs/Geometry/CarrierPacking.lean`: checked counterexample restrictions
  and local interval-overlap geometry for the next upper-bound steps.
- `GridGraphs/Accounting/CarrierLayers/OneExcessSeparated.lean`: proves
  `q+p+|S|+1<=r+c` for actual root-separated hole middles. The sharp bound
  f<=T follows conditionally if `p+|S|>=7`; no existence of such S is asserted.
- `GridGraphs/Accounting/CarrierLayers/CoveredBoundary.lean`: actual pure
  boundary mass P gives `B<=P+2*(r-p)` and `B<=P+E`; for n>=7,
  `4n-4<=P+2b` and `4n-4<=P+b+2*(r-p)`. Here P is occupancy, not P(n).
  These bounds charge the same physical contacts and cannot be added as
  independent charges. Both upper branches remain open.
- `GridGraphs/Accounting/CarrierLayers/ConcentratedGaps.lean`: a missing-side
  root-free inclusive interval has length <=16 only for k>=5, p<=3, f>=T+1.
  Shared inward carriers force root-free intervals, excluding inclusive spans
  >=17 in that branch. A preserved interval of length L independently costs
  `floor(L/2)` capacity two rows away; this local loss is not globally addable.
- `GridGraphs/Accounting/CarrierLayers/CoveredDeficit.lean`: the shadow union S
  consists of actual boundary holes, counted once. For n>=7, p=4 gives
  shortfall `D=n*p-P>=|S|+4`. A top next-ring segment of length L>=2 with
  endpoints in one carrier and columns in [1,n-2] casts L+2 holes (n>=5),
  hence D>=L+6 for n>=7, p=4. The cost bound is `|S|+2p<=b+2r` (n>=7).
  For k>=5, `|S|+2p+b+2c>=6k+19` suffices for f<=T; this certificate is
  not guaranteed. Neither new module improves an unconditional upper or lower
  bound or closes the remaining upper branches.
- `GridGraphs/Results/SmallDiagonalExact/`: structural exact proofs for sides
  3, 5, 7, and 10, including the equalities `P(7)=22` and `P(10)=42`.
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
  historical unconditional lower bound `3k^2+6k+2+k/2`, for k>=3. This does not
  attain the conjectured stable target at all widths.
- `GridGraphs/Constructions/ResidueTwo/Staircase/ComponentLedger.lean`: uniform
  combined component ledger, fixed 11x11/14x14 seed profiles, and actual
  six-width step gain one short of the target. No target-count pump is proved.
- `GridGraphs/Constructions/ResidueTwo/RailRepair/`: Geometry, Forest, and
  Score prove a single terminal parity repair, its unconditional acyclicity,
  and the new uniform lower bound `3k^2+6k+3+(k-1)/2`, k>=3.

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

The global upper formula remains `P(3k+2)<=T+(2k+2)/3`, k>=5. The current
formal lower bound is `L(k)=3k^2+6k+3+floor((k-1)/2)`, k>=3, via
`GridGraphs.RailRepair.residueTwo_le_maxPreserved`. It improves the staircase
by one at odd k and agrees at even k: 110 at side 17, 195 at side 23, and
304 at side 29. The current intervals are [110,114], [195,201], and [304,312];
in particular side 17 is not proved exact.

This terminal repair is not a target-count pump: k->k+2 still gains 12k+25,
not 12k+26. Its deficit from the stable target `3k^2+7k-1` is
`floor(k/2)-2` for k>=5. Lower-side Python experiments and L2 research
documents remain separate paper-level evidence, not a formal target pump.
Joint-notch and new paper searches remain finite side-11/14 research with no
new formal claim.

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

For full strict cached verification, run from `lean/` without cleaning the
existing project/mathlib artifacts:

```bash
LEAN_NUM_THREADS=2 lake --no-cache --wfail build \
  GridGraphs \
  GridGraphs.Tests.FourCropBoundaryCounterexample \
  GridGraphs.Tests.GroupedAlternatingClosureCounterexample \
  GridGraphs.Tests.InsertionReflexCounterexample \
  GridGraphs.Constructions.ResidueZero.ResidueZeroPersistentEnds \
  GridGraphs.Results.SmallDiagonal
```

This exact command passed for the snapshot above; its log is
`/tmp/opencode/u1-u3-l2-gap-shadow-full-build.log`. No competing full build was active at
the initial check. Existing artifacts were reused, not deleted or rebuilt from
scratch. The axiom-audit command and complete coverage are in `EVIDENCE.md`.

## Sorry-free Verification

```bash
grep -rE '^\s*(sorry|admit)\s*$|by sorry|by admit|:= sorry|:= admit' \
  GridGraphs/ GridGraphs.lean
# Expected output: nothing.
```
