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
previously unimported modules remain outside the aggregate import closure.
All 40 new CornerPacket/Rootless/BoundarySix.Connected/EndpointUpper modules
and the previous Annulus/ThreeCarrier and BoundaryFive/FourCarrier groups are
covered by the aggregate.
Check the five legacy modules explicitly when verifying every source file. See `STATUS.md` for
current verification rather than inferring it from this directory structure.

The latest 2026-09-07 EndpointUpper snapshot passed the exact full strict
cached build on Lean/mathlib 4.33.1: **9,049 jobs, exit 0, zero errors and warnings**.
It contains **342 modules under `GridGraphs/`** (100,477 lines), plus the
188-line root: **343 library source files, 100,665 lines total**. All **40 new
modules** are in the recursively checked root closure; only the five original
legacy targets remain outside. EndpointUpper was already imported. The closure
check found the unused valid leaf `BoundarySix.Connected.RingEndpoint`; this
pass added its permitted root import before the full build/audit snapshot.

The unchanged external `TotalCurrentAudit.lean` and `AnnulusThreeCarrierAudit.lean`
reran the previous **409 public theorems + 28 definitions + 2 abbreviations +
2 structures**. The generated `endpoint-upper-final-Audit.lean` checked all
new public declarations and both Symmetry exports: **202 declarations**.
All three import only `GridGraphs` and passed with warnings as errors.
The old `exists_top_gap_pullback` is the only overlap, so combined coverage is
**584 theorems + 50 definitions + 3 abbreviations + 5 structures = 642 unique
explicitly named public declarations**. Dot-named methods are included; generated field
projections, constructors, and recursors are not additional source entries.
Private helpers are covered transitively where used, not separately
counted. Every printed axiom list is a subset of
`{propext, Classical.choice, Quot.sound}`, possibly empty. This is not a
whole-library axiom audit: six legacy `native_decide` uses remain in the three
separately built counterexample tests, outside this public audit scope.

| New group under `Accounting/` | Modules | Lines | Theorems | Definitions | Abbreviations | Structures |
|---|---:|---:|---:|---:|---:|---:|
| `BoundaryFive/CornerPacket/` | 6 | 1,196 | 30 | 0 | 0 | 0 |
| `BoundaryFive/Rootless/` | 15 | 2,206 | 69 | 12 | 0 | 2 |
| `BoundarySix/Connected/` | 18 | 2,402 | 73 | 10 | 1 | 1 |
| `EndpointUpper.lean` | 1 | 46 | 2 | 0 | 0 | 0 |
| **Total** | **40** | **5,850** | **174** | **22** | **1** | **3** |

All new modules are **31-521 lines**. The existing Symmetry file is 143 lines
with two public theorems, one new; its old theorem statement is preserved.
All **300 old modules other than Regression and Symmetry** match the previous
Annulus/ThreeCarrier snapshot, including the **11 old oversized files**. Root and all
342 module fingerprints (including every test) stayed stable through build and
audit. The comment-aware scan found zero `sorry`/`admit`/`sorryAx` tokens.
Regression passed the uniform refined lower/upper interval, unconditional
P(23)<=200 and P(32)<=376, and all older checks. No Regression repair was needed.
Only the three verification documents and the one permitted root import were
edited in this pass, not proofs, tests, or Python application files; unrelated
existing changes were left alone. No Python or optimization searches were run.
`EVIDENCE.md` records exact declarations, method/count conventions, and logs;
the fingerprints do not cover all mathlib artifacts or the entire workspace.

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
  `ThreeCarrier/Closure.lean` proves **f<=T for any missing open side**,
  T=3k^2+7k, independently of pure-carrier count p. Missing means no pure
  carrier meets that side, not no preserved vertices. The missing-side
  boundary bound is b>=2k+3; no maximality or connectivity is assumed beyond
  forced-graph acyclicity. No off-side cost W assumption is needed either.
  In particular p<=3 implies f<=T; MissingSideSharp retains the older T+1 bound.
  `RadialNearTightExclusion.lean` excludes the former two-excess three-carrier
  profile; MissingSideSharp extends this to every missing side. All feasible
  f>=T+1 sets now cover all four open sides with distinct physical pure carriers,
  hence p>=4. Only the all-sides-covered sharp upper branch remains open.
- `GridGraphs/Accounting/CarrierLayers/RadialOneExcess.lean`: for k>=5, p<=3,
  f>=T+1, proves f=T+1 and exact natural slack `a+d+e=3` with
   `r=k+2+a`, `c=1+d`, `b=2k+3+e`. For q missing-side roots, m=k-q satisfies
  m<=e+1 and p<=a+m+2. Root saturation r=q+p makes distinct empty-block
  middles ambient isolates, giving c>=k-q+1 and m<=d. No distinct inward
   carriers are assumed for different blocks; this is not a sharp exclusion.
   The new global results force p=3 and a>=1 here. Algebraically, A=a-1 gives
   `r=k+3+A`, `c=1+d`, `b=2k+3+e`, `A+d+e=2`; this shifted form is
   a derived consequence, not a new checked named API. These one-excess
   premises are now impossible by the entire missing-side closure.
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
  independent charges. The missing-side branch is now closed; all-covered remains open.
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
  not guaranteed. Neither of these earlier modules alone improves an
  unconditional upper or lower bound; the later missing-side closure is separate.
- `GridGraphs/Accounting/CarrierLayers/GapGlobalCapacity.lean`: h counts actual
  shallow nonpure carriers, allowing boundary endpoints. The global bounds are
  `f<=B+E+(n-4)*(r-p-h)` (n>=5) and `f<=4n-4+(n-4)*(r-p-h)` (n>=7),
  with natural subtraction. Deep capacity is deducted once per carrier, not per
  hole or inward witness. At p=3, f>=T+1, r=k+2+a, k>=5, h<=a.
- `GridGraphs/Accounting/CarrierLayers/GapGlobalExclusion.lean` and
  `GapGlobalMinimal.lean`: the first excludes the minimal-induced connected
  three-pure profile; the second excludes **p=3, r=k+2 for any c** above T,
  using unused missing-side holes as a global boundary/next-ring loss.
- `GridGraphs/Accounting/CarrierLayers/CoveredGlobalMissingSides.lean`: every
  feasible f>=T+1 set at **k>=5** has at most one missing open side, at least
  three physically covered sides, **p>=3** (old threshold k>=7), and
  **r>=k+3** (old k+2). Two missing sides give disjoint holes and b>=4k.
- `GridGraphs/Accounting/CarrierLayers/GlobalUpperProfiles.lean`: for k>=5,
  e>=1 and f>=T+e, the global excess budget is **b+c+3e<=2k+9**.
  For **b>=6**, **f<=T+floor((2k+1)/3)**. When k%3=2, reaching the old
  endpoint would force exactly that score and **(r,c,b)=(k+4,1,5)**.
  The new BoundaryFive argument excludes this profile.
- `GridGraphs/Accounting/BoundaryFive/Upper.lean`: the previous **global** bound
  **P(3k+2)<=T+floor((2k+1)/3), k>=5**, for all boundary budgets. The generic
  nonpure-singleton bound `f+n<=(n-4)r+12` (n>=10, b=5), top-gap singleton,
  and cardinality/acyclicity-preserving square symmetry exclude the old endpoint.
  No full-frame normalization or connectedness assumption is needed.
- `GridGraphs/Accounting/CarrierLayers/FourCarrier/Closure.lean`: closes the
  **p=4 missing-side branch for every k>=5**, including n=17, with f<=T.
  Any remaining missing-side counterexample at f>=T+1 has **exactly p=3**.
  ThreeCarrier.Closure now also excludes that three-carrier one-excess branch;
  the all-sides-covered branch remains open.
- `GridGraphs/Accounting/CarrierLayers/ThreeCarrier/Closure.lean`: the entire
  missing-side bound **f<=T, k>=5**, with no p or W assumption. W2 uses an
  enlarged nonpure strip including top/next-ring vertices and joint nearby-rod
  edge packing, with no remaining top/equality exceptions. W3 needs no
  extra-hole adjacency classification: one actual extra off-side hole permits
  a joint defect of at most two edges, giving **f<=T-k+5<=T**. W4 uses the
  annulus deficit and connected shallow carriers.
- `GridGraphs/Accounting/CarrierLayers/Annulus/`: **B+E<=4n-9 for n>=9**,
  K=4n-4-B-E>=5, cubic **rA+cA+4<=2K**, actual full-rod packet bound
  **M+1<=cA**, and **r+5<=2K+D**, where D=(n-4)d minus deep occupancy.
  No carrier-contact forest is assumed. Counterexamples have d=r-p-h>=k.
  The entire **b>=7** branch satisfies **f<=T+floor(2k/3)**, including the
  conditional n=23 bound 200. EndpointUpper now excludes all three old k%3=1
  upper-endpoint profiles `(r,c,b)=(k+5,1,5), (k+4,2,5), (k+4,1,6)`.
- `GridGraphs/Accounting/CarrierLayers/AllCoveredCounterexamples.lean`:
  every f>=T+1 set is all-covered with **p>=4 and r>=k+4**; globally,
  **b+c+3e<=2k+8 for all e>=1 and f>=T+e**, without a coverage premise.
  These do not improve the unconditional upper formula or RailRepair lower bound.
- `GridGraphs/Accounting/EndpointUpper.lean`: the current **unconditional** bound
  **P(3k+2)<=T+floor(2k/3), k>=5**, via
  `GridGraphs.maxPreserved_residueTwo_le_endpoint_refinement`. CornerPacket
  excludes the connected b=5 first profile by two actual short carriers and
  the annulus. Rootless bridges the actual c=2,b=5 profile to a fully rooted
  deep square with q=k and four U corners, then contradicts long-rod missing
  triples. BoundarySix.Connected uses the same bridge for E=1 and corner-U
  E=0; the remaining all-corners-F E=0 case uses two five-edge packets to
  force an actual singleton, then summed annulus deficits. Only the gap is
  oriented; no extra canonical hole choices or distinct-corner-carrier
  assumption is imposed. `Rootless.strict_carrier_cap` requires
  `UniqueBoundaryRoots`; no generic ambient b=5 strict n-5 theorem is claimed.
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

The global upper formula is `P(3k+2)<=T+floor(2k/3)`, k>=5, T=3k^2+7k.
It saves one at k%3=1: P(23)<=200 (previously 201), P(32)<=376 (previously 377).
The current
formal lower bound is `L(k)=3k^2+6k+3+floor((k-1)/2)`, k>=3, via
`GridGraphs.RailRepair.residueTwo_le_maxPreserved`. It improves the staircase
by one at odd k and agrees at even k: 110 at side 17, 195 at side 23, and
304 at side 29. Current intervals are **17 [110,113], 20 [149,154],
23 [195,200], 26 [246,253], 29 [304,312]**, and the formulas give **32 [367,376]**;
in particular side 17 is not proved exact.

The topologically full sharp bound P(3k+2)<=T remains unproved. The next
profile program concerns all-covered **f=T+e, 1<=e<=floor(2k/3)**, retaining
p>=4, r>=k+4, d=r-p-h>=k and b+c+3e<=2k+8. These necessary constraints
organize actual boundary/component slack but do not exclude all lower excess;
further nonreused physical losses are needed, including beyond the current
b>=7 bound. No remaining excess level or new upper endpoint is asserted
attainable. The three old k%3=1 endpoint profiles are closed, not next tasks.
The entire missing-side f<=T closure and RailRepair are unchanged.

This terminal repair is not a target-count pump: k->k+2 still gains 12k+25,
not 12k+26. Its deficit from the stable target `3k^2+7k-1` is
`floor(k/2)-2` for k>=5. Lower-side Python experiments and L2 research
documents remain separate paper-level evidence, not a formal target pump.
Joint-notch and new paper searches remain finite side-11/14 research with no
new formal claim.
The 76-center n=14 rootless-output candidate in
`../docs/L2_TERMINAL_TAIL_INTERFACE.md` is paper-only evidence, not a new
formal lower bound or accumulating pump; its six-width gain is still 12k+25.

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
`/tmp/opencode/endpoint-upper-final-full-build.log` (same-stem `.exit` is 0).
Existing artifacts were reused, not deleted or rebuilt from
scratch. The axiom-audit command and complete coverage are in `EVIDENCE.md`.
The build ran without an imposed time limit. The root directly imports
EndpointUpper and the otherwise unused valid RingEndpoint leaf,
covering all 40 new modules alongside the old imports.
Only the original five legacy modules lie outside the aggregate closure; the
command above includes them all. No additional separate build is needed.
All audits are external `/tmp/opencode/*.lean` files; ThreeCarrier's removed
Audit, ClosureAudit, CostTwoClosureAudit, and CostThreeAudit production modules
were not reintroduced. Their current public declarations were enumerated from source.

## Sorry-free Verification

```bash
rg -n -g '*.lean' '^\s*(sorry|admit)\s*$|by sorry|by admit|:= sorry|:= admit' \
  GridGraphs/ GridGraphs.lean
# Expected output: nothing.
```
