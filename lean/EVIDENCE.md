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

Full strict cached verification of the latest 2026-09-06 U1/U3/L2 snapshot passed on
Lean/mathlib **4.33.1** with **zero errors and zero warnings**: **8,941 jobs,
exit 0**. It covers 234 modules under `GridGraphs/` plus the aggregate root,
including the five explicitly requested modules outside its import closure.
The source count is 84,372 lines under `GridGraphs/`, or 84,551 including
the 179-line root (235 library source files in total). This snapshot includes
BoundarySix, global CarrierLayers, CarrierLayerBound, the staircase
ComponentLedger, all three RadialTight modules, the five MissingSide/near-tight
leaves, OneExcessSeparated/CoveredBoundary/RailRepair, and the new
ConcentratedGaps and CoveredDeficit modules. Root and Regression import both
new modules. The new regressions passed unchanged: a length-four preserved
interval on row 1 of a 9x9 board bounds row 3 occupancy by seven; at k=5,
shadow-cost threshold 49 implies f<=110. Previous lower/upper, missing-side,
and two-excess checks also passed. No proof or test files were edited. The full
command is in `README.md`; the completed log is
`/tmp/opencode/u1-u3-l2-gap-shadow-full-build.log`.

Existing finite-witness data and statements are unchanged; their fixed entries
now use efficient kernel `decide` replay, not new searches or native proof
axioms. See `STATUS.md` and `../docs/ROADMAP.md` for the current verification
command. Older counts and line references below belong to their historical
milestones; the theorem names and relocated module paths are the stable references.

### U1/U3/L2 Axiom Audit (2026-09-06)

The temporary files `/tmp/opencode/U1U3L2Audit.lean` (previous 72),
`/tmp/opencode/U1U3L2MissingSideAudit.lean` (previous 31),
`/tmp/opencode/U1U3L2RailRepairAudit.lean` (previous 44), and
`/tmp/opencode/U1U3L2GapShadowAudit.lean` (new 16), outside the proof tree,
import `GridGraphs` and explicitly print axioms for every public theorem
in these snapshot modules. The actual new public theorem count is 16:

| Module group | Public theorems audited |
|---|---:|
| `Accounting/BoundarySix/`: Geometry, Witnesses, Decomposition, Pairs, NextRing, Balance, CarrierBound, Upper | 25 |
| `Accounting/CarrierLayers/`: NextRingInjection, RadialSideGeometry, RadialPacking, RadialSideCounting, RadialSide, Counterexamples | 22 |
| `Accounting/CarrierLayers/RadialTightBoundary.lean` | 4 |
| `Accounting/CarrierLayers/RadialTightPacking.lean` | 3 |
| `Accounting/CarrierLayers/RadialTightExclusion.lean` | 3 |
| `Accounting/CarrierLayerBound.lean` | 5 |
| `Constructions/ResidueTwo/Staircase/ComponentLedger.lean` | 10 |
| `Accounting/CarrierLayers/MissingSide.lean` | 6 |
| `Accounting/CarrierLayers/MissingSideSharp.lean` | 3 |
| `Accounting/CarrierLayers/RadialNearTightBoundary.lean` | 9 |
| `Accounting/CarrierLayers/RadialNearTightExclusion.lean` | 5 |
| `Accounting/CarrierLayers/RadialOneExcess.lean` | 8 |
| `Accounting/CarrierLayers/OneExcessSeparated.lean` | 6 |
| `Accounting/CarrierLayers/CoveredBoundary.lean` | 7 |
| `Constructions/ResidueTwo/RailRepair/Geometry.lean` | 9 |
| `Constructions/ResidueTwo/RailRepair/Forest.lean` | 6 |
| `Constructions/ResidueTwo/RailRepair/Score.lean` | 16 |
| `Accounting/CarrierLayers/ConcentratedGaps.lean` | 7 |
| `Accounting/CarrierLayers/CoveredDeficit.lean` | 9 |
| **Total** | **163** |

Run from `lean/`:

```bash
LEAN_NUM_THREADS=2 lake env lean -DwarningAsError=true /tmp/opencode/U1U3L2Audit.lean
LEAN_NUM_THREADS=2 lake env lean -DwarningAsError=true /tmp/opencode/U1U3L2MissingSideAudit.lean
LEAN_NUM_THREADS=2 lake env lean -DwarningAsError=true /tmp/opencode/U1U3L2RailRepairAudit.lean
LEAN_NUM_THREADS=2 lake env lean -DwarningAsError=true /tmp/opencode/U1U3L2GapShadowAudit.lean
```

Result: all four exit 0, zero warnings/errors, with all 163 dependency lists contained
in `{propext, Classical.choice, Quot.sound}`. No `sorryAx` or native proof
axiom appears. Complete outputs:
`/tmp/opencode/u1-u3-l2-gap-shadow-previous72-axioms.log`,
`/tmp/opencode/u1-u3-l2-gap-shadow-previous31-axioms.log`,
`/tmp/opencode/u1-u3-l2-gap-shadow-previous44-axioms.log`, and
`/tmp/opencode/u1-u3-l2-gap-shadow-new16-axioms.log`.
This covers public helper theorems as well as headline upper bounds, global
counterexample profiles, seed edge counts/profiles, both step lemmas, and all
10 tight-boundary, exact-phase, and exclusion theorems, all 31 missing-side,
near-tight, exclusion, and one-excess theorems, all 44 root-separated,
physical-occupancy, repaired-geometry, forest, and score theorems, and all 16
concentrated-gap and covered-shadow theorems. The previous 147 checks were
rerun, not merely carried forward. Output counts are 72, 31, 44, and 16,
including the axiom-free `GridGraphs.RailRepair.attachment_subsingleton`.
Private helpers are covered transitively where used, not individually printed;
definitions are not separately audited. Later additions require a new audit.
This is not a whole-library axiom audit. The three separately built legacy
counterexample tests contain six `native_decide` uses; no native proof axiom
occurs in the 163 audited dependency lists.

The source-length inventory is `/tmp/opencode/u1-u3-l2-gap-shadow-source-lengths.log`.
The source fingerprint manifest is `/tmp/opencode/u1-u3-l2-gap-shadow-source-sha256.log`
(234 modules plus the aggregate root); it identifies this verified snapshot.
All 31 audited modules are 55-380 lines. ConcentratedGaps and CoveredDeficit
are 297 and 244 lines, with 7 and 9 public theorems respectively.
OneExcessSeparated, CoveredBoundary,
and RailRepair Geometry, Forest, and Score are respectively 303, 276, 141,
97, and 146 lines, all below 1,000.
`Geometry/GridLayers.lean` adds the
12-line generic next-ring predicate. `STATUS.md` lists all 11 existing modules
over 1,000 lines. A fresh tactic-position `sorry`/`admit` scan using the
documented pattern returned no matches. No optimization search was run.

### Boundary Six And Global Packing (2026-09-06)

`maxPreserved_residueTwo_le_boundary_six_refinement` proves
`P(3k+2)<=3k^2+7k+(2k+2)/3` for k>=5, unconditionally across boundary
budgets. The improvement over the earlier floor is one at k divisible by three,
including `P(20)<=154` and `P(29)<=312`. At b=6, the checked geometry gives
at most one preserved next-ring vertex (n>=9), B>=4n-10, B+E<=4n-9,
and f<=(n-4)r+7 (n>=12).

For arbitrary feasible sets, let p count pure boundary carriers, r all preserved
carriers, c all ambient forced components including isolates, b complement
boundary deficiency, and B/E preserved boundary/next-ring occupancy.
CarrierLayerBound and NextRingInjection prove p<=r, B<=n*p+E,
f<=B+E+(n-4)*(r-p), E<=|unpreserved boundary|<=b (n>=5), and
4n-4<=n*p+2b (n>=7). These use physical neighbor injections without reuse.

For n=3k+2, k>=5, T=3k^2+7k, **any missing open side implies f<=T+1**
and b>=2k+3, independently of p. Missing means no pure boundary carrier
meets that open side, not zero preserved occupancy. In particular p<=3
implies f<=T+1. No maximality or connectivity assumption is needed beyond
forced-graph acyclicity. `residueTwo_card_le_target_add_one_of_missing_side`
is the uniform endpoint in `MissingSideSharp.lean`.

The formerly remaining two-excess profile `(r,c,b)=(k+2,1,2k+3)` is now
excluded on any missing side. In the three-carrier branch an empty triple
forces an extra inward carrier distinct from all root and pure carriers;
root/component nonreuse then extends the exclusion to arbitrary p.
`residueTwo_four_distinct_pure_carriers_of_two_excess` proves every feasible
f>=T+2 set covers all four open sides with an injective choice of physical
pure carriers, hence p>=4. Older profile implications are still valid but
their missing-side two-excess hypotheses are impossible.

For p<=3 and f>=T+1, `one_excess_exact_slack` proves f=T+1 and
`r=k+2+a`, `c=1+d`, `b=2k+3+e`, with natural `a+d+e=3`.
For q roots on a missing side, put m=k-q. The refined profile gives
`m<=e+1`, `p<=a+m+2`, and at root saturation `r=q+p`, `m<=d`.
The last bound charges at least k-q distinct empty-block middle isolates
to ambient components, plus one component containing a preserved vertex:
`c>=k-q+1`. It does not assume different blocks have different inward
carriers. At c=4 the geometry forces p=3, q=k-1, two off-side near-corner
holes, preserved corners, and an ambient isolate. These are necessary
conditions, not a one-excess exclusion. The one-excess and all-sides-covered
branches remain open. The global upper formula remains T+(2k+2)/3, k>=5.

`GridGraphs.CarrierLayers.separated_holes_charge_components` in
`OneExcessSeparated.lean` proves `q+p+|S|+1<=r+c` for actual selected
root-separated hole middles. Nonisolated middles use distinct extra induced
carriers, isolated middles use distinct ambient components, and one further
ambient component contains a preserved vertex. Holes in a common root-free
gap may share an inward carrier. The derived score bound is
`3f+p+|S|<=9k^2+21k+9`; for k>=5, `p+|S|>=7` gives f<=T conditionally.
There is no theorem asserting the existence of such a separated set S.

`CoveredBoundary.lean` defines `pureBoundaryVertices`: its cardinality P is
actual pure boundary occupancy, not the extremal function P(n). It is the sum
of disjoint pure-carrier lengths and satisfies P<=n*p. The module proves
`B<=P+2*(r-p)` without a size threshold, `B<=P+E` for n>=5, and for n>=7
both `4n-4<=P+2b` and `4n-4<=P+b+2*(r-p)`. It also derives full-side
shortfall bounds, including the exactly-four-pure-carrier case. These budgets
use the same physical contacts, not independent charges that can be added.
Neither new upper module closes the one-excess or all-sides-covered branch.

### Concentrated Gaps And Covered Shadows (2026-09-06)

For an acyclic forced set on side 3k+2, `missing_side_gap_length_budget`
proves `3q+L<=3k+4` (k>=1), where q counts preserved roots on a missing
open side and L is an inclusive root-free interval length. With **k>=5,
p<=3, f>=T+1**, T=3k^2+7k, `one_excess_gap_length_le_sixteen` gives
**L<=16** (more precisely L<=3e+7 in the exact slack profile). This is not
a universal gap bound. Shared inward witnesses in one actual induced carrier
force the whole intervening interval to be root-free; inclusive span >=17 is
excluded under those one-excess hypotheses. The conditional long-shared-carrier
endpoint gives f<=T, not existence of such a carrier.

`concentrated_interval_row_capacity_loss` independently proves that a preserved
interval of length L removes `floor(L/2)` capacity two rows away, even for
disconnected opposite occupancy. It counts physical row holes, not globally
addable component loss. The 9x9 regression specializes L=4 to row occupancy <=7.

`coveredBoundaryShadow` is the union S of actual boundary holes diagonally
opposite preserved next-ring vertices. Shared witnesses count once, not once
per carrier. If P is actual pure boundary mass and D=n*p-P is full-side
shortfall, `pure_mass_add_coveredBoundaryShadow_le_perimeter` proves
`P+|S|<=4n-4` for n>=7. Thus p=4 gives `D>=|S|+4`; all-side coverage gives
`D>=n*(p-4)+|S|+4`. A top next-ring segment of length L>=2, with endpoints
in one actual carrier and columns in [1,n-2], casts L+2 distinct boundary holes
(n>=5). Consequently p=4 and n>=7 give `D>=L+6`.

Cancelling the shared pure mass against the existing contact budget yields
`|S|+2p<=b+2r` (n>=7), without adding overlapping charges. The endpoint
`residueTwo_card_le_target_of_covered_shadow_cost` gives f<=T for k>=5
**if `|S|+2p+b+2c>=6k+19`**. This sufficient physical certificate is not
guaranteed in covered configurations. For p=4 it is `|S|+b+2c>=6k+11`;
the k=5 regression checks the general threshold 49 implies f<=110.
Neither module gives a new unconditional upper or lower bound or closes the
one-excess or all-sides-covered branch.

### Terminal-Rail Repair (2026-09-06)

The three `Constructions/ResidueTwo/RailRepair/` modules prove the repaired
coordinate family, its physical support intersections and forest gluing, and
its exact inner cardinality `3s^2+1+floor(s/2)` for s>=2. The full score is
`3s^2+12s+12+floor(s/2)` on side 3s+5. With k=s+1, the unconditional endpoint
`GridGraphs.RailRepair.residueTwo_le_maxPreserved` proves

```text
L(k) = 3k^2+6k+3+floor((k-1)/2) <= P(3k+2),    k>=3.
```

It gains one over the historical staircase at odd k and agrees at even k.
The new uniform theorem gives 110 at side 17, 195 at side 23, and 304 at
side 29. The current proved intervals are [110,114], [195,201], and [304,312];
110 at side 17 matches the existing finite lower witness, not a proof of
exact P(17). The global upper formula is unchanged.

This is a single terminal parity repair, not an accumulating target-count
pump. `score_step_two` still gives 12s+37, equivalently 12k+25, one short of
the stable target gain 12k+26. Its deficit from `3k^2+7k-1` is
`floor(k/2)-2` in the stable range k>=5.

### Historical Six-Width Seeds (2026-09-06)

The actual staircase has b=5 and `r+c+3*((s+1)/2)=6*s+7`, s>=2,
side 3s+5. Kernel-checked fixed induced edge counts 39 and 64 yield seed
profiles `(f,r,c,b)=(48,9,7,5)` at side 11 and `(76,12,7,5)` at side 14.
These scores are not the optimal early scores 49 and 77. They match the stable
polynomial at k=3 and k=4 but do not establish a pumping invariant.
The checked actual s->s+2 gain is 12s+37 preserved vertices and 9 combined
component units, not the target gain 12s+38. Separate uniform component counts
and target-count geometric closure remain unproved. This historical family's
lower bound `3k^2+6k+2+k/2`, k>=3, is now improved at odd k by RailRepair.

The new lower-side Python experiments and L2 research documents are
paper-level evidence only, distinct from the new Lean repair theorem. They do
not prove a target-count pump; no Python search or test was run in this Lean
verification pass. Joint-notch and new paper searches remain finite side-11/14
research, with no new formal construction or bound claim.

### Boundary-Stratified Upper Bound (2026-09-06)

`GridGraphs/Accounting/BoundaryStratifiedCarrierBound.lean` proves
`P(n)<=n*(n*n+4*n-7)/(3*n+1)` for n>=7. The b=5 case uses the empty next ring
to bound deep carriers by n-4 and requires at least four boundary carriers;
the b>=6 case pays an additional unit in the ledger. No optimizer normalization
is assumed. The closed residue-two upper bound is `3k^2+7k+(2k+3)/3`, k>=2.

`maxPreserved_ten_ten` proves `P(10)=42` by matching this bound to the known
construction. With RailRepair, side 23 has the proved interval `[195,201]`; side 26 remains
`[246,254]`. Counterexample-budget profiles and the local two-row packing
restriction are also checked, without asserting a sharp general exclusion.
All new result axiom audits contain only the standard logical axioms.

### Carrier-Length Upper Bound (2026-09-06)

`GridGraphs/Accounting/CarrierLengthBound.lean` proves
`P(n)<=n*(n*n+4*n-6)/(3*n+1)` for n>=5 by injecting each straight preserved
component into one coordinate and summing cardinalities. This is an
unconditional upper bound, not an interface assuming universal waste.

At side 7 it matches the existing lower construction, giving the unconditional
theorem `maxPreserved_seven_seven` in `Results/SmallDiagonalExact/Seven.lean`.
The original carrier estimate gives intervals [194,202] and [246,254] at sides
23 and 26; the boundary-stratified improvement above tightens the first.
The tests specialize structural theorems rather than optimize those grids.
The new theorem axiom audits contain only the standard logical axioms.

`Results/SmallDiagonalExact.lean` is now an aggregate over the split exact-case
proofs. Earlier line-number references to that file are historical; public
theorem names remain unchanged. No split module exceeds 708 lines.

### Boundary-Five Component Obstruction (2026-09-05)

The historical improved family is formalized in `ResidueTwoStaircase.lean`
and `ResidueTwoStaircaseForest.lean`. The latter proves unconditionally
`3k^2+6k+2+k/2 <= maxPreserved (3k+2) (3k+2)` for k>=3 through actual
coordinate geometry and forest gluing. It is strictly stronger than the affine
bound for k>=8, not a proof of the conjectured optimum. The side-26 regression
is a specialization of the arbitrary-width theorem, not a grid search.
RailRepair now improves this lower formula at odd k, as recorded above.

`GridGraphs/Accounting/BoundaryFiveBudget.lean` proves `b>=5` for every feasible forced
set on a square of side at least five. Combined with the existing component
ledger, it proves `r<=3k+6` at cardinality `3k^2+7k` on side `3k+2`, and
rules out the retained `4k` and counter `4k+1` component architectures in
their stated ranges. These are arbitrary-width structural proofs, not finite
census results. The four exported theorems use only `propext`,
`Classical.choice`, and `Quot.sound`; targeted and full builds passed.

The tests at sides 20 and 23 instantiate those universal theorems rather than
evaluate or optimize grid configurations. Exact residue-two lower and upper
bounds remain open. The boundary-five unique gap and next-ring exclusion are
now checked in `GridGraphs/Accounting/BoundaryFiveEquality.lean` on 4.33.1. Its five
exported results have axiom audits containing only `propext`, `Classical.choice`,
and `Quot.sound`. Symbolic tests cover uniqueness at side 8 and next-ring
exclusion at the threshold side 7.

`BoundaryFiveFrame.lean`, `BoundaryFiveAttachment.lean`, and
`BoundaryFiveConstruction.lean` now check the actual canonical frame tree,
the necessary-and-sufficient attachment condition, and the exact counted
extension. The principal axiom audits use only the standard logical axioms.
The residue-two bound-transfer theorem is conditional: an actual inner set of
the required cardinality and attachment type is still missing. Arbitrary-b=5
normalization and the separate smaller-grid Q reformulation are not yet fully
formalized; see `analysis/BOUNDARY_FIVE_PEELING.md`.

### `GridGraphs/Core/Defs.lean`

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

### `GridGraphs/Core/Bounds.lean` — algebraic bound expressions

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

### Exact `4 x n` family

`ForcedMaximum.lean` proves that `maxPreserved` is exactly the maximum size of
an acyclic forced vertex set. `WidthFourLower.lean` realizes `2n` vertices by
the top and bottom forced combs. `WidthFourExact.lean` splits cotree incidence
waste by checkerboard color: each color waste is a positive multiple of three,
so each color contains at least `n` non-preserved vertices.

| Lemma | Statement |
|-------|-----------|
| `maxPreserved_eq_maxForcedAcyclic` | spanning-tree and forced-forest maxima agree on nonempty grids |
| `two_mul_le_maxPreserved_widthFour` | `2*n ≤ maxPreserved 4 n` for `n≥2` |
| `maxPreserved_widthFour_le_two_mul` | `maxPreserved 4 n ≤ 2*n` for `n≥2` |
| **`maxPreserved_widthFour_eq_two_mul`** | **`maxPreserved 4 n = 2*n` for `n≥2`** |
| `maxForcedAcyclic_widthFour_eq_two_mul` | exact forced-forest form of the same theorem |

### `GridGraphs/Core/Forced.lean` — forced edges

| Lemma | Statement | Location |
|-------|-----------|----------|
| `forcedEdgeGraph` (def) | the subgraph of all `G`-edges incident to some `F`-vertex | `Forced.lean:27` |
| `preservesIncidentEdges` (def) | edge-containment formulation of full-degree | `Forced.lean:43` |
| `forcedEdgeGraph_le_of_preserves` | preserved → forced edges lie in `T` | `Forced.lean:48` |
| **`forcedEdgeGraph_isAcyclic_of_preserves`** | **forced-edge graph of preserved set in acyclic `T` is acyclic** | `Forced.lean:58` |
| `grid_forcedEdgeGraph_isAcyclic_of_preserves` | grid specialisation | `Forced.lean:73` |

### Incidence-waste and forest-component accounting

| Lemma | Statement |
|-------|-----------|
| `incidenceWaste_add_twice_card_edges` | `W + 2|E| = 3|support|` under maximum degree three |
| `incidenceWaste_exchange_balance` | exact arbitrary equal-edge support exchange balance |
| `incidenceWaste_int_delta` | signed formula `Delta W = 3(new-lost)` |
| `IsAcyclic.card_edgeFinset_add_card_connectedComponent` | finite forest ledger `|E|+c=|V|` |
| `grid_cotree_incidenceWaste_identity` | `W + D + 3*numPreserved = 3mn` for a grid spanning tree |
| `diagonal_cotree_incidenceWaste_ge_iff_preserved_bound` | `W>=n+2` iff the additive diagonal full-degree bound holds |
| `grid_component_reduction` | exact full-set forced-forest component identity |
| `grid_prefix_component_ledger` | exact subtraction-free row-prefix charge identity |
| `square_grid_component_reduction_compl` | exact square `U`-form of `Q_U+c_F+c_H` accounting |
| `square_grid_tree_component_bridge` | exact identity `Q_U+c_F+c_H = W+2` for a square-grid spanning tree cotree |
| `incidenceWaste_ge_of_combinedChannelContourRouting` | joint exit and merger/root resource routing implies `W>=n+2` |
| `incidenceWaste_ge_of_prunedRootChannelRoutingWithDirectExits` | direct and later exits imply `W>=n+2` when exit roots replace, rather than duplicate, carrier terminals |
| `incidenceWaste_ge_of_channelMergerResources` | concrete merger factorization hypotheses discharge the joint routing premise |
| `GridChannelContourRealization.incidenceWaste_ge` | every complete geometric realization gives the universal `W>=n+2` bound |
| `CanonicalShoreDemand.boundaryIncidence_injective` | the `n+3` canonical demands have distinct side-labelled boundary germs |
| `CanonicalShoreDemand.directExitEmbedding` | support-based direct germs inject into actual split outer ports |
| `canonicalShoreDemandEmbedding` | every continuing canonical demand is a private leaf in the launched-shore forest |
| `canonicalShoreTerminalTreeEdgeEmbedding` | merger-child and maximal-root attachment edges are jointly distinct tree edges |
| `canonicalTerminalResources_iff_card_le` | the exit-free prototype's terminal-resource condition is exactly the global internal-edge/component cardinal inequality |
| `square_grid_tree_universalWaste_of_canonicalTerminalResources` | that conditional prototype resource theorem implies `W>=n+2`; universality is not asserted |
| `uResidueTwoAffine_dual_connected` | the affine residue-two U-U dual is connected for every `k>=5` by symbolic width-three edge transport and face attachment |
| `residueTwoAffine_uniform_le_maxPreserved` | unconditional near-target lower bound `3k^2+6k+5 <= P(3k+2)` for every `k>=5` |
| `SimpleGraph.IsAcyclic.sup_of_support_inter_subsingleton` | two forests glued along at most one active vertex have acyclic union |
| `IntervalStarGluingOrder.forcedEdgeGraph_isAcyclic` | a leaf-elimination order with unique physical attachments proves acyclicity of the complete forced interval-star union |
| `card_carrierQuotient_add_card_collision` | raw terminal occurrences split exactly into distinct carrier classes and labelled duplicate contacts |
| `PhysicalTreeTokenQuotientRouting.resourceEmbedding` | canonical internal-edge and component reservations plus residual collision routing reconstruct the full terminal embedding |
| `nonempty_physicalTreeTokenQuotientRouting_iff_card_le` | residual collision routing exists exactly when unreserved internal-edge/component capacity covers all labelled collisions |
| `square_grid_tree_universalWaste_of_canonicalCollisionRouting` | universal waste follows if every canonical forest admits the exact residual collision routing |
| `GridExpandedContour.equiv_isCycle_of_spanningSquareTree` | the contour refined to all vertex/compass slots is one cycle for every nontrivial spanning square-grid tree |
| `MarkedCycleFirstStop.leaves_eq_demands` | demand-reachable first-stop restriction shares suffixes while private starts remain exactly all leaves |
| `CanonicalExpandedContourForest.exitEmbedding` | reached first-stop roots use distinct geometric split outer ports |
| `CanonicalExpandedContourForest.mergerSlotTreeEdgeEmbedding` | expanded-contour merger slots use distinct unsupported canonical inward tree edges |
| `canonicalExpandedJointCollisionRouting_iff_incidenceWaste_ge` | port-aware residual collision capacity is exactly equivalent to the universal waste target |
| `MarkedCycleFirstStop.canonicalMergerSlotUnmarkedStartEmbedding` | merger slots use injective orbit-local owners, including marked direct-start endpoints |
| `rankedCarrierCollisionEquiv` | ordered carrier representatives split occurrences into first contacts and later collision labels |
| `localizedHall_iff_exists_embedding` | localized Hall inequalities are exactly equivalent to injective neighborhood-respecting routing |
| `HorizontalSouthBareComb.gapResourceEmbedding` | every gap in a bare comb uses a distinct internal edge or labelled cotree transition; symmetric APIs cover the other orientations |
| `RankedTransitionSystem.exists_terminalState_same_origin` | every occurrence-indexed decreasing transition chain terminates without losing its debt provenance or quotienting reconverged labels |
| `gridTreeCell_internal_or_labelledCotree` | every grid-tree cell supplies an internal supported edge or an exact labelled cotree transition on one side |
| `orderedHullDepth_concentric` | for every `k`, a pairwise laminar family of `k` nested ordered hulls crosses one cut, disproving any laminarity-only fixed hull bound |
| `ReconvergenceLens.rank_parent` / `parentWellFounded` | nearest later-merger lens parents strictly decrease first-stop distance and form a well-founded occurrence forest |
| `ReconvergenceLens.reachedStop_eq_of_parent` | child and parent lenses continue to the same reached marked stop |
| `CanonicalExpandedContourForest.collisionLensEmbedding` | every canonical expanded-contour merger occurrence embeds into its occurrence-level lens |
| `CanonicalExpandedContourForest.lensTreeEdgeEmbedding` | every canonical lens retains a distinct physical unsupported inward tree-edge token |
| `CanonicalExpandedContourForest.lensOuterPort_eq_of_parent` | parent-related canonical lenses reach the same split outer cotree port |
| `ReconvergenceLens.originRegion_ssubset_of_parent` | parent passage strictly enlarges the finite set of originating start occurrences; this is not planar containment |
| `CanonicalExpandedContourForest.lensMergerBranches_children_eq` | every canonical lens merger has exactly its private start and unique shared predecessor as children |
| `CanonicalExpandedContourForest.lensMergerBranches_sharedPredecessor_eq_pred` | the shared branch enters from the explicit predecessor slot of the expanded contour |
| `GridExpandedContour.edges_walk` / `darts_walk` | erasing in-place expanded-contour turns gives an honest retained-tree walk with exactly the collected ordered darts and edges |
| `ReconvergenceLens.iterate_rank_mergerState_eq_reachedStop` | iterating a lens merger through its stop-distance rank reaches its common marked terminal |
| `CanonicalExpandedContourForest.edges_lensSharedSuffixWalk` | the canonical merger-to-outer-port suffix is realized as an exact retained-tree walk |
| `CanonicalExpandedContourForest.lensBranchGerm_darts_ne` | when both local branch germs traverse retained edges, their oriented darts are distinct |
| `GridExpandedContour.slotPoint_injective` | distinct expanded slots map to distinct sector points in the fourfold collar grid |
| `GridExpandedContour.segmentMidpoint_injective` | distinct expanded successor segments have distinct collar midpoints |
| `GridExpandedContour.segmentMidpoint_ne_slotPoint` | no collar segment midpoint collides with any slot-sector point |
| `GridExpandedContour.collarTrace_isPath_of_advance_injective` | every slot-injective expanded interval realizes as an actual path in the collar grid |
| `GridExpandedContour.spanningTreeCollarCycle_isCycle` | the complete expanded contour orbit is a genuine cycle in the fourfold collar grid |
| `CanonicalExpandedContourForest.inwardShoreCollarCycle_isCycle` | a retained inward dart, its reverse contour arc, and an explicit edge chord bound a genuine local cycle |
| `CanonicalExpandedContourForest.canonicalUpperU1Default` | unconditional U1 certificate with concrete rooted shore regions, corrected planar parent forest, and outer boundary roots |
| `CanonicalExpandedContourForest.CanonicalUpperU2ExposedOwnership` | exposed ports, internal edges, and selected free-component contacts have unique first owners and injective physical embeddings |
| `parentForest_global_le_of_regional_telescope` | regional passed-transition terms cancel over a ranked parent forest |
| `canonicalUpperU3_localInequality_implies_globalHall` | the one-region debt inequality implies global Hall for first-owned resources |
| `planarLensLocalDebtEquivFin` | local occurrence debt is exactly the merger-excess index `Fin (q-1)` |
| `planarLensLocalDebtInterfaceGapEmbedding` | the `q-1` debts born at a reconvergence use distinct immediate-child collar interface lanes |
| `canonicalUpperU3_activeLocalInequality_globalHall` | corrected one-state-per-debt regional inequalities imply global Hall after selected passes telescope |
| `canonicalPlanarLensDebtRouting` | every original merger-slot occurrence is routed along its unique planar parent chain with exact local/child flow conservation and preserved provenance |
| `canonicalPlanarLensDebtRouting_carriesCanonicalLocalInterfacesAt` / `canonicalPlanarLensDebtRouting_passesIncomingAt` | canonical routing discharges all nonroot local-interface and inherited-pass obligations |
| `planarLensOriginalDebtFirstStopMergerEmbedding` | every planar merger debt selects a distinct immediate-child first-stop merger token |
| `planarLensOriginalDebtFullPrunedLaunchEmbedding` | selected tokens split injectively into one raw-component representative per carrier or an occurrence-labelled ranked collision |
| `FullPrunedRegionalCertificate.planarLensOriginalDebtPhysicalEmbedding` | any certified ranked collision continuation enlarges the launch to an injective map into raw boundary ports, internal edges, and components |
| `FullPrunedRegionalCertificate.rootActiveDebtFiberPhysicalEmbedding` | the enlarged physical map is injective on every planar root active fiber without asserting false root ownership |
| `CheckerboardBoundaryRuns` definitions | generic boundary component labels, cyclic run counts, nonalternation, and a proved cancellation bridge from two color-run bounds to `CheckerboardBoundaryBound`; the candidate color bounds themselves are false |
| `AxialCarrierGap` definitions | consecutive collinear non-singleton preserved components have finite, uniquely oriented complement gaps; parallel gaps are disjoint and perpendicular gaps intersect in at most one vertex |
| `CanonicalInsertionCircuit` definitions | maximal omitted vertices retain canonical attachment pairs, unique forced-forest paths, and exact orthogonal turn counts; no aggregate turn bound is asserted |
| `FiniteAlternatingExchange` | finite partial matchings, occurrence-labelled alternating reachability, certified augmentation, and Hall-deficient saturated closures |
| `AutomaticOwnershipDisplacement` / `GridGroupedAlternatingMatching` | reserved raw resources have unique automatic owners and grouped sources retain exact displacement adjacency |
| `AlternatingTreeExchange` / `RawFreeComponentContinuation` / `OrderedOuterBoundaryExchange` | occurrence-preserving internal-edge, component-contact, basis-exchange, and ordered outer-boundary continuation without duplicating physical resources |
| `PhysicalSaturationTransitionSystem` | all sound continuation mechanisms are packaged into one finite source-indexed reachability system with deduplicated raw-resource neighborhoods |
| `canonicalUpperU3_activeGlobalHall_of_canonicalRootHall` | for canonical routing, the corrected active global Hall theorem reduces solely to raw physical Hall at parentless roots |
| `rootDebtCanUse_eq_outerPort` | the audited root escape can expose only supported outer ports, never internal edges or raw components |
| `canonicalRootRawNeighborhood_card_le_one` | every canonical neighborhood in the former root-Hall endpoint is empty or a singleton |
| `canonicalUpperU3RootHall_activeFiber_card_le_one` | the former root Hall endpoint would force at most one accumulated active debt per planar root |
| `interfaceLane_eventTermination` | every occurrence-labelled interface/root-escape stream reaches a finite geometric event with provenance preserved |
| `no_planarLensRegionalAssignment_of_unaryRoot_obstruction` | the rejected all-crossing ledger can demand capacity at a resource-empty unary root |
| `canonicalFirstMarkedEvent_not_injective_of_reconvergence` | any first-mark assignment factoring through a reconverged state identifies distinct origins |
| `card_primalContourResource_add_one_eq_fourSideComponentRank` | the primal routing resource count plus one is exactly four-side component rank |
| `square_grid_tree_universalWaste_of_universalPrimalContourRouting` | an explicit canonical-demand routing into primal contour resources implies `W>=n+2` |
| `outerEdgeAtPosition_mem_clockwiseOuterArc_iff_openCyclicSector` | a selected collar outer edge lies on the clockwise closure exactly for positions in the corresponding open boundary sector |
| `residueTwoAffine_target_eq_compl_card_add_gap` | the stable residue-two target exceeds the affine preserved score by exactly `k-5` |
| `uResidueTwoAffine_compl_card_step` / `residueTwoStableTarget_step` | affine pumping gains `6k+9` preserved vertices while the exact target recurrence requires `6k+10` |
| `square_cotree_black_waste_ledger` / `square_cotree_white_waste_ledger` | exact checkerboard-color decomposition of cotree incidence waste |
| `card_blackCotreeContourMark_eq_incidenceWasteOn` | black contour marks have exactly black incidence-waste cardinality, with a white analogue |
| `CanonicalShoreDemand.card_phase_colors_even` / `card_phase_colors_odd` | exact six phase/color demand histograms in residue two |

All statements are subtraction-free over `Nat` where possible. Component
counts for the induced full-vertex graph use the subtype vertex set, so the
empty-set case contributes zero components rather than ambient isolated
vertices.

### `GridGraphs/Geometry/Diagonal.lean` — induced-edge decycling and cell hitting

| Lemma | Statement | Location |
|-------|-----------|----------|
| `IsInducedEdgeDecyclingSet` (def) | `forcedEdgeGraph G Uᶜ` acyclic | `Diagonal.lean:22` |
| `forcedEdgeGraph_compl_adj_iff` | `Uᶜ`-forced graph = grid edges not internal to `U` | `Diagonal.lean:27` |
| `compl_isInducedEdgeDecyclingSet_of_preserves` | `Fᶜ` is decycling for any preserved `F` | `Diagonal.lean:47` |
| `fourCycle_has_unforced_edge` | every acyclic 4-cycle has a `U-U` boundary edge | `Diagonal.lean:57` |
| `gridGraph_cell_adj_top` etc. | the four boundary edges of every cell are grid edges | `Diagonal.lean:130–145` |
| `cell00_ne_cell11`, `cell01_ne_cell10` | diagonal disequalities | `Diagonal.lean:148,155` |
| **`grid_cell_has_unforced_edge`** | **every grid 2×2 cell has at least one `U-U` boundary edge** | `Diagonal.lean:164` |
| `grid_tree_cotree_support_row_or_column_coverage` | cotree support meets every row or every column | `UniversalWaste.lean` |
| `grid_cell_has_unforced_corner` | every cell contains at least one corner outside `F` | `Diagonal.lean:180` |
| `preserved_set_cell_corner` | spanning-subgraph form of the cell-hitting condition | `Diagonal.lean:195` |
| `connected_graph_has_spanning_tree` | wrapper around mathlib's `Connected.exists_isTree_le` | `Diagonal.lean:214` |

### `GridGraphs/Geometry/GridDual.lean` — explicit rectangular dual

| Lemma | Statement | Location |
|-------|-----------|----------|
| `horizontalPrimalEndpoints_adj` | every horizontal coordinate edge is a grid edge | `GridDual.lean` |
| `verticalPrimalEndpoints_adj` | every vertical coordinate edge is a grid edge | `GridDual.lean` |
| `gridGraph_adj_exists_coordinate_edge` | every grid adjacency has a horizontal/vertical coordinate witness | `GridDual.lean` |
| `uuDualGraph_adj_iff` | exact U-U dual adjacency characterization | `GridDual.lean` |
| `hasDualEndpoints_iff` | same-side predicates are invariant under unordered endpoint orientation | `GridDual.lean` |
| `cycleComplementDualGraph` / `cycleInteriorFaces` | face graph avoiding cycle edges, and faces unreachable from `out` | `GridDual.lean` |
| `rowRayCrossingEdges` / `FaceRowRayOdd` | finite vertical crossings of a cell's leftward row ray and their parity | `GridDual.lean` |
| `even_walkCutCrossings_iff` | walk cut crossings are even iff endpoint sides agree | `GridDual.lean` |
| `even_walkCutCrossings_of_isClosed` | every closed walk crosses every Boolean cut evenly | `GridDual.lean` |
| `even_gridRowPrefix_crossings` / `even_gridColumnPrefix_crossings` | row/column prefix cut parity for closed grid walks | `GridDual.lean` |
| `gridCycle_even_incident_edges` | every cycle vertex has even edge-list incidence count | `GridDual.lean` |
| `out_not_mem_cycleInteriorFaces` | the unbounded face is not in the unreachable-face set | `GridDual.lean` |
| `horizontal_mem_cycleInteriorFaces_iff_of_not_mem_edges` and vertical counterpart | an unused primal edge has both incident faces on the same reachability side | `GridDual.lean` |
| `horizontal_not_mem_forcedCycle_edges` and vertical counterpart | no U-U edge is traversed by a forced-`Uᶜ` walk | `GridDual.lean` |
| `reachable_mem_iff_of_respectsCut` | every reachable pair lies on the same side of a respected cut | `GridDual.lean` |
| `not_connected_of_respectsCut` | a graph respecting a nontrivial cut is disconnected | `GridDual.lean` |
| `cycleComplementDualGraph_respects_faceRowRayOdd` | row-ray parity is invariant along complement-dual walks | `GridDual.lean` |
| `gridCycleEnclosesBoundedFace_of_rowRayParity` | an odd face is unreachable from parity-zero `out` | `GridDual.lean` |
| `uuDualGraph_respectsCut` | grid-edge same-side conditions imply that the U-U dual respects the face cut | `GridDual.lean` |
| `gridPrimalCycleFaceCut_of_cycleEnclosesBoundedFace` | unreachable faces supply every clause of the finite primal face cut | `GridDual.lean` |
| `gridPrimalCycleFaceCut_of_rowRayParity` | row-ray parity supplies the finite primal face cut | `GridDual.lean` |
| `countP_edgeCrossesRowRay_eq_card` | a trail's filtered crossing count equals `rowRayCrossingEdges.card` | `GridDual.lean` |
| `gridCycleRowRayParity` | every simple forced grid cycle has an odd face and unused edges preserve row-ray parity | `GridDual.lean` |
| `gridDualCycleSeparation_of_primalCycleFaceCut` | finite cycle-face-cut separation implies `GridDualCycleSeparation` | `GridDual.lean` |
| `gridDualCycleSeparation_of_cycleEnclosesBoundedFace` | bounded-face enclosure directly implies `GridDualCycleSeparation` | `GridDual.lean` |
| `gridDualCycleSeparation_of_rowRayParity` | row-ray parity directly implies `GridDualCycleSeparation` | `GridDual.lean` |
| `gridDualCycleSeparation` | unconditional rectangular-grid primal/dual cycle separation | `GridDual.lean` |
| `isInducedEdgeDecyclingSet_of_uuDual_connected` | cycle separation plus dual connectivity gives decycling | `GridDual.lean` |
| `exists_isTree_preserving_compl_of_uuDual_connected` | conditional preserving-tree construction endpoint | `GridDual.lean` |
| `exists_isTree_preserving_compl_of_uuDual_connected_grid` | unconditional preserving-tree endpoint | `GridDual.lean` |

The row-ray chain is complete. The proof identifies filtered counts on the
cycle trail with `rowRayCrossingEdges.card`, proves horizontal parity using a
finite segment cut, handles vertical prefixes including both boundaries, and
obtains an odd incident face from an arbitrary cycle edge. The resulting face
cut proves unconditional `GridDualCycleSeparation` and the preserving-tree
endpoint above.

`ConnectivityTransport.lean` also packages the generic construction-side
principle used by both residue-two step interfaces: source adjacencies may map
to target paths, and target vertices need only attach to the source image for
connectivity to transport.

### `GridGraphs/Constructions/ResidueOne/ResidueOne.lean` — residue-1 diagonal `U` cardinality

For `n = 3k + 1` (square grid `n × n`), the residue-1 lower-bound construction
`residue_one_pattern` from `analysis/patterns/diagonal_patterns.py` (see Proposition L1
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

### Operational diagonal theorem API

| Lemma | Statement |
|-------|-----------|
| `maxPreserved` | finite maximum over all grid spanning subtrees |
| `exists_spanningSubtree_numPreserved_eq_maxPreserved` | the maximum is attained on every nonempty grid |
| `uuDualGraph_uResidueOne_connected` | residue-one U-U dual connectivity for every `k>=1` |
| `residueOne_le_maxPreserved` | unconditional lower bound `3k^2+5k` |
| `uResidueZero_card` | residue-zero phase family has size `6k^2-3k+2` for `k>=7` |
| `phaseRows_adjacent_valid` | every recursive residue-zero row transition is one of six symbolic classes |
| `residueZero_le_maxPreserved_of_interior` | target residue-zero lower bound from the isolated interior-frontier certificate |
| `ResidueZeroAnchorCertificate` | widening-stable bounded-anchor formulation and conditional lower-bound chain |
| `maxPreserved_eq_diagonalFormulaP` | the four named open hypotheses imply the proposed formula for all `n>=3` |

The residue-zero chain is now unconditional for every `k>=7`. Explicit
ranked-parent U-U dual certificates also prove the target construction lower
bounds at `n=3,5,6,8,9,11,12,14,15,17,18,20`. Consequently the strengthened
final assembly theorem assumes only the arbitrary-width residue-two
construction tail beginning at `n=23`; the three upper-bound structural
hypotheses remain separate.

The elementary perimeter theorem now gives unconditional cotree-waste floors
`W>=3` in residue one and `W>=4` in residues zero and two, improving the
generic diagonal maximum bounds without any solver. The intermediate linear
target is formally equivalent to `n+2 <= fourSideComponentRank`, where the
rank is the sum of four boundary-support cardinalities and the two exact forest
component counts. The affine residue-two family is also encoded symbolically
with exact cardinality and recurrence; its arbitrary-width dual connectivity
is reduced to four local width-three step obligations rather than asserted.

An exact-count twenty-based residue-two pump is now also formalized: its U count
is `6k^2+5k+4`, with increments `12k+11` and `24k+34`, and its base is exactly
the proved `n=20` certificate. The arbitrary-width theorem is not claimed:
three symbolic old-edge/path and new-face attachment fields remain. On the
upper side, hypothetical `W=n+2` and `W=n+5` profiles now have fully proved
support sizes and component ranks; the missing facts are geometric
nonexistence/debt theorems, not accounting identities.

The exact pump and its first balanced seam repair have now both been ruled out
symbolically in Lean. The original pump isolates a checkerboard face at its
first repeated-column seam. Adding that missing seam vertex and deleting a
carried vertex preserves the exact count, but the deletion creates a closed
two-face dual component at every positive pump depth. Thus there remains no
proved target construction at `n=23`; these cardinality-correct families are
explicit negative controls rather than construction hypotheses.

The upper-bound program now also has a checkerboard formulation. The black and
white full-center star graphs are proved acyclic, and their ambient component
sum is exactly the old component charge plus the cotree-support cardinality.
Consequently the subtraction-free checkerboard boundary inequality is proved
equivalent to `W>=n+2`. Its exact slack is formalized as well: slack zero is
`W=n+2`, and slack three is `W=n+5`. These are reductions, not assertions of
the still-open disk-coupled boundary inequality or its equality exclusions.

The plane tree contour is now formal rather than heuristic. Coordinate grid
edges are equivalent to abstract grid edges without collapsing parallel dual
boundary incidences. Clockwise rotation of directed tree edges defines a finite
permutation. A generic finite-permutation cut lemma, bridge shores, local
rotation, and tree connectivity prove that this permutation is one cycle.
Supported boundary sectors and supported repeated tree visits form a finite
`CotreeContourMark` type whose cardinality is proved equal to incidence waste.
Return marks are additionally realized as actual outgoing contour darts.
Every fundamental shore is proved to be one contour interval with a unique
entry and exit, and its ambient cut is exactly its attachment edge plus
edge-labelled cotree ports. Lane routing into the disjoint sum of internal
marks and outgoing ports now has an exact cardinal criterion. Occurrences of
one labelled port are proved convex along nested shores, and a local routing
with an injective outside-port discharge is proved to yield a mark injection.
Independently,
the primal contour ledger proves
`W+1 = boundary(U) + internalTreeEdges(U) + components(grid[F])`.
No global injection is asserted yet: the remaining step is to compose the
local routings through nested shores while discharging ports without reuse.

### `GridGraphs/Core/Spanning.lean` (refined) — `preserved_le_refinedUB`

Phase 8.refined. Adds vertex-class predicates and the matching upper-bound
theorem.

| Lemma | Statement | Location |
|-------|-----------|----------|
| `isCornerVertex` / `isBorderVertex` / `isInteriorVertex` (defs) | vertex-class predicates | `Spanning.lean` |
| `vertexClass_trichotomy` | every vertex is exactly one class | `Spanning.lean` |
| `vertexDeficiency_le_of_corner`/`_of_border`/`_of_interior` | per-class caps via predicates | `Spanning.lean` |
| `interior_card_eq` | `\|interiorSet\| = I m n` | `Spanning.lean` |
| **`preserved_le_refinedUB`** | **`numPreserved m n T ≤ refinedUB m n` for spanning subtrees** | `Spanning.lean` |
| `forall_spanning_subtree_preserved_le_refinedUB` | ∀-quantified form | `Spanning.lean` |

### `GridGraphs/Forests/ForestExtension.lean` — Forest extension

Standalone, generic lemma. Mathlib-style.

| Lemma | Statement | Location |
|-------|-----------|----------|
| **`SimpleGraph.isAcyclic_extends_to_isTree`** | any acyclic `F ≤ G` in a finite connected graph extends to a spanning tree of `G` | `ForestExtension.lean` |

Generalises mathlib's `Connected.exists_isTree_le` (case `F = ⊥`). Used
to convert any acyclic forced subgraph into a real spanning tree
witness.

### `GridGraphs/Constructions/DoubleComb.lean` — Lower-bound construction (partial)

Definitions and connectivity for the simpler "top spine + every column"
spanning-tree candidate, plus the L-bend forced-subgraph framework.

| Lemma | Statement | Location |
|-------|-----------|----------|
| `lBendForced` (def) | the L-bend forced subgraph (top + left + verticals + horizontals minus corner cycle) | `DoubleComb.lean` |
| `lBendForced_le_gridGraph` | L-bend ≤ gridGraph | `DoubleComb.lean` |
| `topSpineColumns` (def) | top row spine + every column verticals | `DoubleComb.lean` |
| `topSpineColumns_le_gridGraph` | candidate ≤ gridGraph | `DoubleComb.lean` |
| `topSpineColumns_connected` | the candidate is connected for `m, n ≥ 1` | `DoubleComb.lean` |
| `topSpineColumns_preserves_top_row` | every top-row vertex is full-degree in the candidate | `DoubleComb.lean` |

Still deferred (in this file): the `IsTree` proof of `topSpineColumns`
(needs edge count via degree-sum + `isTree_iff_connected_and_card`), the
headline existence theorem, and the L-bend acyclicity proof.

### `GridGraphs/Tests/Regression.lean` — small-grid sanity tests

A regression suite of `decide`-evaluated `example`s pinning Lean values
of `D`, `basicUB`, `refinedUB`, `lowerB`, the vertex-class counts, and
`uResidueOne k` cardinalities to specific small-grid values matching
`lean/results-empirical.csv`. Any regression in the bound expressions or
vertex counts breaks `lake build`.

### `GridGraphs/Core/Spanning.lean` — operational upper bound `P(m,n) ≤ basicUB m n`

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

Phase 8 (basic + refined upper bounds, total deficiency, forest extension)
is now **complete**. For the exact diagonal formula, the construction side is
complete through `n=20`, complete for every residue-zero and residue-one width,
and open only for the residue-two tail `n>=23`. The universal waste bound and
its equality refinements remain the independent upper-bound gaps.

- Headline existence theorem `lowerB m n ≤ maxPreserved m n` (i.e. there
  exists a spanning tree achieving `numPreserved ≥ m + n − 2`). The
  L-bend forced subgraph and the simpler `topSpineColumns` candidate
  are both defined in `DoubleComb.lean`; `topSpineColumns` is proved
  connected and shown to preserve all top-row vertices. The remaining
  step is to prove `IsTree` (via edge count) and combine with the
  preservation lemma.
- An exact-cost rooted open-slab transfer for `n=3k+2`, `k>=7`. Explicit Lean
  certificates cover the residue-two bases `n=5,8,11,14,17,20`, but no
  arbitrary-width target-count recurrence is known from `n=23` onward.

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

### Bounded proof-oriented censuses

- `check_residue_two_counter_interval_surgery.py` verifies the abstract
  root-edge subdivision formulas at `k=7,8,9,12`: total length
  `3k^2+7k`, one-parent tree structure, postorder elimination, and transition
  gain `6k+10`. It does not assert a grid realization.
- `census_residue_two_counter_interval_geometry.py` exhausts the explicitly
  declared `7 x 7` corner grammar at `k=7,8,9`. All 7,912,264 candidates fail
  the unit-cell obstruction; replay data is stored in
  `residue_two_counter_interval_geometry_census.json`. This excludes only the
  declared grammar and is not a proof dependency.
- `census_residue_two_affine_endpoint_extensions.py` classifies all `56`
  transported single-endpoint types from `k=7`; none survives through `k=9`.
  The exact target-count arithmetic remains abstractly valid, but every type is
  geometrically obstructed.
- `census_residue_two_endpoint_slide.py` derives `20` constant-size blockers
  from those obstructions and exhausts four unit translations for each. All
  `80` chains fail, narrowing the next topology to a two-leaf hinge exchange.
- `census_residue_two_two_leaf_hinge.py` derives exactly two legal leaf-hinge
  chains from seven late-stage witnesses; both fail at every tested width.
- `census_residue_two_nonleaf_spine_bypass.py` exhausts the five remaining
  witness-derived minimal bypasses. Each necessarily overlaps its carrier ray,
  giving a symbolic count obstruction for all `k>=7` within that grammar.
- Subsequent deterministic classifiers exhaust the two-layer dogleg, residue-
  zero cap/double-cap/sparse-rail splices, safe horizontal combs, all density-
  one-third periodic bulks through `6x6`, staircase seams, elbow islands, and a
  buffered three-wall branch. None supplies the target count together with a
  singleton-owned incidence tree. These are bounded negative results, not proof
  dependencies or a global nonexistence theorem.

### Diagonal `P(n, n)`

The square diagonal is the most-studied special case. `P(n, n)` is computed
exactly by the Rust DP for `n ≤ 10` (`results-empirical.csv`) and by the
forced-edge upper-bound DP plus completed-spanning-tree witnesses for
`n = 11..15` (`analysis/proofs_diagonal.md`). The conjectured closed form
(Conjecture C in `analysis/conjectures.md` and `docs/ROADMAP.md`) is

```
P(n, n) = ⌊n² / 3⌋ + n + C(n mod 3),    n ≥ 4,
```

where `C(1) = −1`, `C(0) = C(2) = −2`. Equivalently, the non-full set has
size `q(n)` from `lean/GridGraphs/Constructions/ResidueOne/ResidueOne.lean`'s `q` function, and
`P(n, n) = n² − q(n)`.

| n  | P(n, n) | basicUB(n, n) | refinedUB(n, n) | conjectured P |
|----|---------|---------------|-----------------|---------------|
| 1  | 1       | 1             | 1               | —             |
| 2  | 2       | 3             | 3               | —             |
| 3  | 4       | 6             | 5               | —             |
| 4  | 8       | 10            | 9               | 8             |
| 5  | 11      | 14            | 13              | 11            |
| 6  | 16      | 19            | 19              | 16            |
| 7  | 22      | 25            | 25              | 22            |
| 8  | 27      | 31            | 31              | 27            |
| 9  | 34      | 38            | 38              | 34            |
| 10 | 42      | 46            | 46              | 42            |
| 11 | 49      | 54            | 54              | 49            |
| 12 | 58      | 63            | 63              | 58            |
| 13 | 68      | 73            | 73              | 68            |
| 14 | 77      | 83            | 83              | 77            |
| 15 | 88      | 94            | 94              | 88            |

Observations:
- The conjectured closed form matches `P(n, n)` exactly at every
  `n = 4..15` (the conjecture's stated range; `n = 1, 2, 3` are listed
  as edge cases of the formula).
- `refinedUB(n, n) = basicUB(n, n)` for `n ≥ 6` and for `n ∈ {1, 2}`; only
  `n ∈ {3, 4, 5}` see a strict improvement (gap of 1). The refined bound
  thus has nothing extra to offer on the diagonal once `n ≥ 6`.
- The gap `basicUB(n, n) − P(n, n)` grows linearly: `2, 3, 3, 3, 4, 4, 4,
  5, 5, 5, 6, 6` for `n = 4..15`. This means the basic upper bound is
  **not** asymptotically tight on the diagonal — both `P(n, n)` and
  `basicUB(n, n)` are asymptotic to `n²/3`, but the difference grows like
  `n/3`. Asymptotic tightness on the diagonal would require a
  diagonal-specific upper bound (Phase 7c in `docs/ROADMAP.md`).
- `preserved_le_basicUB` (Phase 8) certifies the `P ≤ basicUB` column
  formally for **all** `n`, not just the empirically tested range.

---

## How the formal and empirical layers connect

The Lean proofs now cover **both** the algebraic bound expressions
(`basicUB`, `refinedUB`, `lowerB`, with their identities, monotonicity, and
ordering) **and** both operational upper bounds. Concretely, for any
spanning subtree `T` of `gridGraph m n`:

```
preserved_le_basicUB   : numPreserved m n T ≤ basicUB   m n
preserved_le_refinedUB : numPreserved m n T ≤ refinedUB m n
```

are now Lean theorems (Phase 8 of `docs/ROADMAP.md`, including the
refined branch). The empirical layer in this file (the `1 ≤ m, n ≤ 10`
table) was previously the *only* layer asserting these inequalities;
they are now also formally proved.

The forest-extension lemma `isAcyclic_extends_to_isTree` is now also
formally proved as a standalone, generic mathlib-style lemma. This is
the key bridge from "forced acyclic forest" to "spanning tree
realizing the construction".

What remains:
- The matching lower bound `lowerB m n ≤ maxPreserved m n`. The
  infrastructure (`topSpineColumns` connectedness + top-row preservation,
  the L-bend forced subgraph) is in place; the IsTree proof
  (via edge count) and headline existence theorem are the remaining
  pieces.
- The diagonal residue-1 lower bound, which would now follow from
  `isAcyclic_extends_to_isTree` plus acyclicity of the
  `(uResidueOne k)ᶜ`-forced graph.
