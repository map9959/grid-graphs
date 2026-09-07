# Astra Roadmap: Exact Square-Grid Optimum

Updated: 2026-09-06.

## Active Checkpoint

Read [the U1/U3/L2 handoff](HANDOFF_U1_U3_L2.md) before continuing. Earlier milestones checked the
boundary-six next-ring theorem, a stronger stable upper bound
`P(3k+2)<=3k^2+7k+floor((2k+2)/3)`, global U3 carrier-layer restrictions,
and the actual component budgets of the n11/n14 lower seeds. The previous milestone
proved that ANY missing open side implies f<=T+1 and b>=2k+3 for k>=5,
independently of p. Missing means no pure boundary carrier meets that side,
not zero preserved occupancy. No maximality or connectivity assumption beyond
forced-graph acyclicity is required. In particular p<=3 implies f<=T+1.
The last two-excess profile is excluded; f>=T+2 requires four distinct actual
pure carriers covering all four open sides. Those results remain valid.

The latest milestone strictly compiles five new modules: CarrierLayers
`OneExcessSeparated.lean`, `CoveredBoundary.lean`, and
`Constructions/ResidueTwo/RailRepair/{Geometry,Forest,Score}.lean`.
The terminal repair now has a uniform Lean forest and score theorem:
`L(k)=3k^2+6k+3+floor((k-1)/2)`, k>=3. With the existing upper-route notation
`T=3k^2+7k`, this is `T-floor(k/2)+2` for k>=5.
It gains one over the staircase at odd k and agrees at even k. Full strict
verification passed with 8,939 jobs and 147 public axiom audits (72+31+44).

Next goals: obtain enough root-separated holes to exclude one excess; address
the all-sides-covered branch using actual pure mass without double counting;
and find a propagating rail/attachment repair with the required
six-width gain. **PROOF NOT FINISHED:** no target pump or sharp general upper
bound is claimed. The global upper formula above is unchanged; the formal
lower bound is now L(k), not just the historical staircase score.

The previous milestone's five leaves under `Accounting/CarrierLayers/` are `MissingSide.lean`,
`MissingSideSharp.lean`, `RadialNearTightBoundary.lean`,
`RadialNearTightExclusion.lean`, and `RadialOneExcess.lean`, all strictly audited.
The earlier RadialTight exclusion left the unique numerical profile
`(r,c,b)=(k+2,1,2k+3)`; that was a historical intermediate result. Now, writing
q for roots on a missing side, physical root/pure-carrier nonreuse gives
q+p<=r and the near-tight bounds force p=3, q=k-1. An empty boundary triple
forces an inward F witness because c=1 forbids an ambient isolate at its middle.
Its new carrier gives r>=q+p+1=k+3, contradicting r=k+2. MissingSideSharp
extends the exclusion to any missing side, regardless of p.

For k>=5, p<=3, f>=T+1, the exact one-excess profile is
`f=T+1, r=k+2+a, c=1+d, b=2k+3+e`, with natural `a+d+e=3`.
For missing-side root deficit m=k-q, `m<=e+1` and `p<=a+m+2`.
At saturation `r=q+p`, equivalently `p=a+m+2`, distinct empty-block middles
are ambient isolates, giving `c>=m+1` and `m<=d`. Outside saturation,
inward witnesses may share a horizontal carrier; do NOT claim general nonreuse.
These necessary conditions do not exclude one excess.

`OneExcessSeparated` now proves `q+p+|S|+1<=r+c` for actual root-separated
hole middles S, without root saturation. An intervening preserved root proves
the needed inward-carrier nonreuse; holes in a shared root-free gap may still
reuse a horizontal carrier. For a missing side, k>=5 and `p+|S|>=7` give
the conditional sharp bound f<=T. No theorem guarantees such an S.

`CoveredBoundary` uses actual pure boundary mass P, not the maximum P(n).
Each nonpure carrier has at most two boundary contacts, giving
`B<=P+2(r-p)`; also `B<=P+E` for n>=5. For n>=7,
`4n-4<=P+2b` and `4n-4<=P+b+2(r-p)`. Here B/E are boundary/next-ring
preserved occupancy. These charge the SAME resources and cannot be added as
independent budgets. Neither upper front yields a new unconditional upper bound.

For L2, [the fixed-rail pocket note](L2_FIXED_RAIL_POCKET.md) gives a scoped paper argument:
repacking only the bottom two deep rows while keeping the frame and rails fixed
cannot beat the existing count. This is not yet a Lean theorem and does not
rule out a pump that changes a rail, an attachment, or another region.

[Terminal rail repair research](L2_RAIL_REPAIR_RESEARCH.md) gives a uniform
forest proof, now backed by uniform Lean theorems, with
`G(s)=3s^2+12s+12+floor(s/2)`, s>=2, n=3s+5.
It gains one over the staircase for even s and is count-neutral for odd s,
but still gains only 12s+37 per six-width step, not 12s+38. It is not an
accumulating pump: in k=s+1 notation the gain is 12k+25, not 12k+26. The module
`analysis.searches.l2_rail_repair_research` searched only n=11/14; with the
original frame and earlier rows fixed, last-four-deep-row repacking has finite
restricted-class maxima 49/76, not global optima. The historical packaging pass
passed three focused repair tests and seven layout tests without searches
during tests. An actual propagating repair must change the attachments that
cause the attempted repeated motif's component collision. The latest main-agent
test run passed 13 tests (three terminal, three propagating, seven layout),
without searches. The [propagating-interface alternative](L2_PROPAGATING_INTERFACE.md)
remains a paper forest argument for an unsuccessful actual-gain candidate,
not the verified single terminal repair or a target pump.

## Research Route Labels

These are the canonical meanings of U1/U2/U3/L1/L2/L3 from the latest plan.
Older planning documents sometimes used these labels differently. Use the
definitions here going forward. They are research routes, not six completed
theorems or a mandatory sequential pipeline. U means upper bound; L means
lower bound.

For n=3k+2, write `T(k)=3k^2+7k` (the conjectured value for k>=5). Here b is complementary
boundary deficiency, r counts induced preserved components, and c counts all
forced-graph components, including isolates. A pure boundary carrier is an
induced preserved component lying entirely on the outer boundary; p counts them.

| Label | Route | Goal and current position |
|---|---|---|
| **U1** | **Boundary-six control** | Analyze feasible sets with b=6, bound preserved vertices in the next ring, and use the resulting carrier capacity together with the b=5 and b>=7 branches. The next-ring bound and the improved unconditional upper bound `P(3k+2)<=T(k)+floor((2k+2)/3)` are checked for their stated ranges. This does not yet give the sharp upper bound. |
| **U2** | **Boundary-five attachment rigidity** | For arbitrary b=5 sets, prove boundary connectivity after the unique perimeter gap, classify actual inward attachments, and exclude a deep preserved carrier spanning all n-4 positions. Use that rigidity to sharpen the remaining b=5 profiles. Canonical-frame connectivity is checked; the full arbitrary-b=5 attachment and strict-capacity route remains open. |
| **U3** | **Global near-extremal packing** | Combine carrier lengths, boundary contacts, layer occupancy, and forced-component cost without resource reuse. Missing sides give f<=T+1; two excess requires four distinct side-covering pure carriers. Exact three-unit one-excess slack, root-separated hole charges, and actual pure-mass budgets are checked. The conditional f<=T bound needs p+\|S\|>=7, not guaranteed. One-excess exclusion and the all-sides-covered branch remain open. |
| **L1** | **Relayout and absorb uncovered vertices** | Rearrange the staircase's rails and attachments so that more uncovered vertices become legal promotion sites. Prove actual coordinates and attachments. The terminal parity repair is now checked, but a target-count relayout is not known. Disconnected forced forests and unrooted components are allowed. |
| **L2** | **Six-width pump from the small seeds** | Construct an actual `k -> k+2` operation gaining `12k+26`, with compatible 11x11/14x14 seeds (historical staircase scores 48/76 and budgets are checked). The uniform terminal repair L(k) is formal, but still gains only `12k+25`. The propagating-interface alternative remains paper-level and fails the actual target gain. No target pump or closure invariant is proved. |
| **L3** | **Alternative boundary or direct dual construction** | Leave the staircase architecture if necessary. Either choose another controlled boundary pattern, such as b=6, and pay its full component budget, or construct an unpreserved set U of size `6k^2+5k+4` with connected U-U dual. Actual coordinates and connectivity must give the target lower bound. No exact arbitrary-width alternative family is known. |

The selected emphasis is **U1 and L2, pushing into U3**. U2 supplies useful
attachment geometry; L1 and L3 remain alternatives rather than requirements.

Upper-route completion means an unconditional bound on every feasible set,
not merely an exclusion inside a chosen construction class. Lower-route
completion means a feasible target-count family at every required width.
Matching the two proves the optimum. A seed budget or a count recurrence alone
does not complete a lower route.

Source layout: the 232 Lean modules under `GridGraphs/` are grouped under `Core`, `Forests`,
`Geometry`, `Accounting`, `Routing`, `Surgery`, `Constructions`, `Results`,
and `Tests`. Construction families have their own subfolders. Public theorem
namespaces and the `import GridGraphs` entry point are unchanged; module
imports and live path references have been updated. See `lean/README.md` for
navigation. The reorganized source tree has passed a fresh full strict build,
including the five modules outside the aggregate import closure.

Python layout: the 283 former flat analysis sources now live in eight subject
packages with mirrored tests. Run them with `python3 -m analysis.<area>.<module>`
from the repository root. `analysis/README.md` documents the layout, bounded
checks, and historical provenance policy. Existing result artifacts were not
regenerated; source snapshots and an explicit before/after migration ledger
preserve their provenance. The smoke/layout suite and six targeted provenance
checks pass (29 tests total), with no optimization searches.

## Verification Status

Lean and mathlib are pinned to `v4.33.1`. The reorganized project passed full
verification with **zero errors and zero warnings**: 8,939 jobs, exit 0.
The command, run from `lean/`, was:

```bash
LEAN_NUM_THREADS=2 lake --no-cache --wfail build GridGraphs \
  GridGraphs.Tests.FourCropBoundaryCounterexample \
  GridGraphs.Tests.GroupedAlternatingClosureCounterexample \
  GridGraphs.Tests.InsertionReflexCounterexample \
  GridGraphs.Constructions.ResidueZero.ResidueZeroPersistentEnds \
  GridGraphs.Results.SmallDiagonal
```

This covers all 232 source modules, including the five outside the aggregate closure. It
reuses cached mathlib dependencies rather than running a separate mathlib-wide
verification. The completed log is `/tmp/opencode/u1-u3-l2-rail-repair-full-build.log`.
There are 83,811 lines under GridGraphs, plus the 177-line root: 233 library
source files and 83,988 lines total. All 147 public theorems in the 29 audited
modules depend only on subsets of `propext`, `Classical.choice`, and `Quot.sound`.
The previous 72+31 were rerun alongside all 44 new public theorems, with warnings
as errors and no `sorryAx` or native proof axiom. Audit logs:

- `/tmp/opencode/u1-u3-l2-rail-repair-previous72-axioms.log`
- `/tmp/opencode/u1-u3-l2-rail-repair-previous31-axioms.log`
- `/tmp/opencode/u1-u3-l2-rail-repair-new44-axioms.log`
- `/tmp/opencode/U1U3L2RailRepairAudit.lean` (new audit driver)
- `/tmp/opencode/u1-u3-l2-rail-repair-source-lengths.log` (source inventory)

OneExcessSeparated, CoveredBoundary, and RailRepair Geometry, Forest, Score
have 303, 276, 141, 97, and 146 lines respectively, all below 1,000.
The 11 pre-existing modules over 1,000 lines are listed
in [Lean STATUS](../lean/STATUS.md); none was extended. Private helpers are
covered transitively where used, not individually printed. See
[README](../lean/README.md) and [EVIDENCE](../lean/EVIDENCE.md) for the snapshot,
audit commands, and regression coverage. These are recorded results, not a
Lean build or Python test rerun for this documentation-only update. Root and
Regression cover both new upper fronts and the lower theorem, including the
symbolic lower/upper interval and lower regressions at sides 17, 20, 23, 29.
This is not a whole-library axiom audit; six legacy `native_decide` uses in
three separately built counterexample tests are outside these audited results.

Migration fixes preserve theorem statements and certificate data. Existing
finite certificates now use efficient kernel-checked fixed-entry replay, not
new searches or native proof axioms. Linter warnings were removed rather than
suppressed. No proof placeholders or global backward-compatibility flags were
added. The staircase construction, boundary-stratified upper bound, and exact
`P(7)=22` and `P(10)=42` results are included in this verified build.

This is the working roadmap. Historical roadmaps and analysis notes retain
the previous programs, evidence, and failed approaches for reference. Their
task ordering is not binding. Reuse valid mathematics, not accumulated workflow.

## 1. Goal And Completion Criterion

For a spanning tree of the n by n grid, a preserved vertex retains its full
grid degree. Let `P(n)=maxPreserved n n`.

The conjectured formula, for n >= 3, is

```text
P(3k)   = 3k^2+3k-2,     k >= 1,
P(3k+1) = 3k^2+5k,       k >= 1,
P(3k+2) = 3k^2+7k+1,     1 <= k <= 4,
P(3k+2) = 3k^2+7k,       k >= 5.
```

The active research focus is residue two. A solution requires an unconditional
upper bound and a feasible construction attaining it. Conditional assembly,
an abstract tree with the right count, and finite examples are not solutions.
The formula itself remains open to revision if mathematics contradicts it.

### Completion Chains

Lower, using the optional canonical b=5 construction:

1. **Checked:** construct the actual outer frame, prove its support is one tree,
   and identify the unattached next-ring vertex.
2. **Checked:** prove the exact inner attachment iff and count the extension
   as `4n-9+|A|`, with a theorem transferring that score to `maxPreserved`.
3. **Open mathematics:** construct A uniformly for k>=7, inside the twice-cropped
   square, with `|A|=3k^2-5k+1`, acyclic incident-edge graph, and no inner path
   between distinct frame-attachment vertices. No such target family is known.
4. Verify its coordinates and attachment invariant in Lean, then combine the
   resulting tail with the existing finite and other-residue constructions.

Upper, via the common budget inequality:

1. **Open mathematics:** prove `B>=n+4` for every feasible F.
2. **Open mathematics:** at n=3k+2, exclude `B=3k+6`, giving `B>=3k+9`.
3. **Open mathematics:** for k>=5 also exclude `B=3k+9`, giving `B>=3k+12`.
4. Apply the exact ledger to obtain all three residue upper bounds. The common
   bound suffices arithmetically for residues zero and one.

A direct stable proof `B>=3k+12` may replace the first three steps in that
range. Neither the upper strategy nor the lower b=5 subclass is mandatory.
Completing the checked lower reduction does not prove existence of its input
and does not establish an upper bound for b>=6.

## 2. What Is Actually Available

| Result | Status |
|---|---|
| Maximum preserved vertices equals maximum feasible forced-set size | Established in Lean |
| Exact component and boundary ledgers | Established in Lean |
| Exact values P(3)=4, P(4)=8, P(5)=11, P(7)=22, P(10)=42 | Established in Lean |
| Residue-zero and residue-one matching lower constructions | Established in Lean |
| Residue-two target-score lower witnesses through n=20 | Established in Lean |
| Uniform affine residue-two lower bound `3k^2+6k+5`, k>=5 | Established in Lean |
| Improved explicit lower family `3k^2+6k+2+floor(k/2)`, k>=3 | Unconditionally proved in Lean: `ResidueTwoStaircaseForest.lean` |
| Stable residue-two upper bound `P(3k+2)<=T(k)+floor((2k+2)/3)`, k>=5 | Established in Lean: `BoundarySix/Upper.lean`; unchanged by latest milestone |
| Any missing open side gives f<=T+1, k>=5, independent of p | Established in Lean: `CarrierLayers/MissingSideSharp.lean`; two excess requires four distinct side-covering pure carriers |
| Exact p<=3 one-excess slack and saturated-root isolate bounds | Established in Lean: `CarrierLayers/RadialOneExcess.lean`; exclusion remains open |
| Root-separated holes and covered-boundary pure mass | Established in Lean: `OneExcessSeparated.lean`, `CoveredBoundary.lean`; conditional sharpness only, no new global upper |
| Terminal rail repair L(k) | Uniform formal lower `3k^2+6k+3+floor((k-1)/2)`, k>=3, in `RailRepair/Score.lean`; not an accumulating pump |
| Propagating-interface alternative J(s) | Paper-only forest argument; actual score fails the target pump gain |
| General sharp square upper bounds | Still open |
| Carrier-length upper bound `P(n)<=n*(n*n+4*n-6)/(3*n+1)`, n>=5 | Unconditionally proved in Lean; division rounds down |
| Stronger boundary-stratified upper bound `P(n)<=n*(n*n+4*n-7)/(3*n+1)`, n>=7 | Unconditionally proved in Lean |
| Residue-two counterexample budget restrictions | Checked necessary conditions, not exclusions of all counterexamples |
| Horizontal carriers two rows apart overlap in at most one column | Checked local packing theorem |
| Residue-two target lower family for k>=7, starting at n=23 | Still open |
| Five-unit boundary bound and target component obstruction | Established in Lean: `BoundaryFiveBudget.lean` |
| Boundary-five corners, boundary count, and unique gap | Established in Lean: `BoundaryFiveEquality.lean` |
| Entire next ring unpreserved at b=5, n>=7 | Established in Lean: `BoundaryFiveEquality.lean` |
| Canonical outer-tree and exact support/spoke decomposition | Established in Lean: `BoundaryFiveFrame.lean` |
| Canonical inner attachment necessity and sufficiency | Established in Lean: `BoundaryFiveAttachment.lean` |
| Concrete extension count and transfer to maxPreserved | Established in Lean: `BoundaryFiveConstruction.lean`, conditional on an inner input |
| Arbitrary b=5 normalization and deep-square Q reformulation | Still partly paper-level |
| Full formula assembly | Established only conditionally |

Residues zero and one are complete on the construction side, not yet as
unconditional arbitrary-width exact formulas. A residue-two-specific proof
need not wait for the common upper theorem; a full diagonal result still
needs the other residues' upper bounds.

The new boundary and staircase axiom audits contain only `propext`,
`Classical.choice`, and `Quot.sound`. The verified improved lower bound is not
the conjectured optimum; the open upper/lower obligations above remain open.

## 3. The Central Model

For any set F of grid vertices, put `U=V\F` and let H contain every grid
edge incident to F, on the full grid vertex set. Then

```text
F feasible <=> H acyclic.
P(n) = max_(F feasible) |F|.
```

A feasible H need not be connected: it extends to a spanning tree. Define

```text
f = |F|,
r = number of components of grid[F],
c = number of components of H, INCLUDING isolated U vertices,
b = sum_(u in U) (4-deg_grid(u)),
B = r+c+b.
```

Corners in U contribute twice to b. The established component ledger gives

```text
3f+B = n^2+4n.
```

For n=3k+2 the entire residue-two conjecture becomes

```text
min_(F feasible) B = 3k+9,    1 <= k <= 4,
min_(F feasible) B = 3k+12,   k >= 5.
```

This is an exact reformulation, not an upper-bound proof. It puts construction
and obstruction on the same accounting system and permits a direct proof
instead of making the historical contour-routing pipeline mandatory.

## 4. New Deductions

Detailed paper proofs and qualifications are in
`analysis/RESIDUE_TWO_COMPONENT_BUDGET.md`. The boundary lower bound and
component obstructions now also have unconditional Lean proofs.

### Boundary Budget

Every feasible F on a square of side n>=5 satisfies `b>=5`.

At each corner, its two boundary neighbors cannot both be F: they would force
the corner unit-cell cycle. The four disjoint pairs therefore require four
noncorner boundary U vertices. If b<=4, these are the only boundary U vertices
and none are adjacent when n>=5. Every perimeter edge would then be forced,
again a cycle. This proves the fifth unit is necessary.

For n>=6, equality b=5 forces exactly one perimeter UU edge. This uniqueness
is now checked in Lean, as are preservation of all corners and the count of
five complementary boundary vertices. The resulting perimeter-path and
attachment decomposition is still paper-level. None of these results proves
that optimal constructions must have b=5.

### Component Obstruction

At stable target size `f=3k^2+7k`, the ledger and `c>=1,b>=5` imply

```text
r+c+b = 3k+12,
r <= 3k+6.
```

Consequences:

- The proposed counter skeleton with `4k+1` distinct maximal preserved
  components is impossible for k>=6, hence throughout its intended k>=7 range.
- Retaining `4k` distinct components at target count is impossible for k>=7.
- At n=23 the target permits at most 27 components. The counter proposal has
  29, and the audited affine architecture has 28.
- The average maximal preserved interval length at target is at least
  `(3k^2+7k)/(3k+6)>k`. A bounded-island construction cannot work uniformly;
  tile segments must concatenate into long components if tiles are used.

The abstract counter tree and its summed lengths remain arithmetically valid.
Their intended grid realization does not. Merging labeled intervals changes
the skeleton; overlapping them requires recounting the preserved set.

### Successor Budget

The uniform affine score has `B=6k-3`. The stable target has `B=3k+12`.
Thus the affine deficit is k-5 preserved vertices, or `3(k-5)` budget units.

```text
Exact successor:  Delta f=6k+10, Delta B=3.
Affine successor: Delta f=6k+9,  Delta B=6.
```

A viable new successor must address component/boundary growth, not just add
one more preserved vertex to an unchanged incidence architecture.

## 5. Formal Milestone And Next Gate

Completed in `lean/GridGraphs/Accounting/BoundaryFiveBudget.lean`:

1. `five_le_boundaryDeficiencySum_compl`: `b>=5` for every feasible F and n>=5.
2. `induced_components_le_three_mul_add_six`: `r<=3k+6` at target count.
3. `not_feasible_target_of_four_mul_le_components`: rules out `r>=4k`, k>=7.
4. `not_feasible_target_of_four_mul_add_one_le_components`: rules out
   `r>=4k+1`, k>=6.

These are statements about actual grid sets. Two symbolic regression examples
specialize the obstructions to sides 23 and 20, without enumerating grids.
The proof reuses the existing unit-cell unforced-edge theorem and forest
extension/perimeter theorem; no new general routing framework was needed.

Also completed in `lean/GridGraphs/Accounting/BoundaryFiveEquality.lean`:

1. `boundaryDeficiencySum_compl_eq_five_corners_and_card`: all corners in F
   and exactly five complementary boundary vertices, n>=6.
2. `boundaryDeficiencySum_compl_eq_five_witness_decomposition`: four independent
   corner witnesses plus one extra boundary vertex, with at most one neighbor
   among those witnesses.
3. `boundaryDeficiencySum_compl_eq_five_unique_perimeter_edge`: existence and
   uniqueness as an unordered `Sym2` edge, not a directed-edge count.
4. `boundaryDeficiencySum_compl_eq_five_no_boundary_distance_two`: same-side
   vertices two grid steps apart cannot both be complementary, n>=7.
5. `boundaryDeficiencySum_compl_eq_five_next_ring_notMem`: the entire boundary
   of the once-cropped square is unpreserved, n>=7.

The equality module and regression tests pass on Lean 4.33.1. Tests instantiate
gap uniqueness at side 8 and next-ring exclusion at the threshold side 7,
without enumeration. Axiom audits report only `propext`, `Classical.choice`,
and `Quot.sound`.

The normalized frame and attachment gates are now checked:

- `BoundaryFiveFrame.Houter_isAcyclic` and `support_isTree` prove the actual
  canonical frame is a forest with one nonisolated component, unconditionally.
- `BoundaryFiveFrame.support_eq`, `w_no_neighbor`, and the unique-spoke
  theorems identify precisely its outer-two-ring support and exceptional vertex.
- `BoundaryFiveAttachment.Houter_sup_isAcyclic_iff` proves that an inner graph
  J whose edges stay in the once-cropped square can be attached iff J is a
  forest and no J-component connects two distinct frame-attachment vertices.
- `BoundaryFiveConstruction.Ffull_isAcyclic_iff` instantiates this for the actual
  union of the boundary centers with a deep input A. `Ffull_card` proves the
  exact count, and `residueTwo_le_maxPreserved` gives the conditional target.

These modules and tests pass on 4.33.1, with only the standard logical axioms.
They do not assume all inner components are rooted. The primary remaining
lower research gate is now the explicit input A, not another frame-gluing API.
Normalization of every arbitrary b=5 configuration and the equivalent Q
description on a smaller vertex type are separate remaining formal obligations,
not dependencies of the canonical lower construction.

## 6. Lower Track: Geometry With The Right Budget

The next research deliverable is a coordinate-defined target family or a
coordinate-defined successor with a provable invariant. Design coordinates
and topology together. Do not require an abstract skeleton to be completed first.

Every candidate must specify and justify f, r, c, b. Reject it immediately if
the ledger fails. Track isolated U vertices explicitly: an interval-incidence
tree may be connected while H has many isolated vertices.

Allow nonlocal rearrangement, deletion or merging of old components, and a
growing interface of ordered interval identities and attachment ancestry.
There is no requirement that every old interval remain a distinct successor
node. A merger that closes an old attachment path must identify the physical
connection removed or rerouted. A parent label alone does not establish this.

An optional sharply specified design class is

```text
b=5, c=1, r=3k+6, f=3k^2+7k.
```

Here H itself is a spanning tree. Its boundary contains the perimeter path
from the equality lemma. If u_j counts U vertices with j F-neighbors, then

```text
u_0=0, u_2=3k+5, u_1=6k^2+2k-1.
```

Its successor would have `Delta r=3`, `Delta u_2=3`, and `Delta u_1=12k+8`.
This is a conjectural sufficient class. No base in it is asserted to exist.
Failure of this class is not failure of the formula: permit other c,b splits
with the same total budget.

### Exact Boundary-Five Peeling

There is a two-way paper reduction, independently audited, in
`analysis/BOUNDARY_FIVE_PEELING.md`. Its unique-gap and next-ring ingredients,
canonical frame, and canonical attachment equivalence are now formalized.
The full arbitrary-configuration normalization is not. For n>=7 and b=5,
normalize the unique perimeter UU edge to `(1,2)--(1,3)` in coordinates 1..n. Then:

- The entire next ring is U, forced by unit-cell obstructions.
- The outer two rings form one forced tree T and one unattached U vertex
  `w=(2,3)`.
- On the deep square D of side m=n-4, H_D must be a forest, its three corners
  other than the designated corner z must be U, and each H_D component may
  contain at most one preserved boundary vertex.
- These conditions are sufficient as well: each rooted inner component
  attaches once to T, and z, if preserved, picks up w as a leaf.

Let Q(m) maximize the inner preserved count subject to those conditions. Then

```text
max_(F feasible, b(F)=5) |F| = 4n-9+Q(n-4).
```

Do not replace Q by unrestricted P. The one-root-per-component condition is
exactly what prevents cycles through the outer tree.

At n=3k+2, the new concrete lower target is a Q-family on side `3k-2`
with `3k^2-5k+1` preserved vertices. It need not be fully rooted. In the
optional c=1 subclass, z is preserved and EVERY H_D component has exactly
one preserved boundary root, including all isolated vertices in the accounting.
Then the induced inner F has `3k+2` components.

The arbitrary-b=5 Q reformulation is not yet fully formalized, and Q has not
been evaluated. The checked construction API instead uses A in ambient
zero-based coordinates `2<=row,col<=n-3` and counts its actual forced edges
and attachments. This is already sufficient to build the lower family if A
is supplied. For the
fully rooted subclass there is also a paper obstruction: any horizontal
preserved interval on row 3 has length at most five, with rotated versions
on the other tracks two steps from a side. A long rail there cannot be fixed
by assigning it a remote root; the boundary vertices above it need domination.

### Historical Staircase Family

Section 8 of `analysis/BOUNDARY_FIVE_PEELING.md` gives actual coordinates
and the proof of score `3k^2+6k+2+floor(k/2)`, k>=3, now formalized in
`ResidueTwoStaircase.lean` and `ResidueTwoStaircaseForest.lean`. A staircase
of opposing intervals is extended by alternating bottom-boundary singleton
stars and interior stars attached to its last left interval. Every attachment
is identified physically, and the count is a symbolic sum.

This strictly improves the affine family for k>=8. Its remaining stable gap is
`floor((k-1)/2)-1`; it does not solve the target. Lean proves the actual center
count, placement, support intersections, and unconditional forced acyclicity
by two finite gluing inductions. `residueTwo_le_maxPreserved` has only the
arithmetic assumption k>=3, not an unproved forest or attachment hypothesis.
The proof works directly in ambient coordinates without the full arbitrary-b=5
Q equivalence. No search, including at large widths, was used.

### Current Terminal Repair

`RailRepair/Geometry.lean`, `Forest.lean`, and `Score.lean` formalize the
single terminal surgery described in the research note, including nonempty
alternating pockets at arbitrary width. The unconditional endpoint is
`GridGraphs.RailRepair.residueTwo_le_maxPreserved`, with L(k) as above.
The staircase remains valid historical infrastructure; L(k) supersedes its
score at odd k. The repair's six-width gain remains 12k+25, not 12k+26.

Completion gates:

1. Attempt the explicit Q-family above, allowing unrooted components if useful;
   if this class fails, return to b>=6 rather than declare the conjecture false.
2. Explicit coordinates for all sufficiently large k, with any omitted finite
   bases supplied separately; no interpolation from a few witnesses.
3. Exact cardinality and component/boundary accounting.
4. Uniform forced acyclicity or complementary dual connectivity, with actual
   grid attachments and no accidental cycles or reused physical connectors.
5. Lean construction and discharge of `RemainingMatchingDiagonalConstructions`.

## 7. Upper Track: Prove The Minimum

### Current Unconditional Upper Bound

The current stable residue-two bound, from `Accounting/BoundarySix/Upper.lean`, is
`P(3k+2)<=T(k)+floor((2k+2)/3)` for k>=5. The latest separated-hole and pure-mass work
does not improve this global formula. The following boundary-stratified result
is an earlier milestone, still valid over its broader range.

`Accounting/BoundaryStratifiedCarrierBound.lean` proves, for every n>=7,

```text
P(n) <= floor(n*(n*n+4*n-7)/(3*n+1)).
```

This improves the earlier numerator-minus-six carrier bound, which remains
available for n>=5. The new proof covers every feasible set, without assuming
that an optimum has b=5:

- If b>=6, the original carrier estimate and c>=1 already pay seven units.
- If b=5 and n>=10, the empty next ring separates induced preserved components
  into boundary carriers and deep carriers. The boundary contains exactly
  `4n-9` preserved vertices and needs at least four carriers; each deep carrier
  has length at most n-4. Consequently `|F|<=(n-4)*r+7`.
- Combining this refined length estimate with the ledger gives the stronger
  bound. The cases n=7,8,9 follow by arithmetic from the earlier estimate.

In residue two, that earlier milestone's checked polynomial form is

```text
P(3k+2) <= 3k^2+7k+floor((2k+3)/3),    k>=2.
```

There is no universal-waste assumption. The improvement does not change the
linear asymptotic coefficient of the earlier bound, and the sharp stable
target `3k^2+7k` remains open.

| Side | Proved lower | Proved upper |
|---:|---:|---:|
| 7 | 22 | 22 |
| 10 | 42 | 42 |
| 14 | 77 | 79 |
| 17 | 110 | 114 |
| 20 | 149 | 154 |
| 23 | 195 | 201 |
| 26 | 246 | 254 |
| 29 | 304 | 312 |

The current uniform repair gives the displayed lower bounds from side 17
onward. In particular 110 matches the existing finite lower witness at side
17, but **P(17) is not proved exact**: its global upper bound is still 114.

The new equality at side 10 is `maxPreserved_ten_ten` in
`Results/SmallDiagonalExact/Ten.lean`, using the existing residue-one lower
construction. These examples specialize structural theorems; no grid searches
were run.

### Checked Counterexample Restrictions

`Accounting/ResidueTwoCounterexampleProfile.lean` proves that a feasible set on
side 3k+2 with `|F|>=3k^2+7k+excess`, k>=1 and excess>=1, must satisfy

```text
r >= k+2,
b+c+3*excess <= 2k+10.
```

Thus a stable counterexample has b+c<=2k+7, and a counterexample to the early
target has b+c<=2k+4. The branch b+c>=2k+8 already satisfies the stable target.
For stable counterexamples with b=5, the refined geometry additionally proves
r>=k+3 and c<=2k+1. These narrow the open profiles; they do not prove that
those profiles are impossible.

`Geometry/CarrierPacking.lean` independently proves the six-cycle obstruction
and the bound `length(C1)+length(C2)<=n+1` for wholly preserved horizontal
intervals two rows apart. This local result has not yet been summed into a
stronger global packing inequality.

Next upper gates: use the exact three-unit slack and root-separated charge to
force a sufficiently large S, or find another obstruction; control the
all-sides-covered branch using pure mass and contacts without adding overlapping
budgets. Boundary-five equality remains a useful subcase, not a global
normalization. Next lower gate: a propagating six-width rail repair with
compatible seeds and gain 12k+26. The formal terminal repair improves L(k),
but neither it nor the paper propagating alternative supplies that pump.

### Sharp Upper Obligations

The direct targets are `B>=3k+9` for 1<=k<=4 and `B>=3k+12` for k>=5,
for every feasible F. The known lower witnesses then close the early range
and k=5,6; the lower track must close the remaining tail.

There are two live routes, with no predetermined winner:

**Direct interval geometry.** Contract maximal preserved intervals. Each U
connector joins at most two intervals, through opposite grid neighbors.
Retain physical connectors and any parallel edges when testing a candidate:
two connectors between the same intervals are already a cycle.

For an interval J, let N(J) be its neighbors in U and put `q(J)=|N(J)|-1`.
For a subfamily A define integer slack

```text
delta(A)=|union_(J in A) N(J)|-sum_(J in A) q(J).
```

For candidates with straight maximal components, feasibility is equivalent
to `delta(A)>=1` for every nonempty A. Equivalently, interval tokens admit a
matching after any one chosen U vertex is forbidden. The matching may depend
on that vertex. Tight overlapping families have an exact uncrossing rule.

These are forest sparsity identities, not the missing inequality. The actual
research gate is a grid-geometric argument forcing a deficient family at a
forbidden score, or a geometric classification of low-budget feasible sets.
In particular, the k=5 threshold still needs an explanation.

The new peeling theorem handles only b=5. Even a sharp Q bound would not
exclude better configurations with b>=6. No normal-form theorem putting an
optimum in b=5 is known; do not silently assume one.

**Global contour exchange.** Retain the existing occurrence-preserving
physical exchange route as an alternative. Prove the missing expansion,
instantiate `UniversalPrimalContourRouting`, obtain universal waste, and then
prove the two residue-two exclusions. Do not assume the disproved regional
first-ownership certificate or count repeated contacts as new resources.

A direct proof of the budget minimum can bypass this route. Conversely, a
valid contour proof need not be rewritten in interval language. More generic
Hall or routing interfaces without new grid geometry are not a milestone.

## 8. What Is Superseded

- The counter subdivision is no longer an active uniform realization candidate.
- Abstract target length plus an abstract tree is not an adequate lower gate.
- A fixed injective old-interval embedding is not a construction requirement.
- Connected incidence is not necessary for forced-set feasibility.
- The historical regional first-ownership theorem is false in general, not an
  unfinished lemma to assume or complete unchanged.
- Exhausted local grammars do not forbid nonlocal constructions, arbitrary
  other periods, or new arguments. Their counterexamples retain their stated
  scope; no global impossibility follows merely from accumulated failed searches.
- New paper deductions are not formal theorems until checked in Lean.

## 9. Laptop And Verification Rules

- Before extending a Lean file over 1,000 lines, split it into focused modules.
  Use sub-subfolders where helpful, preserve public theorem names, and keep
  new modules below that limit. Do not hide the old proof in an oversized helper.
- Address every project linter warning; do not silence linters to obtain a clean
  build. Verify changed modules and the full source set with warnings as errors.

The previous 2,420-line `Results/SmallDiagonalExact.lean` has been split into
`Three`, `BoundaryFive`, `LedgerFive`, `AttachmentFive`, `AttachmentCasesFive`,
and `Five` under `Results/SmallDiagonalExact/`. The largest is 708 lines. The
original entry module now aggregates these results and the `Seven` and `Ten` theorems;
all 17 prior public declaration names are preserved.

This work runs on a laptop with 32 GB RAM and a short interactive time budget.

- No new exact-grid optimization, exhaustive enumeration, SAT/SMT, or expanding
  state-product search above 15x15. Reuse existing larger results.
- Being at most 15x15 is not permission for a long run. A proposed search needs
  a precise falsification question, explicit time/memory caps, and approval.
- Prefer symbolic reasoning. No optimization was needed for the new deductions.
- Polynomial replay of an explicit witness is different from finding an
  optimum. Keep even those checks short and purpose-specific. Finite replay
  is debugging evidence, not an arbitrary-width proof.
- Do not add another solver or generic proof framework without a concrete need.
- Preserve concurrent worktree changes. Do not infer verification from a clean
  file or an old status document.
- User authorization overrides the previous full-build time cap: project-library
  verification may run in the background without a time limit. Keep its log and
  exit status observable, reuse mathlib caches, and avoid competing full builds.

During formal development, run the affected module from `lean/`:

```bash
lake env lean GridGraphs/NewModule.lean
```

Before reporting a formal milestone, run `lake build` from `lean/` and
`git diff --check` from the repository root. Audit new proofs for `sorry`,
`admit`, additional axioms, and computational proof dependencies. Report any
build or resource blocker explicitly. Documentation-only updates do not require
a full Lean build and must not be reported as one.

## 10. Minimal Navigation

| File | Role |
|---|---|
| `docs/HANDOFF_U1_U3_L2.md` | Latest formal repair, scoped upper fronts, verification, next goals |
| `docs/L2_FIXED_RAIL_POCKET.md` | Paper-only obstruction with frame and rails fixed |
| `docs/L2_RAIL_REPAIR_RESEARCH.md` | Now-formal terminal repair, historical finite searches, and scoped propagation obstruction |
| `docs/L2_PROPAGATING_INTERFACE.md` | Separate paper alternative with unsuccessful actual target gain |
| `lean/GridGraphs/Constructions/ResidueTwo/RailRepair/Score.lean` | Current uniform formal lower bound and insufficient six-width gain |
| `lean/GridGraphs/Accounting/CarrierLayers/OneExcessSeparated.lean` | Root-separated hole charge without saturation; conditional sharp bound |
| `lean/GridGraphs/Accounting/CarrierLayers/CoveredBoundary.lean` | Actual pure mass and shared physical boundary budgets |
| `lean/GridGraphs/Accounting/CarrierLayers/MissingSideSharp.lean` | Uniform missing-side bound and four distinct side-covering pure carriers |
| `lean/GridGraphs/Accounting/CarrierLayers/RadialOneExcess.lean` | Exact one-excess slack and saturation-only isolate bounds |
| `analysis/RESIDUE_TWO_COMPONENT_BUDGET.md` | New paper proofs, exact qualifications, analytic gates |
| `analysis/BOUNDARY_FIVE_PEELING.md` | Exact paper reduction to an inner boundary-rooted forest |
| `lean/GridGraphs/Accounting/BoundaryFiveBudget.lean` | Checked boundary bound and target component obstructions |
| `lean/GridGraphs/Accounting/BoundaryFiveEquality.lean` | Checked equality geometry, unique gap, and next-ring exclusion |
| `lean/GridGraphs/Accounting/CarrierLengthBound.lean` | Unconditional square upper bound from component lengths |
| `lean/GridGraphs/Accounting/BoundaryStratifiedCarrierBound.lean` | Stronger all-configuration upper bound using the b=5/b>=6 split |
| `lean/GridGraphs/Accounting/ResidueTwoCounterexampleProfile.lean` | Necessary low-budget profiles and the solved high-budget branch |
| `lean/GridGraphs/Geometry/CarrierPacking.lean` | Six-cycle and two-row interval-overlap restrictions |
| `lean/GridGraphs/Constructions/BoundaryFive/BoundaryFiveFrame.lean` | Actual canonical frame, support tree, and spokes |
| `lean/GridGraphs/Constructions/BoundaryFive/BoundaryFiveAttachment.lean` | Exact canonical inner-attachment iff |
| `lean/GridGraphs/Constructions/BoundaryFive/BoundaryFiveConstruction.lean` | Counted concrete extension and lower-bound transfer |
| `lean/GridGraphs/Constructions/ResidueTwo/ResidueTwoStaircase.lean` | Improved family's coordinates, placement, and exact count |
| `lean/GridGraphs/Constructions/ResidueTwo/ResidueTwoStaircaseForest.lean` | Improved family's support geometry and unconditional lower bound |
| `lean/GridGraphs/Core/ForcedMaximum.lean` | Exact optimization equivalence |
| `lean/GridGraphs/Accounting/ComponentReduction.lean` | Existing exact ledger |
| `lean/GridGraphs/Results/SmallDiagonalExact.lean` | Aggregate for modular exact 3x3, 5x5, 7x7, and 10x10 proofs |
| `lean/GridGraphs/Constructions/ResidueTwo/ResidueTwoAffineMax.lean` | Uniform near-target lower bound and exact deficit |
| `lean/GridGraphs/Constructions/IntervalStarGluing.lean` | Reusable lower-bound acyclicity interface |
| `lean/GridGraphs/Routing/UniversalPrimalContourRouting.lean` | Alternative upper-bound endpoint |
| `lean/GridGraphs/Results/DiagonalUpperResidue.lean` | Precise open upper hypotheses and adapters |
| `lean/GridGraphs/Results/DiagonalFormula.lean` | Remaining construction obligation and conditional assembly |
| `lean/STATUS.md`, `lean/EVIDENCE.md` | Detailed source/evidence indexes, not substitutes for fresh verification |

Start with these files. Consult historical notes only when their specific
construction, obstruction, or interface becomes relevant; do not survey the
entire experiment collection.
