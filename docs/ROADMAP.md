# Astra Roadmap: Exact Square-Grid Optimum

Updated: 2026-09-05.

Source layout: the 190 Lean modules are now grouped under `Core`, `Forests`,
`Geometry`, `Accounting`, `Routing`, `Surgery`, `Constructions`, `Results`,
and `Tests`. Construction families have their own subfolders. Public theorem
namespaces and the `import GridGraphs` entry point are unchanged; module
imports and live path references have been updated. See `lean/README.md` for
navigation. Verification recorded before this move does not certify the new
module layout; a fresh warning-as-error check is required.

## Toolchain Migration Status

The project now pins Lean `v4.33.1` and mathlib `v4.33.1`; the dependency
manifest and mathlib binary cache have been updated. The earlier successful
7,521-job build below was on Lean `v4.24.0-rc1`, not the new toolchain.

The boundary/test dependency chain now builds on 4.33.1:
`lake build GridGraphs.Constructions.BoundaryFive.BoundaryFiveConstruction GridGraphs.Tests.Regression` passed with
8,732 jobs. The former `Forced`, `ResidueOne`, and `MarkedCycleFirstStop`
blockers are fixed, along with further graph, component, contour, and
construction API changes exposed downstream.

Full-library validation now runs in the background WITHOUT a time limit,
explicitly authorized by the user. It targets `GridGraphs`, reusing cached
mathlib dependencies, not a separate mathlib-wide verification. The log is
`/tmp/opencode/grid-graphs-library-verification-retry.log`; completion writes
`/tmp/opencode/grid-graphs-library-verification-retry.exit`. Do not launch a competing
full build or assume success while that status file is absent.

The first unrestricted pass finished with exit 1. Every module it reported
has now passed a direct source check, and the retry runs against those fixes.
In particular, the existing finite certificates for sides 8,9,11,12,14,15,17,18,20
now replay their fixed entries with kernel-checked `decide`, instead of broad
table simplification. Certificate data, statements, and limits are unchanged;
these are rechecks, not new optimization searches or native evaluation axioms.
The 17/18/20 files passed in about 19-21 seconds each; the smaller files took
about 6-11 seconds. The original log and exit status remain at the paths
without `-retry`. Full-library success is not claimed until the retry completes.

The active proof chain is usable, so equality/peeling work has resumed. No
theorem statements were weakened and no proof placeholders or global
backward-compatibility flags were added.

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
| Exact bases P(3)=4, P(4)=8, P(5)=11 | Established in Lean |
| Residue-zero and residue-one matching lower constructions | Established in Lean |
| Residue-two target-score lower witnesses through n=20 | Established in Lean |
| Uniform affine residue-two lower bound `3k^2+6k+5`, k>=5 | Established in Lean |
| Improved explicit lower family `3k^2+6k+2+floor(k/2)`, k>=3 | Unconditionally proved in Lean: `ResidueTwoStaircaseForest.lean` |
| General sharp square upper bounds | Still open |
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

Verification on 2026-09-05, before the toolchain upgrade: the new boundary module and regression tests passed,
then `LEAN_NUM_THREADS=2 timeout 90s lake build` completed successfully with
7,521 jobs. The four new theorems depend only on `propext`, `Classical.choice`,
and `Quot.sound`. This certified the formal milestone on Lean 4.24.0-rc1,
not current 4.33.1 compatibility, the open paper results, or the diagonal formula.

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

### Improved Explicit Family

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
| `analysis/RESIDUE_TWO_COMPONENT_BUDGET.md` | New paper proofs, exact qualifications, analytic gates |
| `analysis/BOUNDARY_FIVE_PEELING.md` | Exact paper reduction to an inner boundary-rooted forest |
| `lean/GridGraphs/Accounting/BoundaryFiveBudget.lean` | Checked boundary bound and target component obstructions |
| `lean/GridGraphs/Accounting/BoundaryFiveEquality.lean` | Checked equality geometry, unique gap, and next-ring exclusion |
| `lean/GridGraphs/Constructions/BoundaryFive/BoundaryFiveFrame.lean` | Actual canonical frame, support tree, and spokes |
| `lean/GridGraphs/Constructions/BoundaryFive/BoundaryFiveAttachment.lean` | Exact canonical inner-attachment iff |
| `lean/GridGraphs/Constructions/BoundaryFive/BoundaryFiveConstruction.lean` | Counted concrete extension and lower-bound transfer |
| `lean/GridGraphs/Constructions/ResidueTwo/ResidueTwoStaircase.lean` | Improved family's coordinates, placement, and exact count |
| `lean/GridGraphs/Constructions/ResidueTwo/ResidueTwoStaircaseForest.lean` | Improved family's support geometry and unconditional lower bound |
| `lean/GridGraphs/Core/ForcedMaximum.lean` | Exact optimization equivalence |
| `lean/GridGraphs/Accounting/ComponentReduction.lean` | Existing exact ledger |
| `lean/GridGraphs/Results/SmallDiagonalExact.lean` | Structural small-grid proofs |
| `lean/GridGraphs/Constructions/ResidueTwo/ResidueTwoAffineMax.lean` | Uniform near-target lower bound and exact deficit |
| `lean/GridGraphs/Constructions/IntervalStarGluing.lean` | Reusable lower-bound acyclicity interface |
| `lean/GridGraphs/Routing/UniversalPrimalContourRouting.lean` | Alternative upper-bound endpoint |
| `lean/GridGraphs/Results/DiagonalUpperResidue.lean` | Precise open upper hypotheses and adapters |
| `lean/GridGraphs/Results/DiagonalFormula.lean` | Remaining construction obligation and conditional assembly |
| `lean/STATUS.md`, `lean/EVIDENCE.md` | Detailed source/evidence indexes, not substitutes for fresh verification |

Start with these files. Consult historical notes only when their specific
construction, obstruction, or interface becomes relevant; do not survey the
entire experiment collection.
