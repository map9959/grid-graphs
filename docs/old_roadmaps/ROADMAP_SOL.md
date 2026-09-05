# Current Roadmap: Exact Diagonal Formula

## Project Direction

The active goal is an unconditional proof of the exact diagonal formula for
the maximum number of full-degree vertices in a spanning tree of the square
grid.

For a spanning tree `T` of `gridGraph n n`, let `numPreserved n n T` be the
number of vertices whose full grid degree is preserved. Define

```text
P(n) = maxPreserved n n.
```

The target formula is:

```text
P(3k)   = 3k^2 + 3k - 2
P(3k+1) = 3k^2 + 5k

P(3k+2) = 3k^2 + 7k + 1,  1 <= k <= 4
P(3k+2) = 3k^2 + 7k,      k >= 5
```

Equivalently, after the three exact bases

```text
P(3) = 4
P(4) = 8
P(5) = 11,
```

the expected recurrence is

```text
P(n) = P(n-3) + 2n - (if n = 17 then 1 else 0).
```

The project has moved from computational exploration to proof development.
The finite computations have already supplied enough data, counterexamples,
and explicit bases. New exponential searches, SAT/SMT encodings, CEGAR loops,
or bespoke finite scripts are no longer part of the roadmap. The remaining
work is structural mathematics and Lean formalization.

The previous historical roadmap is preserved in `docs/ROADMAP_OLD.md`.

## Reassessment: 2026-09-05

This section supersedes the abstract-tree-first lower strategy and the strict
ordering of the historical upper program below. Failed finite grammars remain
counterexamples to those grammars, not prohibitions on new mathematical ideas.
The target formula remains conjectural where its lower or upper proof is open.

New paper deductions, proofs, qualifications, and revised gates are recorded in
`analysis/RESIDUE_TWO_COMPONENT_BUDGET.md`. They are not yet new Lean theorems.

For any feasible forced set F on side `3k+2`, define `r=c(grid[F])`,
`c=c(forcedEdgeGraph grid F)` including isolated U vertices, and
`b=boundaryDeficiency(U)`, where `U=univ\F`. The existing ledger gives

```text
3|F| + B = 9k^2+24k+12,       B = r+c+b.
```

The exact residue-two problem is therefore a minimum-budget problem:

```text
min B = 3k+9   for 1<=k<=4,
min B = 3k+12  for k>=5.
```

This is a reformulation, not a proof. A direct geometric proof of the second
minimum may bypass the common upper-bound routing and separate exclusions.
Both sides remain necessary: prove no smaller budget and realize that budget.

**New global construction obstruction:** corner-cell and perimeter cycles force
`b>=5` for side at least 5. Together with `c>=1`, a target-count family must
have `r<=3k+6`. The proposed `4k+1`-node counter skeleton cannot be realized
with distinct maximal preserved components for `k>=6`, hence throughout its
intended range `k>=7`, regardless of coordinate choices. Retaining `4k`
components is already impossible for `k>=7`.
Merging nodes is a different skeleton, not a realization of the old one.
This closes its proposed uniform realization, not just a bounded local grammar.

At boundary equality `b=5` and `n>=6`, there is exactly one perimeter UU
edge, so H contains a path through every boundary vertex. This gives a
concrete boundary-first gate for the optional b=5 lower family, without
restricting its interior to any previously exhausted local grammar.

The affine family has budget `6k-3`; the target has `3k+12`. An exact
successor must add only three budget units, versus six for the affine successor.
New lower designs must account for components, isolated vertices, and boundary
incidences before further coordinate experimentation. Long-range interval
coalescence is allowed; a fixed old-node embedding is no longer required.

An exact neighborhood formulation also identifies feasibility with a token
matching surviving deletion of any one U vertex. Its tight-family uncrossing
rule is available as an analytic tool. It is equivalent to forest sparsity,
not a new upper bound: the missing ingredient is still grid geometry.

**Laptop constraint:** no new optimization or exhaustive grid search above
15x15. Smaller searches are not automatically acceptable: require a specific
question, explicit time/memory caps, and approval. Prefer symbolic proofs.
Inspection of existing large witnesses and short polynomial checks of explicit
coordinate constructions are distinct from optimization. No computation was
used for this reassessment, and no finite check is a final proof dependency.

## Current Position

The diagonal cases `n = 0 mod 3` and `n = 1 mod 3` are essentially formalized
on the construction side. Their exact formulas follow once the common planar
upper bound is proved. The difficult case is `n = 2 mod 3`, where both a
stable lower construction and two sharp upper-bound exclusions remain open.

| Area | Current state |
|---|---|
| Forced-set optimization model | Complete |
| Exact bases `P(3)`, `P(4)`, `P(5)` | Complete in Lean |
| Residue-zero lower constructions | Formalized, including a uniform symbolic tail |
| Residue-one lower constructions | Formalized uniformly |
| Residue-two lower constructions | Explicit through `n=20`; stable `n>=23` family missing |
| Common universal upper bound | Reduced to a concrete planar channel realization |
| Residue-two sharp upper bounds | Tight and near-tight profile exclusions still open |
| Arithmetic formula assembly | Complete conditionally |
| Unconditional final formula | Not yet proved |

## Why Computation Is No Longer The Plan

The underlying optimization problem is NP-hard in its general form, and the
finite-state and exact-search methods grow exponentially. Those methods were
valuable for:

- discovering the residue formulas;
- finding exact small cases and construction witnesses;
- detecting the exceptional change at `n=17`;
- falsifying overly simple transfer states and local potentials;
- locating concrete failure modes for proposed residue-two pumps.

They have now reached diminishing returns. In particular:

- more exact widths do not prove an arbitrary-width theorem;
- larger state products repeatedly hit memory or exponential-time barriers;
- several finite models lost the component ancestry or channel information
  required by a proof;
- the remaining gaps are identifiable structural lemmas, not missing data.

Therefore:

> Do not add new computational scripts or solvers for the diagonal proof.
> Continue with symbolic graph theory, planar topology, explicit constructions,
> and Lean proofs.

Policy refinement after the targeted wave of 2026-08-11: bounded deterministic
computations are permitted for falsifying a precisely declared finite grammar
or validating a proof-oriented transition API. They must have hard resource
caps, no lossy pruning, independently replayable witnesses, and no role as a
final proof dependency. Exact-width optimization, open-ended neighborhood
growth, SAT/CEGAR, and larger beam searches remain outside the roadmap. See
`analysis/TARGETED_COMPUTATION_WAVE_2026-08-11.md`.

Existing computational artifacts remain useful historical evidence, but they
are not dependencies of the final theorem.

## Core Formal Reduction

The most important completed reduction is

```lean
maxPreserved_eq_maxForcedAcyclic
```

from `ForcedMaximum.lean`.

A set `F` of grid vertices is feasible exactly when the graph containing every
grid edge incident with `F` is acyclic:

```text
forcedEdgeGraph G F = {xy in E(G) : x in F or y in F}.
```

Thus the diagonal problem can be studied as the finite extremal problem

```text
maximize |F| subject to forcedEdgeGraph (gridGraph n n) F being acyclic.
```

This model is exact, not merely an upper bound. Any feasible forced forest can
be extended to a spanning tree preserving every vertex in `F`.

## Exact Bases

All recurrence bases are now unconditional Lean theorems:

```text
P(3) = 4
P(4) = 8
P(5) = 11
```

The `5 x 5` proof is fully structural. It uses:

- the exact component/deficiency ledger;
- straightness of induced forced components;
- cyclic boundary-run counting;
- corner cell obstructions;
- explicit six-cycle contradictions for the final four rotated cases.

No exhaustive configuration enumeration or computational decision tactic is
used in the Lean proof.

Relevant module:

```text
lean/GridGraphs/SmallDiagonalExact.lean
```

## Residue Status

### Residue Zero: `n = 3k`

The intended value is

```text
P(3k) = 3k^2 + 3k - 2.
```

Current state:

- finite construction bases are available;
- the phase-row residue-zero family is formalized;
- its exact cardinality is formalized;
- uniform dual connectivity and forced acyclicity are formalized in the stable
  range;
- construction-score successor bounds are formalized.

The remaining dependency for exactness is the common universal upper bound.
No residue-zero-specific construction theorem is considered a primary blocker.

Relevant modules include:

```text
ResidueZero.lean
ResidueZeroDual.lean
ResidueZeroFrontier.lean
ResidueZeroPersistent*.lean
ResidueZeroLocalGeometry.lean
```

### Residue One: `n = 3k+1`

The intended value is

```text
P(3k+1) = 3k^2 + 5k.
```

Current state:

- the explicit residue-one family is formalized uniformly;
- its cardinality is exact;
- dual connectivity and forced acyclicity are formalized;
- the reverse-frame template and exact construction-score gain are formalized;
- extremal wrappers from explicit constructions to `maxPreserved` are present.

As in residue zero, the remaining dependency for exactness is the common
universal upper bound.

Relevant modules include:

```text
ResidueOne.lean
ResidueOneDual.lean
ResidueOneMax.lean
ResidueOneReverseFrame.lean
```

### Residue Two: `n = 3k+2`

The residue-two formula changes at `k=5`:

```text
P(3k+2) = 3k^2 + 7k + 1,  1 <= k <= 4
P(3k+2) = 3k^2 + 7k,      k >= 5.
```

Current lower-bound coverage:

| Side | Status |
|---:|---|
| `5, 8, 11, 14` | Explicit early residue-two construction scores |
| `17` | Explicit score 110 |
| `20` | Explicit score 150 |
| `23` and above | No valid exact stable family currently known |

Current upper-bound obligations:

1. Prove the universal waste bound `W >= n+2`.
2. Exclude `W = n+2` in residue two.
3. Exclude `W = n+5` for `k >= 5`.

The exact reductions for obligations 2 and 3 already exist. What remains is
the geometric nonexistence proof for the corresponding tight support profiles.

## Formula-First Strategy

The current strategy is to prove the formula from matching absolute bounds,
then derive the recurrence afterward.

```text
absolute upper bound + explicit lower construction
  -> exact diagonal formula
  -> DiagonalRecurrence
```

This is preferable to making crop equality phases or reverse frames from
arbitrary maximizers prerequisites for the theorem.

## Critical Path

| Step | Work | Deliverable | Completion gate |
|---:|---|---|---|
| 1 | Define the concrete grid channel realization | `GridChannelContourRealization` combining demands, a pruned channel forest, exits, merger slots, and carrier roots | The structure contains geometric data rather than assuming the final cardinal inequality |
| 2 | Construct canonical channels | Realize the `n+3` row/column and corner germs as leaves or exits | Demand map is injective; parent relation is genuine immediate continuation |
| 3 | Define the reconvergence-lens tree | Every ordered collision belongs to a smallest planar lens; lenses are disjoint or nested | Shared suffixes and the `n=8` multi-hull witness are represented without a fixed hull-depth bound |
| 4 | Prove regional paid-merger discharge | A lens pays local branch excess with first-owned primal resources or passes labelled debt to its parent | The inequality is local, handles bare combs, and is not inferred from total waste |
| 5 | Telescope lens discharge and apply Hall | Global collision embedding into unreserved ports, internal edges, and free components | Child/parent debt cancels, root debt is zero, and no resource is charged twice |
| 6 | Prove universal waste | `square_grid_tree_universalWaste : n + 2 <= W` | Holds for every square-grid spanning tree without a realization hypothesis |
| 7 | Exclude tight residue-two waste | `ResidueTwoExactWasteExcluded` | `W != n+2` for every residue-two tree |
| 8 | Exclude stable near-tight waste | `StableResidueTwoNearWasteExcluded` | `W != n+5` for `k>=5` |
| 9 | Assemble the absolute upper formula | `maxPreserved n n <= diagonalFormulaP n` | All three residues, including `P(17)<=110` |
| 10 | Construct the stable residue-two interval tree | Score `3k^2+7k` for every `k>=7` | Repeatable incidence-tree surgery gains `6k+10` preserved vertices with a stable rooted interface |
| 11 | Formalize the stable family | `IntervalStarGluingOrder` or uniform connected U-U dual certificate | Arbitrary-width proof, not finite-width extrapolation |
| 12 | Assemble the absolute lower formula | `diagonalFormulaP n <= maxPreserved n n` | Every `n>=3` covered |
| 13 | Prove the exact formula | `maxPreserved_eq_diagonalFormulaP_unconditional` | Upper and lower inequalities combined by antisymmetry |
| 14 | Derive the recurrence | `diagonalRecurrence_proved : DiagonalRecurrence` | Formula arithmetic yields the exceptional `n=17` step |
| 15 | Verify | Full build, diff check, prohibited-token scan | No assumptions or proof shortcuts |

## Upper-Bound Program

### Exact Waste Ledger

For a spanning tree `T`, let

```text
C = gridGraph n n \ T
U = supportFinset C
F = univ \ U.
```

The project has formalized the exact identity

```text
W + 1 = boundaryDeficiency(U)
      + internalTreeEdges(U)
      + components(grid[F]).
```

The target universal inequality is therefore equivalent to producing `n+3`
distinct resources of these three kinds.

### Completed Planar Infrastructure

The following pieces are formalized:

- cyclic rectangular boundary positions;
- physical grid-edge labels;
- rooted tree shores and laminarity;
- cotree ports and path/cut equivalence;
- convexity of rooted edge-labelled channels;
- split outer ports, including both incidences at corners;
- exact equivalence between split outer ports and boundary sectors;
- abstract parent-forest leaf/branch-excess identity;
- carrier-pruned root embeddings into preserved components;
- internal-or-preserved merger dichotomy;
- generic merger/root resource factorization;
- joint merger/root routing into the contour ledger, allowing noninternal
  mergers to consume preserved-component resources;
- direct composition of the merger factorization hypotheses with the
  conditional exact waste bound;
- a concrete `GridChannelContourRealization` interface;
- direct boundary exits separated from continuing forest demands;
- injective canonical side-labelled boundary germs and direct split-outer
  termination;
- unique immediate-supershore continuation and its ranked parent forest;
- the launched-shore ancestor closure with private demand leaves;
- at most one private child per carrier, so every merger-excess slot selects a
  distinct physical shore child and attachment tree edge;
- joint injection of merger-child and maximal-root attachment edges.

Relevant modules:

```text
RootedTreeShore.lean
GridCotreePorts.lean
NoncrossingShoreChannels.lean
PlaneChannelForest.lean
GridCotreeSplitOuter.lean
GridShoreChannelForest.lean
ChannelCarrierRoots.lean
ChannelMergerResources.lean
ChannelContourRouting.lean
GridChannelContourRealization.lean
CanonicalShoreGerms.lean
CanonicalShoreContinuation.lean
CanonicalShoreForest.lean
CanonicalChannelRealization.lean
```

### Missing Planar Theorem

The launched canonical channel forest and its initial boundary maps are
constructed. The current prototype sets its later exit set to empty, so it is
not yet a universal realization.

The desired interface has the following shape:

```lean
structure GridChannelContourRealization ... where
  Carrier : Type
  channels : PlaneChannelForest Carrier

  directExits : Finset (CanonicalShoreDemand axis n)

  continuingEmbedding :
    (CanonicalShoreDemand axis n \ directExits) -> channels.demand

  exitEmbedding :
    (directExits + channels.exits) -> GridCotreeOuterPort T

  terminalResourceEmbedding :
    (channels.forest.MergerSlot + channels.forest.roots) ->
      (internalTreeEdges(U) + components(grid[F]))
```

Direct exits are necessary: a spanning tree may have cotree support on every
grid vertex, leaving no preserved component in which a mandatory nonempty
forest could terminate. Only demands that do not exit directly enter the
continuing forest.

`CanonicalChannelRealization.lean` records the conditional prototype:

```lean
CanonicalTerminalResources axis hn2 hn3 hT
```

This is exactly the existence of an embedding of `MergerSlot + roots` into the
sum of internal support-support tree edges and preserved components. It is
equivalent to the corresponding finite cardinal inequality, but it is false
for some spanning trees when the canonical forest has no later exits.

Two corrections are required. First, distinct selected noninternal tree edges
can meet the same support-free component, so edgewise component injectivity is
invalid. Second, internal edges and preserved components alone do not have
enough capacity: supported boundary sectors encountered after launch must be
retained as `channels.exits` rather than discarded by `exits := ∅`.

The next geometric theorem must classify the first terminal event along each
immediate-shore continuation as a later split-outer exit, an internal
support-support tree edge, or a preserved component. It must prove global
nonreuse across all three resource types. Only that corrected theorem can
construct an unconditional realization and yield universal waste.

The corresponding collision claim is false for the current exit-free maximal-
shore forest. A concrete `3 x 3` spanning tree has two distinct canonical roots
contacting the same preserved component, no internal support-support tree edge,
and no later exits because the prototype sets `exits := empty`. Thus the next
step must first define a port-valued split-outer continuation and truncate the
forest at first boundary contact; it cannot repair the existing maximal roots
afterward. See `analysis/CANONICAL_CARRIER_COLLISION.md`.

The abstract accounting for that theorem is now formalized by
`incidenceWaste_ge_of_prunedRootChannelRoutingWithDirectExits`. It requires
later exits to be roots of the truncated forest and routes only
`MergerSlot + (roots \ exits)` to internal-edge/component resources. Thus an
exit root replaces its carrier terminal instead of being counted twice.

`TerminalCarrierQuotientRouting.lean` now gives the exact valid factorization
of the remaining terminal condition. Physical internal tokens reserve their
own internal edges, one representative of each noninternal carrier class
reserves that preserved component, and only the labelled duplicate contacts
remain as collision debt. It constructs the original terminal embedding from
an embedding of those collisions into the unreserved resources and proves that
existence is exactly the corresponding finite capacity inequality. This removes
the false raw component-injectivity premise but does not assert collision
capacity or create resources by quotienting.

The port-valued truncation problem is now solved at the modeling level by a
different canonical forest. `GridExpandedContour.lean` refines the tree contour
to all vertex/compass slots and proves that this refinement is one cycle; split
outer ports are literal distinct missing slots, including both corner
incidences. `MarkedCycleFirstStop.lean` cuts that cycle at all supported outer
ports and shares demand-reachable suffixes. `CanonicalExpandedContourForest.lean`
embeds all `n+3` canonical demands, proves that reached ports are exactly the
roots, and gives an injective root-to-port map. Direct and later arrivals at one
port now merge before consuming the port, rather than competing for it.

Merger slots inject into distinct unsupported canonical inward tree edges, and
the port-aware quotient permits duplicate component contacts to use any
unreserved port, internal edge, or component. However, this residual condition
is exactly equivalent to universal waste, as proved by
`canonicalExpandedJointCollisionRouting_iff_incidenceWaste_ge`. It is therefore
an exact normal form, not a proof. The remaining theorem must be a localized
Hall/decongestion result with a geometric candidate relation. Straight
free-component branches do not suffice: bare supported leaf branches own no
port, internal edge, or additional component. See
`analysis/EXPANDED_CONTOUR_DECONGESTION.md`.

The finite and local transport layers are now formalized. Merger slots use a
canonical orbit-local unmarked start, and component representatives are the
first contacts in expanded-contour order rather than arbitrary quotient
choices. `LocalizedHallRouting.lean` packages Hall neighborhoods and reduces a
disjoint-owner routing to one inequality per owner fiber.

`BareCombTransition.lean` proves the exact one-layer conservation law in all
four orientations. Every gap between consecutive bare leaves has a distinct
fourth edge: a retained edge is an internal support-support resource, while an
omitted edge is retained as a labelled cotree transition carrying debt to the
next layer. `GridCellBoundaryEdges.lean` supplies the corresponding labelled
cell and dual API, including an internal-or-transition side for every cell of a
grid spanning tree. `RankedTransitionOwnership.lean` now supplies an
occurrence-indexed decreasing transition system and proves terminal reachability
with unchanged debt provenance. Equal geometric labels are not quotiented at
reconvergence. The missing theorem is still geometric global transition
splicing: it must construct those ranked states and prove final owner-fiber
capacity. Labelled transition chains can travel arbitrarily far and reconverge,
so bounded local neighborhoods and first-later-event rules do not satisfy Hall
in general.

A bounded occurrence-labelled micro-census now gives a sharper negative result:
even the complete transported trace basin can contain four preserved debt
occurrences but only three geometric slots. Provenance preservation is therefore
necessary but insufficient; reconvergence needs an explicit paid-merger resource.
The same targeted wave found that the normalized one-hull language is closed at
`n=5` but has a concrete, independently replayed two-simultaneous-hull defect at
`n=8`. Any finite upper language pursued next must be multi-hull.

However, multi-hull laminarity does not itself give finite control.
`OrderedMultiHull.lean` constructs `k` pairwise laminar nested hulls crossing one
cut for every `k`. Hull depth can therefore be arbitrarily large without a
merger or carrier collision. Before another transducer is built, a genuinely
grid-geometric low-waste bound on active hulls is required; no such noncircular
bound is currently known.

### Upper Research Plan: Reconvergence-Lens Discharge

The upper program will not build a larger fixed-hull transducer. Its next object
is a recursive planar decomposition that allows arbitrarily deep nesting and
pays multiplicity where branches first reconverge.

#### Upper Gate Status

| Gate | Status | Completed | Still required |
|---|---|---|---|
| U1 lens tree | **Complete** | concrete common-root shore regions, injective occurrence assignment, disjoint-or-nested regions, unique minimal strict-supershore parent, ranked planar forest, root characterization, outer rank-zero roots, full collar cycles, and nonempty inward face carriers | optional face-carrier laminarity refinement; not required by the U1 shore-region certificate |
| U2 physical ownership | **Complete for exposed resources** | explicit port/internal-edge/free-component-contact subtypes, geometric exposure, unique first owner, injective forgetful maps, distinct-owner disjointness, and direct outer-port reservations | resource adequacy is deliberately deferred to U3; no cardinality or matching claim is part of U2 |
| U3 regional discharge | **Research blocked at geometric assignment** | component-quotiented active-debt routing, one selected transition per original debt, distinct `q-1` interface lanes, unary contraction, root escapes, occurrence-preserving event termination, regional ledgers, and the exact local injection certificate | construct unconditional injections from active debts into first-owned raw physical resources plus selected parent passes; trace-slot/contact freshness is false and unrestricted resource freshness is circular |
| U4 telescope/Hall | **Complete conditional on U3 certificate** | corrected pass cancellation, root-pass elimination, global cardinal bound, Hall construction, and existing collision-routing-to-waste implication | instantiate the U3 regional injections; this is the only missing input to unconditional `square_grid_tree_universalWaste` |

U1 is complete using concrete rooted shore-vertex regions, which satisfy the
roadmap's planar grid-region option. Origin `Finset` containment and retained-
tree walks alone are not regions; the completed certificate does not substitute
either for the shore geometry.

#### U1. Define Lenses and Their Tree

For each ordered collision occurrence, retain its two predecessor contour
occurrences up to their first shared continuation. The two noncrossing contour
arcs between those predecessors define a candidate reconvergence lens. The
formal object must record:

```text
left and right predecessor occurrences,
the first shared continuation state,
the enclosed expanded-contour interval or planar cell region,
the originating collision labels with multiplicity,
the parent lens containing the continuation after discharge.
```

Required theorems:

1. Every collision belongs to a smallest lens.
2. Two lenses are disjoint or nested after shared contour suffixes are split by
   occurrence label.
3. Strict containment gives a decreasing finite rank, hence a parent forest.
4. The roots are the regions that reach an unreserved outer boundary sector.
5. The construction represents the concrete `n=8` two-hull prefix and does not
   assume bounded nesting depth.

Planned Lean layer:

```text
ReconvergenceLens.lean
CanonicalReconvergenceLens.lean
```

Current formal state: `ReconvergenceLens.lean` constructs one lens per concrete
binary merger slot, its nearest later-merger parent, a strict stop-distance
rank, monotone origin provenance, and the reached marked stop. The parent map is
a ranked forest. `CanonicalReconvergenceLens.lean` specializes this to the
expanded grid contour: collision occurrences embed into lenses, every lens
retains an injective physical tree-edge token, and parent lenses reach the same
split outer cotree port. It also proves strict containment of origin-occurrence
sets and the exact binary local merger picture: one private start at the merger
slot and one distinct shared predecessor equal to the expanded-contour
predecessor. `CanonicalDirectBranchGerm` and `CanonicalSharedBranchGerm` recover
the honest local geometry: a direct germ is a retained inward dart or outer
stub, while a shared germ is a retained incoming dart or in-place turn. Their
slots are distinct, and edge-valued germs have distinct oriented darts.

`GridExpandedContourTrace.lean` now erases in-place turns from any finite
expanded-contour interval and produces an actual `T.Walk`, with exact ordered
dart and edge lists. Canonical lenses therefore have proved walks from the
shared predecessor to the merger and from the merger to the reached outer-port
vertex. This also identifies the remaining obstruction precisely: every
projected edge lies in the tree, so these walks cannot form a nontrivial primal
cycle. This retained-tree limitation requires an offset/collar realization of
contour slots, including boundary stubs. Only a collar cycle can feed
`cycleInteriorFaces`; the next paragraph records the completed local part of
that bridge.

`GridExpandedContourCollar.lean` now supplies the first geometric offset. It
embeds slot sectors injectively in `gridGraph (4m+3) (4n+3)` and realizes every
expanded successor by a two-edge collar segment, including outer slots. Segment
midpoints are disjoint from every slot point and injective in their source slot.
Finite trace support is classified exactly, yielding
`collarTrace_isPath_of_advance_injective` for every nonrepeating slot interval.
The immediate remaining global theorem is that a complete one-cycle orbit is a
trail, hence an `IsCycle`; vertex repetition is already controlled, and only
undirected first/final edge nonrepetition remains. This global collar cycle does
not itself close a lens, whose direct occurrence starts at the merger; a second
lens-specific collar arc remains necessary.

That collar work is now complete. `spanningTreeCollarCycle_isCycle` proves the
full orbit is a grid cycle. For every retained inward canonical demand, an
explicit four-edge tree-corridor chord plus the contour arc from a dart to its
reverse gives `inwardShoreCollarCycle`, a genuine nonempty planar face carrier.
Raw first-stop parents are not geometric parents: a concrete small-tree audit
found parent-related fundamental shores can be disjoint. The corrected U1
hierarchy therefore orients inward darts away from their common reached outer-
port root and defines parenthood by the unique minimal strict containing shore.
`canonicalUpperU1Default` packages the unconditional completed gate. Outer
direct occurrences have rank zero and are boundary roots.

Completion gate: an occurrence-to-lens map, concrete planar regions, and the
ranked disjoint-or-nested parent forest are constructed from grid/contour data
alone, including the root-boundary characterization. No resource cardinality or
waste inequality may appear in their fields.

#### U2. Define First-Owned Physical Resources

Assign every unreserved primal resource to the smallest lens whose closed
region exposes it:

```text
supported split outer port,
retained internal support-support tree edge,
new free component first contacted inside the lens.
```

Resources on a child boundary remain owned by the child. A labelled cotree
transition is not a resource; it transports one unit of debt to the parent.
The ownership theorem must prove that distinct lenses have disjoint owned
resource sets even when their contour paths share suffixes.

Planned Lean layer:

```text
ReconvergenceLensResources.lean
```

Completion gate: explicit resource subtypes and injective forgetful maps into
the three unreserved primal resource types. Defining ownership by a global
matching or minimum-cardinality choice is forbidden.

Completion state: `canonicalUpperU2OwnershipPrimitives` and
`CanonicalUpperU2ExposedOwnership` instantiate split outer ports, retained
internal support edges, and selected free-component contacts. Exposure is
geometric, first ownership is by the smallest exposing planar shore, and the
global forgetful maps are injective with distinct-owner disjointness. This gate
is complete for the exposed-resource subtypes. Whether enough such resources
exist to pay every debt is exactly the U3 inequality, not an omitted U2 matching
assumption.

#### U3. Prove the Regional Discharge Inequality

For a lens `L`, define:

```text
localDebt(L)  = branch-excess occurrences born at L,
passed(L)     = unresolved labelled transitions leaving L for its parent,
owned(L)      = first-owned ports, internal edges, and free components.
```

The target local theorem is:

```text
localDebt(L) + sum passed(child) <= |owned(L)| + passed(L).
```

The proof must use the grid cells and contour arcs inside `L`. Bare combs use
their fourth-edge dichotomy repeatedly: retained fourth edges enter `owned(L)`;
omitted fourth edges contribute to `passed(L)`. At a reconvergence of `q`
occurrence-labelled transports, the proof must expose `q-1` new owned resources
or pass those `q-1` units separately. Equal geometric transition labels may not
collapse their multiplicity.

Completion gate: the theorem is proved for one arbitrary lens without summing
over the complete grid. If its proof invokes `W>=n+2`, unrestricted residual
capacity, or `canonicalExpandedJointCollisionRouting_iff_incidenceWaste_ge`, it
is circular and rejected.

Current formal reduction: `PlanarLensRegionalDemand` is local merger debt plus
child-arriving labelled transitions; `PlanarLensRegionalOwned` is the sum of the
three first-owned resource kinds. `parentForest_global_le_of_regional_telescope`
cancels passed transitions globally, and
`canonicalUpperU3_localInequality_implies_globalHall` reduces Hall to the local
inequality. Leaves are discharged. Every remaining region is classified as
unary propagation or genuine multi-child reconvergence. Unary regions have a
canonical first-difference slot and ranked parent-shell traversal, but still
need a theorem converting that slot injectively into a first-owned boundary
port/internal edge or an origin-labelled transition to the parent. The genuine
reconvergence inequality remains open.

The all-crossing version of that reduction was subsequently rejected: pairing
every debt with every geometrically crossing edge multiplies one occurrence into
many witnesses, and a unary resource-empty root gives a direct obstruction.
The corrected main path uses `PlanarLensDebtRouting`, one active state and at
most one selected transition per original merger slot. Unary chains contract
without independent capacity. At a genuine `q`-child reconvergence, the `q-1`
new debts inject into distinct retained child-interface collar lanes; these are
transport labels, not physical resources. Root escapes continue parentless debt
around the finite contour and `interfaceLane_eventTermination` proves
provenance-preserving arrival at a geometric event.

Arrival is not payment. Four occurrence debts can share three trace slots, and
multiple contacts can represent one raw free component. The exact remaining U3
theorem is therefore the component-quotiented regional injection

```text
activeDebt(region) -> firstOwnedRawResource(region) + selectedPass(region).
```

Root regions have no selected parent pass. `CanonicalUpperU3TransportCertificate`
and the corrected active-debt telescope package the construction and imply
global Hall once these injections are supplied. Proving them by assuming enough
unreserved capacity or unrestricted terminal freshness is rejected as circular,
because the repository already proves that complete residual routing is
equivalent to `W>=n+2`.

The corrected implementation now includes `PlanarLensDebtRouting`, distinct
child-interface transport lanes, parentless root escapes, and finite
occurrence-preserving event termination. This confirms the final obstruction:
geometric event arrival is not fresh physical payment. A deterministic first-
marked-event map is formally noninjective after reconvergence. The exact missing
statement is the component-quotiented regional paid-or-passed injection; this is
the geometric content of U3, not another bookkeeping lemma.

#### U4. Telescope and Route

Sum the regional inequalities over the lens forest. Child `passed` terms cancel
against the corresponding parent input. Root passed debt must be zero because
root regions terminate at first-owned outer resources. This yields one capacity
inequality per root subtree, hence localized Hall and the desired collision
embedding.

Planned Lean layer:

```text
ReconvergenceLensHall.lean
square_grid_tree_universalWaste
```

Completion gate: `LocalizedHallRouting.exists_owned_embedding` constructs the
physical collision routing, after which the existing quotient and contour
theorems derive `W>=n+2`.

`UniversalPrimalContourRouting.lean` packages the completed U4 endpoint. An
explicit embedding

```text
CanonicalShoreDemand axis n -> PrimalContourResource T U
```

implies `n+4 <= fourSideComponentRank n U` and then
`square_grid_tree_universalWaste`. This routing hypothesis is structured and
geometric, not a cardinal inequality. Its unconditional construction remains
exactly the open U3 regional assignment.

The boundary-noncrossing route is complete through C4: outer-edge dual-face
classification, crosscut sectors, alternating path intersection, and boundary
component nonalternation are kernel-checked. These facts constrain global-core
resource neighborhoods but do not supply the open C5 Hall inequality.

#### Immediate Upper Completion Chain

These gates must be discharged in order; later gates may use all earlier ones.

| Gate | Required theorem | Completion test |
|---|---|---|
| C1 outer-edge faces | `outerEdgeAtPosition` has dual endpoints `out` and one explicit bounded collar face | all four boundary sides and both corner incidences are kernel-checked |
| C2 crosscut sectors | boundary anchor-face side equals open-sector membership for a canonical collared crosscut | clockwise and counterclockwise closures agree with the alternating-endpoint contradiction |
| C3 path crossing | two simple grid paths joining cyclically alternating boundary pairs share a vertex | no Jordan axiom; proof uses the explicit collar cycle and row-ray parity |
| C4 component nonalternation | alternating boundary contacts in distinct induced/forced components are impossible | component paths plus C3 force component equality |
| C5 regional routing | active debts inject regionwise into first-owned raw resources plus selected parent passes | raw free components counted once; occurrence labels retained only on passes |
| C6 U3/U4 assembly | instantiate `UniversalPrimalContourRouting` | derive unconditional `square_grid_tree_universalWaste` |

The chain is not complete until C6. C1-C4 are geometric infrastructure; they do
not themselves imply a resource cardinality bound. C5 is the decisive
component-resolved routing theorem and must not be replaced by unrestricted
freshness or a global cardinal inequality.

Current completion state: C1-C4 are proved. In particular,
`grid_paths_intersect_of_cyclicallyAlternating` and
`componentLabelsNonalternating_gridBoundary` are kernel-checked. C4 is necessary
but not sufficient for C5: nonalternation forbids `C,D,C,D` contacts for
distinct components, but arbitrarily many debts can still contact one component
without alternating. C5 is therefore the root-neighborhood Hall theorem after
collapsing all contacts to raw components. Repeated contacts must be paid by
distinct internal edges, split ports, or selected parent/root-escape capacity;
they may not be counted as additional components.

The transport-classification part of C5 is now unconditional. Every full-pruned
ordered collision canonically determines its raw component, its component-local
spatial gap, the exact ordinary-or-duplicated-corner occurrence, and an omitted
cotree transition. For an ordinary gap, `ordinaryGapBoundaryCellWitness` uses
straight-component interval closure to construct the omitted opposite cell
side without a bare-comb hypothesis. Occurrence labels are retained, so equal
coordinate edges do not identify transport states and no geometric edge-
injectivity premise is needed.

The earlier attempt to inject inward collisions into merger slots on launch
supershore chains is false even for the abstract one-root contact tree: its one
leaf is balanced by its root and it has zero branch excess. The correct local
identity is `leaves = roots + branchExcess`; discarding the root summand cannot
be repaired by choosing a farther supershore. Consequently
`FullPrunedCarrierBlockGapAssignment` is now unconditional bookkeeping with no
planar-slot field. Components, spatial gaps, and omitted transitions are derived
directly from inward collisions, while the component-local cotree-dual forest
accounts for their private leaves through roots and branch excess.

The component-split cotree-dual forest exposed an important failure mode but is
not the active C5 construction. Copying the continuation core into every raw-
component fiber duplicates physical boundary roots; neither those copies nor
the resulting branch-excess slots are independent payment. The retained APIs
are legacy audit/Euler scaffolding.

The full-pruned collision source is now formally partitioned into inward- and
outer-direct germs. Inward collisions have a canonical injective launch into the
corrected shore forest. An outer collision's direct port is its reached
`lensOuterPort` and lies in the existing `exitEmbedding` range, so that port is
excluded from the unreserved pool and cannot pay the collision. Both inward and
outer collisions remain source obligations. The exact residual target is still
an embedding of their sum into genuinely unreserved ports, internal edges, and
raw components.

Audited implementation chain after global-core correction:

1. Keep one global cotree/escape core; component data labels contacts but does
   not copy continuation vertices, roots, or branches.
   `FullPrunedSharedCotreeDualEdgeOccurrence` and
   `fullPrunedSharedCotreeDualForest` implement this carrier; selected gaps keep
   collision provenance while each actual cotree transition occurs once.
2. Retain each original active debt through the global escape system and define
   `RootDebtCanUse` only from a reached raw resource that the same root first
   owns.
3. `canonicalPlanarLensDebtRouting` now discharges all nonroot local-interface
   and inherited-pass obligations by exact descendant-fiber conservation.
4. The former `CanonicalUpperU3RootHall` endpoint is too narrow: its escape
   system emits only a common outer-port candidate for all debts at one root.
   Kernel-checked no-go lemmas show that Hall would force each root active fiber
   to have size at most one.
5. The replacement launch is now constructed: every planar merger debt selects
   a distinct first-stop token, pays once at the ranked component representative,
   or continues as an occurrence-labelled repeated-component collision. A
   `FullPrunedRegionalCertificate` turns this into an injective map to boundary,
   internal-edge, and raw-component resources.
6. The regional certificate cannot be constructed unconditionally: a concrete
   `3 x 3` tree has no first-owned residual terminal for its ranked collision.
   Replace regional first ownership by a global exchange/routing theorem, or use
   a direct inequality that does not localize payment to one inward shore.

The grouped Python audit now combines occurrence-preserving raw-component
continuation, tree-basis exchange through both internal edges and reached raw-
component contact edges, ordered outer walks, reverse-root traversal, and
internal support-support edge pass-through to the opposite incident dual face.
Exhaustive `n=3,4` testing over every gap bijection and source subset reaches
Hall in every audit. The opposite-face rule repairs `T780` by continuing through
boundary edge `(7,11)` to `OUT` and then to port `(11,E)`, without counting the
internal edge twice. Contact-edge basis exchange repairs the final `T779` audit:
the reached component-`11` contact `(10,11)` exchanges through omitted edge
`(10,14)` and reaches residual component `12`, again without adding a physical
resource or quotienting the initiating occurrence. This remains analysis
evidence, not a Lean theorem.

The extended falsification campaign covers 44 random/targeted trees at each
`n=5,6,7,8`, both axes. It checks all gap bijections in 351 of 352 axis audits
and 64 seeded samples of the remaining `n=8` audit's 720 choices. Ledgers with
at most four sources are exhaustively enumerated; larger ledgers use exact
bipartite maximum matching with a recoverable Hall witness. No failure was
found. The maximum grouped source count was six, and the campaign took 13.24
seconds; see `analysis/alternating_closure_grid_trees_n5_n8.json`.

The legacy component-split layer now proves its tree-cotree boundary
connectivity and exact root classification, but that does not repair its copied
continuation roots. Likewise `ComponentResolvedBoundaryGapHullExpansion` and
`CanonicalGroupedResidualHullExpansion` quantify over injective witnesses for
every selected set: they are Hall-strength assumptions, not topology lemmas.
Arbitrary first-separator and outer-collision classifications in that layer are
retained for compatibility only and are not active launch mechanisms.
The shared-core Euler/root APIs are present, but the build currently blocks in
their elaboration and the physical Hall step remains unproved.

#### Upper Falsification Gates

Every proposed definition or local inequality must be checked against:

1. The `3 x 3` duplicate-component collision.
2. Arbitrarily long bare combs with no bounded local final resource.
3. The four-debt/three-trace-slot transported-basin counterexample.
4. The `n=8` nested two-hull prefix.
5. The arbitrary-depth concentric hulls of `OrderedMultiHull.lean`.

The first four are required positive coverage tests; the fifth forbids any fixed
hull-depth assumption. Bounded computation may falsify a concrete lens rule,
but cannot establish the regional theorem.

The strictness arithmetic for Steps 7 and 8 is also prepared independently.
`CheckerboardColorWaste.lean` gives exact colorwise waste ledgers and the tight
and near-tight residue-two normal forms. `CanonicalDemandPhase.lean` proves the
phase and phase/color histograms, including provenance sums over reached exits.
`CheckerboardContourMarks.lean` partitions actual contour marks by supported
vertex color, and `ResidueTwoColorCapacity.lean` proves parity-specific tight
and near capacity rigidity conditional on a color-preserving anchored marking.
These are prerequisites for the exclusions, not yet contradiction theorems.

### Residue-Two Upper Exclusions

After universal waste, residue zero and residue one have the required absolute
upper values. Residue two requires two additional exclusions.

The tight case is reduced to nonexistence of an acyclic complementary forced
profile with support cardinality

```text
6k^2 + 5k + 2.
```

The stable near case is reduced to nonexistence of a tree support with
cardinality

```text
6k^2 + 5k + 3.
```

Relevant formal propositions:

```text
ResidueTwoExactWasteExcluded
ResidueTwoTightAttachmentContradiction
StableResidueTwoNearWasteExcluded
StableResidueTwoPersistentAttachmentDebt
```

The preferred proof is a phase-refined version of the planar channel theorem,
not another scalar potential. Component identities and checkerboard phase must
survive pruning so that equality forces an additional merger, exit, or carrier
resource.

## Lower-Bound Program

The only missing infinite lower family is stable residue two from `n=23`
onward.

Before formalizing another candidate, verify these conditions symbolically:

1. No unit cell contains three forced vertices.
2. No unit cell contains diagonally opposite forced vertices.
3. Every induced forced component is a straight interval.
4. Every interval-star is a tree.
5. The incidence graph of interval-stars is a forest.
6. The successor gains exactly `6k+10` forced vertices.
7. The successor interface is stable under `k -> k+1`.
8. No bounded dual face is isolated.
9. No nonempty proper symbolic face set has empty dual boundary.
10. A uniform acyclicity or dual-connectivity proof exists before Lean coding.

The existing affine family is now proved symbolically at arbitrary width. Old
occurrences embed through a step either by moving the final pumped block or by
keeping its copy at the insertion. Explicit seam paths transport every old dual
edge, and symbolic row/column corridors attach every inserted face. This gives
the unconditional near-target bound `3k^2+6k+5 <= P(3k+2)` for `k>=5`, without
a finite-state search. The exact family must improve this by `k-5` preserved
vertices while retaining a similarly closed-form interface.

A useful next abstraction is a comb-gluing theorem:

> A union of straight interval-star trees is acyclic when every physical
> intersection is uniquely owned and the global incidence multigraph is a
> forest.

This would turn the stable residue-two construction problem into designing a
periodic interval family of exact cardinality `3k^2+7k` with a tree-shaped
incidence graph.

That abstraction is now formalized in `IntervalStarGluing.lean`. It proves
binary forest gluing along at most one active vertex, lifts this to indexed
leaf-elimination orders, and specializes the result to unions of forced
interval-stars.

The simplest promoted-affine application is impossible. In every repeated
`3 x 3` pump block the affine pattern is `UU.` in each row. Promoting either U
vertex completes a forced unit-cell cycle against the neighboring preserved
column. More generally, the first nontrivial affine member at `k=6` admits no
valid single-vertex promotion, so adding one independent preserved vertex per
pump block cannot produce the exact family. The next candidate must change the
seam by a coordinated add/delete exchange or use a different closed-form
interval family; do not launch a state search for promotions.

The smallest endpoint exchange is impossible as well. Shortening one preserved
vertical spine by one vertex and filling the adjacent two-vertex `UU` gap has
the correct net cardinality, but the second insertion completes a forced unit
square with the surviving spine endpoint. At `n=20`, existing complete local
checks exclude every net-one affine repair through three additions and four
deletions. The first affine-neighborhood size not already excluded is therefore
four additions and five deletions, and existing slab negatives require such a
change to coordinate the middle with the closing cap. No width-independent
coordinates or rooted-interface proof are currently known for that exchange.

A deterministic 75,296-template census also excludes one broad stable repair
grammar: period-at-most-three contiguous assignments repeated in every bulk
packet of the affine family, together with all subsets of five fixed cap/seam
toggles, produce no exact candidate simultaneously at `n=23,26,29`. This does
not exclude nonuniform seams, multiple operations per packet, or a different
interval-incidence skeleton; do not enlarge the grammar automatically.

The affine family's own interval skeleton is now independently audited at
`k=7,8,9`: it has `4k` straight preserved intervals and `4k-1` singleton
physical attachment links forming a tree, with a valid leaf-elimination order.
Lean records that its score is exactly `k-5` below the stable target and that
each pump gains `6k+9`, one below the required `6k+10`. Thus the remaining lower
problem is specifically to invent a different scalable incidence tree, not to
repair the affine acyclicity proof.

### Lower Research Plan: Interval-Incidence Tree Surgery

The lower program will design topology and coordinates together, subject first
to the exact component budget in the 2026-09-05 reassessment. An abstract tree
with the right total length is not enough; neither connected incidence nor
preservation of every old node is required for a feasible forced forest.

#### Lower Gate Status

| Gate | Status | Completed | Still required |
|---|---|---|---|
| L1 rooted skeleton | **Partial; counter family globally obstructed** | audited affine skeleton; counter arithmetic, but its `4k+1` distinct maximal components are impossible throughout the intended `k>=7` range | target geometry with `r+c+b=3k+12`, hence `r<=3k+6` |
| L2 repeatable surgery | **Research blocked** | exact abstract `6k+10` counter subdivision plus complete obstructions for all declared affine repairs, neighboring-residue cap splices, periodic bulks through `6x6`, safe combs, one-wall seams, bounded elbow islands, and buffered three-wall junctions | genuinely new unbounded/nonlocal incidence topology, packet-dependent branching surgery, or global dual-tree construction; no further bounded local grammar is justified |
| L3 grid realization | **Open** | deterministic geometry validators for cells, straight components, interval stars, incidence trees, and forced forests | uniform coordinates surviving `k=7,8,9`, followed by symbolic all-`k` geometry proofs |
| L4 Lean family | **Open** | reusable `IntervalStarGluingOrder` acyclicity theorem and affine symbolic precedent | target family definitions, cardinality, gluing order, forest extension, and stable residue-two lower theorem |

Negative finite censuses close only their declared grammars. They are completed
falsification gates, not evidence that L2 or L3 as a whole is complete.

#### L1. Specify an Abstract Rooted Skeleton

Represent each preserved component by:

```text
orientation,
fixed row or column,
two symbolic interval endpoints,
one parent attachment vertex,
an ordered list of child attachment vertices.
```

The following was the original rooted-tree design brief. It is now an optional
sufficient subclass: allow a forest, a growing interface, and interval mergers.
Any replacement must first pass the component-budget gate. The old brief was:

```text
total interval length = 3k^2+7k,
S_(k+1) contains an embedded copy of S_k outside the insertion cross,
new and lengthened intervals contribute exactly 6k+10 vertices,
every new interval has one parent in the uneliminated suffix.
```

The number of maximal intervals is not fixed in advance, but must be at most
`3k+6` at the stable target. The audited affine value `4k` cannot be retained
indefinitely. Parent/child incidence and coordinates should be developed
together; abstract owner names do not certify realizability.

Deliverable: a paper definition of the index type, interval lengths, parent
map, insertion map, and exact symbolic cardinality recurrence.

Completion gate: all endpoint and counting formulas are valid for arbitrary
`k>=7`; no finite witness or interpolated polynomial substitutes for the proof.

#### L2. Design One Repeatable Tree Surgery

The successor operation may detach and reattach a whole branch. It must not be
expressible as independent affine-U promotions. A valid surgery must specify:

1. Which old intervals are embedded unchanged.
2. Which old endpoints move by three under row/column insertion.
3. Which branch is detached from its old physical owner.
4. Which intervals are lengthened or introduced.
5. The new singleton attachment that reparents the detached branch.
6. Why the net preserved gain is exactly `6k+10`.

The proof obligation is an explicit leaf-elimination order for the successor
incidence tree. The old order should transport through the insertion map, with a
closed-form list of new leaves inserted near the reparented branch.

Completion gate: the abstract successor tree is connected and acyclic by its
parent map, and every attachment is assigned a unique symbolic physical owner.

Historical abstract candidate: `analysis/RESIDUE_TWO_COUNTER_INTERVAL_SURGERY.md`
subdivides the affine root-to-boundary-spine edge by a counter interval `C_k` of
length `k-5`. It has `4k+1` nodes, `4k` parent links, target total length
`3k^2+7k`, a transported postorder, and exact step gain `6k+10`. The two new
physical owners remain symbolic. Its abstract count/tree statements remain
valid, but the component-budget obstruction rules out its uniform realization
as distinct maximal intervals throughout its `k>=7` range. It is no longer an
active L3 candidate.

#### L3. Realize the Skeleton in the Grid

Give affine coordinate formulas for every interval endpoint and attachment.
Prove, symbolically:

1. All coordinates lie in the `(3k+2) x (3k+2)` grid.
2. Distinct centers are disjoint and their union has the target cardinality.
3. Every center is a straight interval.
4. Every forced interval-star is a tree.
5. Each star meets the uneliminated suffix only at its declared parent vertex.
6. No undeclared pair of stars has a second physical intersection.
7. The construction has a stable `k -> k+1` rooted interface.

Only after these formulas exist may `construction_lab.py` check `k=7,8,9` as a
falsification and transcription test. A successful finite check is not the
proof; any failure sends the design back to L1 or L2 without widening a search.

The natural corner realization of the counter candidate has been falsified
completely in its declared bounded grammar. For `k=7,8,9`, every horizontal
all-new counter interval in the `7 x 7` attachment corner, with one to three
root/boundary-spine deletions and equally many compensating additions, fails the
unit-cell condition. The deterministic census classifies all `7,912,264`
choices and stores replayable witnesses. This excludes only that grammar. A
replacement must place the counter elsewhere, reuse old centers, edit adjacent
components, or obtain the extra endpoint by lengthening an existing interval.

The existing-interval alternative is now exhausted too. The two endpoints of
all `28` affine intervals at `k=7` give `56` transported endpoint types. Adding
the required `k-5` collinear cells has the exact target count and contributes
the missing `+1` per transition, but every type fails across `k=7,8,9`: it is
out of grid, meets an old center, violates a unit cell, or merges components.

The obstruction-derived one-blocker repair is also complete. Exactly `20`
constant-size transported leaf blockers arise from the first endpoint failures;
translating each by one cardinal grid step gives `80` hard-capped chains. None
realizes even one width without a forbidden cell, overlap, multiple star
intersection, or non-blocker parent change. The next symbolic topology is a
two-leaf hinge exchange: move one of the six multiple-intersection blockers or
the single parent-change blocker together with its adjacent hinge leaf, then
lengthen the carrier and install one new singleton owner. This topology must be
specified before another census.

That two-leaf hinge gate is now complete as well. The seven late-stage witnesses
name only two legal constant-size leaf hinges; both fail at `k=7,8` by forbidden
unit cells and at `k=9` by overlap. The other five witnesses require splitting a
nonleaf root or vertical spine. Their minimal projected-segment bypass also
fails uniformly: the spine/carrier distance is two while the bypass length is
`k-5>=2`, so the bypass necessarily contains the far carrier-ray center and
loses at least one count. The next declared topology is an offset bypass with a
`k-7` core and two one-center connector leaves. At `k=7` the core is empty.

All subsequent justified lower branches have now also been closed. Immediate
and borrowed offset bypasses, a two-layer dogleg, residue-zero terminal-cap and
double-cap exchanges, sparse two-layer and three-layer ladders, all density-one-
third periodic bulks through `6x6`, a horizontal safe-comb base, a staircase
horizontal/vertical domain wall, two-wall elbow islands, and the final buffered
three-wall junction all fail their declared gates. The periodic classifications
collapse to parallel rails with score `3k^2+5k+2`. The best one-wall seam has
gain `6k+9`, one short per pump. Bounded islands either lose count or cannot
produce singleton incidence ownership. The final buffered class has singleton
articulations but no incidence parent tree and gain only `6k+5`.

The lower gate therefore remains open but is now explicitly research blocked.
No wider local census should be launched. A next construction needs genuinely
new mathematics: an unbounded packet-dependent branching incidence tree, a
global dual-tree coordinate construction, or a nonlocal connectivity theorem
that can be converted into uniform coordinates.

#### L4. Formalize Through Interval-Star Gluing

Planned Lean layer:

```text
ResidueTwoStableIntervals.lean
ResidueTwoStableIntervalGeometry.lean
ResidueTwoStableIntervalMax.lean
```

Required formal objects:

```lean
residueTwoStableIntervalCenter
residueTwoStableIntervalOrder
residueTwoStableIntervalGluingOrder
residueTwoStablePreserved_card
residueTwoStable_le_maxPreserved
```

`IntervalStarGluingOrder.forcedEdgeGraph_isAcyclic` supplies forced acyclicity.
Forest extension then gives a preserving spanning tree. The final theorem must
populate `RemainingMatchingDiagonalConstructions.residueTwoTail` for every
`k>=7`.

#### Lower Falsification Gates

Reject a proposed surgery immediately if it exhibits any of:

1. Three preserved vertices or a preserved diagonal pair in one unit cell.
2. A second physical intersection between two interval-stars.
3. A cycle in the contracted incidence multigraph.
4. The isolated face of `uResidueTwoExact 7`.
5. The persistent two-face cut of the balanced exact repair.
6. A gain other than `6k+10`.
7. An interface whose type or coordinate formulas grow with `k` without a
   uniform symbolic description.

The affine skeleton checker is the baseline regression. The new family may
change its topology, but it must retain equally explicit parent ownership and a
leaf-elimination proof.

## Two-Sided Surgery Infrastructure

The crop-surgery work remains valid and useful, but it is no longer the primary
critical path to the formula.

Completed pieces include:

- public `BundleToothCertificate` objects;
- exact defect-sized terminal sets;
- first-tooth forced endpoints and exact endpoint coverage;
- triangle-free grid specialization with at most three deletions;
- sequential delete/add surgery traces;
- exact telescoping cardinality;
- final-state normalization to `(C \ D) union R`;
- exact crop delete/add frame-loss accounting;
- endpoint-fiber sharing and exact deletion-saving identities;
- all sixteen total-three crop embeddings;
- exact sixteen-crop survival and frame-loss incidence sums;
- a conditional aggregate upper-recurrence interface.

The missing surgery theorem is still the global surplus inequality

```text
sum_Q (|R_Q| - |D_Q|) >= sum_Q max(0, frameLoss_Q - 2n).
```

No current theorem forces enough endpoint sharing or zero-defect insertions to
pay the defect-two and defect-three owners. This route should remain secondary
unless a new geometric discharge theorem is found.

## Disproved Approaches

Do not repeat these approaches without a materially different invariant or
construction.

| Candidate | Exact failure |
|---|---|
| Monotone Four-Crop unit-resource charging | One repair owner may carry three independent cycle defects |
| Abstract branch slots as deletion capacity | De-forcing an interior forced branch vertex need not remove forced-forced edges |
| Raw exact residue-two pump | The first `n=23` successor has an isolated dual face |
| Seam-balanced exact repair | It creates a persistent two-face dual cut |
| Cap-balanced exact repair | Every positive pump depth creates two isolated top faces per cap deletion |
| Full-row stripe bridges | The first bridge completes a forced unit-cell cycle |
| Cropping the residue-zero family by one row and column | Every contiguous corner crop loses far too many forced vertices |
| Monotone residue-one one-frame extension | Its sharp gain is only `k+2`, below the required `2k` |
| Two persistent boundary caps plus horizontal combs | The component-incidence graph contains `K_(2,k+1)` cycles |
| Scalar component/boundary potentials | Exact ledgers show they only re-express cardinality |
| Seam components as injective resources | Distinct physical demands may share one seam component |
| One affine-U promotion per pump block | Every repeated-block candidate closes a forced cell cycle; the `k=6` affine member has no valid single promotion |
| Shorten one affine spine and fill its adjacent `UU` gap | The second inserted center completes a forced unit-square cycle through the surviving spine endpoint |

Negative results are part of the proof state. Preserve them so future work does
not return to refuted local models.

## Formula Assembly

Once absolute upper and lower bounds are available, prove the formula directly:

```lean
theorem maxPreserved_eq_diagonalFormulaP_unconditional
    (n : Nat) (hn : 3 <= n) :
    maxPreserved n n = diagonalFormulaP n :=
  Nat.le_antisymm
    (maxPreserved_le_diagonalFormulaP n hn)
    (diagonalFormulaP_le_maxPreserved n hn)
```

Then expose the currently private arithmetic recurrence for
`diagonalFormulaP` and derive:

```lean
theorem diagonalRecurrence_proved : DiagonalRecurrence where
  three := maxPreserved_three_three
  four := maxPreserved_four_four
  five := maxPreserved_five_five
  step := by
    intro n hn
    rw [maxPreserved_eq_diagonalFormulaP_unconditional n (by omega)]
    rw [maxPreserved_eq_diagonalFormulaP_unconditional (n - 3) (by omega)]
    exact diagonalFormulaP_recurrence n hn
```

The existing theorem

```lean
maxPreserved_eq_diagonalFormulaP_of_recurrence
```

remains useful, but the preferred dependency now runs from the formula to the
recurrence rather than requiring recurrence-specific surgery first.

## Formalized State To Preserve

- `maxPreserved_eq_maxForcedAcyclic`
- forced-forest insertion and maximality criteria
- straight induced forced components and interval lemmas
- exact crop signatures and labelled quotient admissibility
- cyclic boundary nonalternation infrastructure
- public tooth-cut certificates
- sequential tooth surgery and final-state normalization
- exact shared-endpoint capacity accounting
- sixteen-crop indexing and incidence identities
- abstract plane-channel pruning
- split outer ports and boundary-sector equivalence
- carrier-pruned root embeddings
- merger/internal-or-component factorization
- conditional contour-to-waste theorem
- exact bases `P(3)=4`, `P(4)=8`, `P(5)=11`
- residue-zero and residue-one construction families
- finite residue-two construction scores through `n=20`
- recurrence-to-formula arithmetic
- generic path-valued connectivity transport for construction steps

## Active Priority Order

Revised order as of 2026-09-05:

1. Formalize the five-unit boundary lemma and its single-perimeter-gap equality
   case, the component-budget obstruction, and the opposite-neighbor connector
   restriction, reusing the existing ledger and cell-cycle lemmas.
2. Lower: design actual long-interval geometry with `Delta B=3`; allow mergers
   and a growing ancestry-aware interface. Check budget and geometry together.
   The optional `b=5,c=1,r=3k+6` subclass is a design hypothesis, not a theorem.
3. Upper: seek a direct geometric minimum-budget proof or continue global
   physical alternating exchange. Neighborhood uncrossing may organize tight
   regions but does not itself supply the missing geometric inequality.
4. Demand a concrete geometric advance before adding more generic routing,
   matching, or tree-gluing interfaces. Keep the conjecture open to revision.
5. Prove both bounds unconditionally, assemble equality, then derive recurrence.

Historical priority list, retained for context rather than as a mandatory
pipeline (in particular, the regional discharge item is superseded by its
recorded counterexamples):

1. Find a global ownership-exchange or direct geometric proof of universal
   waste. Do not assume `FullPrunedRegionalCertificate`, summed four-crop repair
   rank, balanced four-crop repair, checkerboard color-run bounds, or the axial
   carrier-gap strengthening; each has an explicit counterexample. Likewise do
   not assume bounded insertion-circuit path, angle-sector, or minimum-reflex
   congestion: maximal forced-forest counterexamples are recorded for all three.
2. The physical alternating-exchange relation is now fully typed and its finite
   saturation passes exhaustive `n <= 4` testing and targeted testing through
   `n = 8`. Prove that no source-indexed alternating closure is Hall-deficient
   at arbitrary width; this is the active global expansion theorem.
2. Instantiate `UniversalPrimalContourRouting` and derive
   `square_grid_tree_universalWaste`.
3. Lower L1-L2: invent a genuinely nonlocal target-count incidence topology;
   all currently declared local/periodic grammars are exhausted.
4. Lower L1: specify the resulting target-count rooted interval skeleton
   independently of its coordinates.
5. Upper U3-U4: prove regional discharge, telescope it, and derive universal
   waste through localized Hall.
6. Lower L3-L4: realize the surgery in coordinates, falsify it at `k=7,8,9`,
   then formalize the arbitrary-width family through interval-star gluing.
7. Prove tight and stable near-tight residue-two upper exclusions using the
   phase/color refinements of the lens ownership.
8. Assemble the complete absolute upper and lower formulas.
9. Prove the unconditional diagonal formula.
10. Derive `DiagonalRecurrence` as a corollary.

The upper-bound and stable-construction tracks can proceed independently.

## Repository Navigation

| Path | Purpose |
|---|---|
| `docs/ROADMAP.md` | Current proof roadmap |
| `docs/ROADMAP_OLD.md` | Historical computational and phase roadmap |
| `lean/STATUS.md` | Detailed Lean proof status |
| `lean/EVIDENCE.md` | Lean theorem and evidence index |
| `lean/GridGraphs.lean` | Root Lean module |
| `lean/GridGraphs/DiagonalFormula.lean` | Formula and conditional assembly |
| `lean/GridGraphs/DiagonalRecurrence.lean` | Recurrence package and arithmetic theorem |
| `lean/GridGraphs/SmallDiagonalExact.lean` | Exact `3 x 3` and `5 x 5` bases |
| `lean/GridGraphs/ForcedMaximum.lean` | Exact forced-set optimization equivalence |
| `lean/GridGraphs/PlaneChannelForest.lean` | Abstract channel pruning count |
| `lean/GridGraphs/ReconvergenceLens.lean` | Generic occurrence lens parent forest and origin containment |
| `lean/GridGraphs/CanonicalReconvergenceLens.lean` | Canonical lenses, completed nonroot debt routing, and audited root-Hall no-go endpoint |
| `lean/GridGraphs/GridExpandedContourTrace.lean` | Stutter-erased finite contour intervals as exact retained-tree walks |
| `lean/GridGraphs/GridExpandedContourCollar.lean` | Injective offset collar segments and nonrepeating-interval path theorem |
| `lean/GridGraphs/ChannelContourRouting.lean` | Conditional channel-to-waste and upper bounds |
| `lean/GridGraphs/NoncrossingShoreChannels.lean` | Rooted channel laminarity and convexity |
| `lean/GridGraphs/ResidueZero*.lean` | Residue-zero constructions and connectivity |
| `lean/GridGraphs/ResidueOne*.lean` | Residue-one constructions and reverse frame |
| `lean/GridGraphs/ResidueTwo*.lean` | Residue-two constructions, reductions, and failed pumps |
| `analysis/RESIDUE_TWO_COUNTER_INTERVAL_SURGERY.md` | Exact abstract `6k+10` counter-edge subdivision |
| `analysis/RESIDUE_TWO_COUNTER_INTERVAL_L3_CENSUS.md` | Complete negative census for its natural corner realization grammar |
| `analysis/RESIDUE_TWO_AFFINE_ENDPOINT_EXTENSION_OBSTRUCTION.md` | Complete obstruction for all transported single-endpoint types |
| `analysis/RESIDUE_TWO_ENDPOINT_SLIDE_OBSTRUCTION.md` | Complete obstruction for the derived one-blocker slide grammar |
| `analysis/RESIDUE_TWO_TWO_LEAF_HINGE_OBSTRUCTION.md` | Complete obstruction for the two witness-derived leaf hinges |
| `analysis/RESIDUE_TWO_NONLEAF_SPINE_BYPASS_OBSTRUCTION.md` | Symbolic overlap obstruction for five minimal nonleaf bypasses |
| `analysis/RESIDUE_TWO_TWO_LAYER_DOGLEG_EXHAUSTION.md` | End of the affine-derived local surgery line |
| `analysis/PERIOD_THREE_RESIDUE_TWO_BULK.md` | Complete `3x3` density-one-third bulk classification |
| `analysis/SIX_BY_SIX_RESIDUE_TWO_BULK.md` | Complete `6x6` density-one-third bulk classification |
| `analysis/RESIDUE_TWO_BUFFERED_BRANCH_OBSTRUCTION.md` | Final bounded domain-wall/branching obstruction |
| `analysis/` | Historical experiments, proof notes, and counterexamples |

## Verification Policy

After each theorem module:

```bash
cd lean
lake env lean GridGraphs/NewModule.lean
```

Before reporting a milestone:

```bash
cd lean
lake build
cd ..
git diff --check
```

New proof files must be scanned for:

```text
sorry
admit
axiom
native_decide
run_tac
```

Do not introduce computational search as a proof dependency. Keep hypotheses
explicit until the corresponding unconditional theorem is constructed.

At the time of this rewrite, the full Lean build passes with 7,471 jobs.
