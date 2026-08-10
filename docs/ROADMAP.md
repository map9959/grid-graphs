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
| 3 | Prove merger/root accounting | Embed `MergerSlot + roots` into internal `U-U` tree edges plus preserved components | Every `k`-way merger retains all `k-1` excess units; no component is charged twice |
| 4 | Prove universal waste | `square_grid_tree_universalWaste : n + 2 <= W` | Holds for every square-grid spanning tree without a realization hypothesis |
| 5 | Exclude tight residue-two waste | `ResidueTwoExactWasteExcluded` | `W != n+2` for every residue-two tree |
| 6 | Exclude stable near-tight waste | `StableResidueTwoNearWasteExcluded` | `W != n+5` for `k>=5` |
| 7 | Assemble the absolute upper formula | `maxPreserved n n <= diagonalFormulaP n` | All three residues, including `P(17)<=110` |
| 8 | Package existing lower constructions | Unified lower theorem for residues zero and one and residue two through `n=20` | Only stable residue two remains |
| 9 | Construct the stable residue-two family | Score `3k^2+7k` for every `k>=7` | Uniform symbolic acyclicity or connected U-U dual proof |
| 10 | Assemble the absolute lower formula | `diagonalFormulaP n <= maxPreserved n n` | Every `n>=3` covered |
| 11 | Prove the exact formula | `maxPreserved_eq_diagonalFormulaP_unconditional` | Upper and lower inequalities combined by antisymmetry |
| 12 | Derive the recurrence | `diagonalRecurrence_proved : DiagonalRecurrence` | Formula arithmetic yields the exceptional `n=17` step |
| 13 | Verify | Full build, diff check, prohibited-token scan | No assumptions or proof shortcuts |

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

1. Define the correct `GridChannelContourRealization` using pruned actual
   channel states.
2. Prove its unconditional existence for every square-grid spanning tree.
3. Derive the universal waste bound `W >= n+2`.
4. Prove the tight residue-two profile exclusion.
5. Prove the stable near-tight residue-two profile exclusion.
6. Assemble the complete absolute upper formula.
7. Design a new stable residue-two interval/incidence-tree family.
8. Prove the complete absolute lower formula.
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
| `lean/GridGraphs/ChannelContourRouting.lean` | Conditional channel-to-waste and upper bounds |
| `lean/GridGraphs/NoncrossingShoreChannels.lean` | Rooted channel laminarity and convexity |
| `lean/GridGraphs/ResidueZero*.lean` | Residue-zero constructions and connectivity |
| `lean/GridGraphs/ResidueOne*.lean` | Residue-one constructions and reverse frame |
| `lean/GridGraphs/ResidueTwo*.lean` | Residue-two constructions, reductions, and failed pumps |
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
