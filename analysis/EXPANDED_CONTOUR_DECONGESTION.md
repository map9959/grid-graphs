# Expanded Contour Decongestion

## Proven Model

The expanded contour has one state for every vertex/compass-direction pair.
Its successor is

```text
(v,d) -> (w,d.opposite.clockwise)  if v--w is the retained edge in direction d,
(v,d) -> (v,d.clockwise)           otherwise.
```

`GridExpandedContour.lean` proves that this is a permutation and, for every
nontrivial spanning square-grid tree, one cycle. Its first return to occupied
slots is the existing directional-dart contour successor.

Every split outer port is the distinct missing slot

```text
(port.vertex, port.outwardDirection).
```

Thus the two incidences at a supported corner remain distinct without adding a
choice of side after the fact.

`MarkedCycleFirstStop.lean` cuts a finite permutation at marked states, retains
only states reached from selected starts before their first mark, shares merged
suffixes, and adds one private leaf per start. For this forest:

```text
leaves = private demands,
roots = reached marked exits,
merger excess = starts - reached exits.
```

`CanonicalExpandedContourForest.lean` instantiates that construction with all
`n+3` canonical demands. A directly supported demand starts at its outward port
slot; every other demand starts at its retained inward slot. The start map is
injective, and reached exits embed injectively into split outer ports. Direct
and later arrivals at the same port are therefore represented by one root and
their additional branches by merger excess.

## Physical Tokens

Every merger slot injects into an unmarked start and hence into a distinct
retained canonical inward tree edge. Since the boundary endpoint of such an
edge is outside cotree support, every selected token is noninternal. One token
per contacted free component reserves that component; repeated contacts become
labelled carrier collisions.

The preferred residual routing permits each collision to use any still-unused:

```text
split outer port,
internal support-support tree edge,
free component.
```

This is formalized by `PortAwarePhysicalTreeTokenQuotientRouting`.

## Exact Audit

The residual routing proposition is not a stronger geometric theorem. The
formal theorem

```lean
canonicalExpandedJointCollisionRouting_iff_incidenceWaste_ge
```

proves

```text
CanonicalExpandedJointCollisionRouting
  <-> n+2 <= incidenceWaste.
```

Indeed, writing `E` for reached exits, `M` for merger slots, `Q` for contacted
component classes, `C` for collisions, and `B,I,K` for all ports, internal
edges, and free components:

```text
E + M = n+3,
Q + C = M,
unreserved capacity = (B-E) + I + (K-Q).
```

Therefore

```text
C <= unreserved capacity
  <-> n+3 <= B+I+K
  <-> n+2 <= incidenceWaste.
```

Changing between row and column axes changes `C` and `Q`, but they cancel in
the same identity. Axis selection alone cannot improve the residual deficit.

## Failed Local Shortcut

A maximal free run on the left boundary is a vertical free component. Every
row start on that run uses a distinct inward tree edge, but all those tokens
have the same component carrier. Forced-component straightness does not pay the
duplicates locally.

In particular, an inward attachment branch may be bare: one interior supported
tree leaf attached to the free component, with no outer port, no internal
support-support tree edge, and no second free component in that branch. Such a
branch supplies no local resource. Several bare branches can occur on one
straight component.

Hence the following proposed ownership rule is false:

> Every repeated contact owns a port, internal edge, or distinct component in
> its own attachment branch.

## Ordered Bare-Comb Transport

The local failure still has an exact conservation law. In a maximal one-sided
run of consecutive bare leaves, consider each unit-cell gap between neighboring
leaves. Three sides of the outward cell are cotree edges. Its distinct fourth
edge is either:

```text
retained: an internal support-support tree-edge resource,
omitted:  a labelled cotree transition to the next dual layer.
```

Thus a run with `k` contacts has `k-1` duplicate-contact debts and exactly
`k-1` distinct immediate payments or transition labels. This is formalized for
all four orientations in `BareCombTransition.lean`.

Transition labels are not final resources. They can propagate through
arbitrarily many layers and several transition chains can reconverge. The next
global theorem must splice these layers while preserving multiplicity and
assign disjoint final owners. `LocalizedHallRouting.lean` provides the finite
Hall endpoint once those owner-fiber inequalities are proved.

`RankedTransitionOwnership.lean` now records the required multiplicity model:
states are occurrences carrying their original debt, not geometric transition
labels. A decreasing rank forces every chain to a terminal occurrence while
preserving provenance, even when distinct occurrences use the same transition
label after reconvergence. `GridCellBoundaryEdges.lean` also proves that every
grid-tree cell has a side supplying either an internal resource or a labelled
cotree transition. What remains is to instantiate the ranked states globally
and prove the owner-fiber capacities.

The targeted occurrence-labelled Hall census in
`TARGETED_COMPUTATION_WAVE_2026-08-11.md` shows that assigning every occurrence
all geometric slots in its transported trace basin still fails Hall: four debts
can share a basin with only three slots. Thus a global construction must pay
each reconverged branch-excess unit with a new physical primal resource. Merely
widening the neighborhood from terminal slots to complete transition traces is
not sufficient.

## Next Theorem

The next result must be a genuinely localized Hall/decongestion theorem, not an
unrestricted embedding or total cardinal inequality. It must assign candidate
resources to collision labels by contour interval or nested-shore ownership and
prove Hall inequalities for every subfamily. Its geometry must explicitly
handle bare attachment branches, likely by transporting their debt to another
interval, another side, or a later contour return.

Before formalization, a candidate relation must satisfy:

1. Every collision has at least one geometrically defined candidate resource.
2. Candidate ownership is stable under merged contour suffixes.
3. A resource belongs to only a controlled set of collision neighborhoods.
4. Hall's inequality is proved locally, not inferred from the total primal
   contour cardinality.
5. Bare branches receive an explicit nonlocal discharge rule.

Without such a relation, the expanded contour remains an exact and useful
normal form for the open inequality, but not its proof.
