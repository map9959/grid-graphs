# Maximal bundle defects do not globalize by unit charging

## Setup

Let `G = G_n`, let `F` be inclusion-maximal subject to

```text
H = forcedEdgeGraph G F = G - E(G[U])
```

being acyclic, and put `U = V - F`.  For `u in U`, write

```text
k(u) = |N_G(u) intersect U|,
r(u) = number of distinct H-components met by N_G(u) intersect U,
       excluding the H-component of u,
beta(u) = bundleCycleDefect G F u = k(u) - r(u).
```

The exact loop/repetition formula in `BundleCycleDefect.lean` says that
`beta(u)` counts central-component loops plus excess multiplicity at every
other component label.

## What maximality gives

The proved Lean lemma

```lean
bundleCycleDefect_pos_of_maximalForcedAcyclic
```

gives, for every `u notin F`,

```text
1 <= beta(u) <= 3.
```

The upper bound is `bundleCycleDefect_le_three_of_not_forced`.  Summing the
lower bound gives the proved lemma

```lean
card_compl_le_sum_bundleCycleDefect_of_maximalForcedAcyclic
```

and hence

```text
|U| <= B := sum_(u in U) beta(u).                       (1)
```

This is an upper, not a lower, control on `|U|`.  Therefore an upper bound on
`B` alone cannot prove the required lower bound

```text
3|U| >= 2n^2 - 3n + 4.                                 (2)
```

An additional inequality in the opposite direction, involving the same global
resource and `|U|`, would be necessary.

## Exact global ledger

Let `e_U = |E(G[U])|`.  Summing
`beta(u) + r(u) = k(u)` and applying handshaking in `G[U]` gives

```text
B + R = 2e_U,             R := sum_(u in U) r(u).       (3)
```

Because `H` is a spanning forest and `G[U]` is exactly its edge complement,

```text
e_U = |E(G)| - |E(H)|
    = 2n(n-1) - (n^2-c_H)
    = n^2 - 2n + c_H.                                  (4)
```

Thus the complete scalar consequence is

```text
B + R = 2n^2 - 4n + 2c_H.                              (5)
```

Equation (5) is only another component ledger.  Maximality says `B >= |U|`,
which yields an upper bound on `R`; it does not yield (2).  Any successful use
of defects must prove a new lower bound on `R`, or a weighted inequality that
does not collapse to (5).

Lean-suitable statements for (3) and (4) are:

```lean
theorem sum_bundleCycleDefect_add_sum_graphicRank
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F U : Finset V) (hpart : U = Finset.univ \ F) :
    (sum u in U, bundleCycleDefect G (F : Set V) u) +
        (sum u in U, starAttachmentGraphicRank G (F : Set V) u) =
      2 * (G.induce (U : Set V)).edgeFinset.card

theorem square_induced_compl_edge_card_of_forced_acyclic
    {n : Nat} (F U : Finset (GridVertex n n))
    (hpart : U = Finset.univ \ F)
    (hacyc : (forcedEdgeGraph (gridGraph n n) (F : Set _)).IsAcyclic) :
    (gridGraph n n).induce (U : Set _).edgeFinset.card =
      n * n - 2 * n +
        Fintype.card (forcedEdgeGraph (gridGraph n n)
          (F : Set _)).ConnectedComponent
```

For robust natural-number formalization, the second statement should instead
be written additively:

```lean
inducedEdgeCard + n * n + 2 * n =
  2 * (n * n) + componentCard
```

after checking the desired normalization of `numEdges`.

## Counterexamples to unit-capacity resources

### Distinct faces or global cycles

In the maximal `2 x 2` pattern

```text
UU
FF
```

`H` is a spanning tree and `G[U]` consists of one edge.  Both `U` endpoints
have defect one.  The two local fundamental cycles are the same unique grid
face.  Therefore neither

```text
B <= number of bounded faces = (n-1)^2
```

nor an injection from owner-labelled defect units to global independent cycles
is possible.  Numerically, `B=2` and `(n-1)^2=1`.

The failure is structural: one physical `U-U` edge appears once in the bundle
at each endpoint.  The best owner-forgetting edge charge has capacity two, and
(3) immediately gives only

```text
B <= 2e_U.
```

This is sharp whenever every quotient edge is a loop.

### Distinct forest edges or branches

The maximal `4 x 4` pattern with `U` at

```text
(0,1), (0,2),
(1,1), (1,2),
(2,0), (2,1), (2,2), (2,3)
```

has one `H` component, `15` forest edges, `9` `U-U` edges, and

```text
B = 18 > 15 = |E(H)|.
```

All quotient edges are loops, so every omitted edge contributes at both
owners.  Hence no injection of all defect units into forest edges, rooted
forest branches, or deletion vertices with unit capacity can hold without an
extra congestion/saving term.  `SharedToothCapacity.lean` records exactly that
missing term as `endpointSaving`.

### Distinct boundary units

The same `4 x 4` pattern has only four boundary vertices in `U`, but `B=18`.
Even charging against all `4n-4=12` boundary positions fails.  Thus a boundary
charge must transport interior defects and must allow nonunit or inherited
component capacity; maximality supplies neither.

The maximal `5 x 5` pattern

```text
FFFFU
UUUUU
FUUUF
FUUUF
FUFUF
```

has `B=29`, `|E(H)|=23`, and only five boundary vertices in `U`.  This shows
the issue is not confined to the smallest square.

## Viable replacement target

The defect sum can still be useful if occurrences are retained rather than
charged immediately.  Define the owner-labelled occurrence set

```text
D = {(u,e) : u in U and e is one of the beta(u) nonbasis star labels}.
```

Then `|D|=B`.  Any genuine globalization needs a map from `D` to resources with
an explicit fiber penalty, for example

```text
B = |image(endpoint)| + endpointSaving
```

as already proved by `sharedEndpointDeletion_card_add_saving`.  To recover the
missing `n+2`, the new geometric lemma would have to control both terms in a
direction that implies

```text
boundaryDeficiencySum n n U + c(G[F]) + c(H) >= n + 4,
```

the exact component form of the universal bound.  Dropping `endpointSaving`,
identifying the two owners of one physical edge, or assigning unit capacity to
faces, branches, components, or boundary positions is disproved above.

A noncircular Lean-level target is therefore a bounded-fiber theorem, not an
injection:

```lean
structure GlobalBundleDefectRouting ... where
  occurrence : Finset Occurrence
  occurrence_card : occurrence.card =
    sum u in U, bundleCycleDefect G (F : Set _) u
  resource : Occurrence -> Resource
  -- A geometric inequality charging every nontrivial fiber explicitly.
  fiberDebtBound : ...
  -- The resulting arithmetic statement must imply the component target.
  closesComponentLedger : ... ->
    n + 4 <= boundaryDeficiencySum n n U + cF + cH
```

Without a concrete `fiberDebtBound`, the final field is merely the original
theorem restated.  The small maximal examples show that its fibers must permit
capacity at least two for faces and physical omitted edges, and unbounded reuse
for component labels.
