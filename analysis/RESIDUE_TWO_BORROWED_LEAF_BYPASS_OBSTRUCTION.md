# Borrowed-Leaf Offset Bypass Obstruction

## Exact Grammar

For each of the five witness spine types and each immediate offset `y=+-1`, use:

```text
removed projected spine segment   k-5
full offset core                   k-5
carrier endpoint ray               k-5 added target correction
prescribed blocker translation       0 net
at most one second leaf translation   0 net.
```

The prescribed blocker must fill beta or gamma.  The second leaf, if present,
fills the other role.  Beta must meet carrier and core once and miss the far
spine; gamma must meet core and far spine once and miss the carrier.

No arbitrary affine leaf is considered.  A second source component must:

1. Be a leaf at `k=7,8,9`.
2. Have one constant length under the affine owner maps.
3. Have its `k=7` star meet a failed singleton connector window from the prior
   offset census.
4. Translate wholly into the same hard-capped local box as that census.
5. Have one common local target signature at all three widths.

Translations are exactly the differences between the old centers and a target
component satisfying the missing role equations.  There are no free vectors.

## Derived Second Leaves

The type-local source list contains six distinct transported chains:

```text
H:r2:c11                    length 1
V:c14:r2..3                 length 2
H:r2:c5                     length 1
V:c15:r5..6                 length 2
H:r8:c14                    length 1
H:r15:c17                   length 1
```

Coordinates shown are at `k=7`; the JSON records their `k=8,9` owners.  The
fourth root witness has no adjacent constant-size second leaf.  Depending on
type, each offset therefore has zero, one, or three second-leaf candidates.

## Complete Obstruction

The hard cap has

```text
5 witness types * 2 offsets * 2 blocker roles = 20 role attempts.
```

Across their 60 width-specific blocker-role checks:

```text
blocker overlaps intended geometry       24
blocker merges intended geometry         18
beta singleton equations fail             9
gamma singleton equations fail            9
valid prescribed blocker roles             0
```

Hence no second-leaf translation can form a transported borrowed pair and the
materialized-chain count is zero.

There is also an independent all-width obstruction.  In local coordinates the
carrier ray contains `(2,0)`.  A full immediate-offset core contains `(2,+1)`
or `(2,-1)` because `k-5>=2`.  These are adjacent centers, so the core merges
with the carrier in every one of the

```text
5 types * 2 offsets * 3 widths = 30
```

instances.  Therefore the declared straight component decomposition is
impossible even if connector ownership were repaired.

The checker implements complete materialization, exact target count, unit
cells, straight components, old-component transport, star acyclicity and
singleton intersections, incidence-tree edge count, forced forest, and
insertion nesting for any surviving borrowed signature.  No signature reaches
those gates because the prescribed blocker role is already impossible.

## Narrowed Next Topology

Exactly one topology remains: a **two-layer dogleg bypass**.

```text
full core local side       y=+-2
prescribed blocker         first short dogleg rung
one adjacent borrowed leaf second short dogleg rung
```

Moving the core from `|y|=1` to `|y|=2` removes the carrier-center adjacency.
The full core still replaces `k-5` spine centers one-for-one, and both leaf
translations remain zero-net, so the carrier retains the missing `+1` step.
No other offset distance or additional leaf is justified.
