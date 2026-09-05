# Offset Spine Bypass Obstruction

## Exact Topology

Let `L=k-5`.  For each of the five nonleaf-spine witnesses, retain the projected
spine split and prescribed blocker translation.  Replace the failed crossing
bypass by:

```text
offset core length     L-2 = k-7
beta connector leaf             1
gamma connector leaf            1
total relocated centers         L.
```

Use local coordinates `(x,y)` at the far projected endpoint.  The `x` axis is
perpendicular from spine toward carrier, and `y` is parallel to the spine.  The
only offset-core choices are

```text
(x,+1), 1 <= x <= k-7
(x,-1), 1 <= x <= k-7.
```

Thus there are exactly two side attempts per witness and ten total.  At `k=7`
the core is empty.  The required parent path is

```text
carrier -- beta -- gamma -- far spine                  (k=7)
carrier -- beta -- core -- gamma -- far spine          (k=8,9).
```

Every edge displayed must have one singleton physical owner.  The old
carrier/near-spine owner is retained, every other affine edge transports to the
appropriate split piece, and the prescribed blocker translation must acquire
one new singleton parent owner.

## Hard-Capped Connector Derivation

Connector centers are not arbitrary edits.  They are enumerated only in the
local box

```text
-2 <= x <= 4,
-3 <= y <= 3,
```

adjacent to the failed bypass.  A beta center is retained only if its singleton
star meets the carrier and core exactly once and misses the far spine.  A gamma
center must meet core and far spine exactly once and miss the carrier.  With an
empty core, beta and gamma must instead meet each other exactly once.  Centers
adjacent to an intended component or each other are rejected because they would
merge components.

The same local `(beta,gamma)` signature must satisfy these equations at all
three widths.  This produces a finite, replayable owner-equation census before
any preserved-set materialization.

## Complete Obstruction

```text
source spine types             5
offset sides per type          2
owner-equation censuses       30
transported connector pairs   0
stable realizations           0
```

At `k=7`, the individual endpoint equations produce 56 ordered beta/gamma
pairs across the ten offsets.  Every pair fails because the empty-core topology
requires a beta-gamma singleton and none exists.

At `k=8`, where the core is one center, no beta or gamma center satisfies its
two required singleton-owner equations for any offset.

At `k=9`, an offset may admit a beta or a gamma candidate, but never both, so
there is again no connector pair.  Consequently no local signature transports
through `7->8->9`; the geometric candidate grammar is empty before target-count,
unit-cell, star, parent-tree, forest, or insertion checks.  Those later checks
remain implemented for any future surviving owner signature.

Each local census replays from

```text
(k, witness type index, offset side),
```

and records candidate counts, every ordered pair terminal status, first replay
signatures, and valid signatures.

## Narrowed Next Topology

Adding two connector centers and shortening the core destroys the attachment
interface at the small widths.  The one next topology is a
**borrowed-leaf offset bypass**:

```text
remove projected spine segment       k-5
add full offset core                  k-5
translate prescribed blocker leaf      0 net
translate one witness-named leaf        0 net
extend carrier                         +1 per step.
```

The two translated affine leaves, rather than new connector centers, must fill
the beta and gamma roles.  This preserves the complete relocation count while
allowing the connector interface to exist already at `k=7`.  The second leaf
must be derived from the failed owner equations before any further census.
