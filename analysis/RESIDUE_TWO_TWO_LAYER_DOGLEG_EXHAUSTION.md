# Two-Layer Dogleg Bypass And Affine-Surgery Exhaustion

## Final Declared Grammar

This is the uniquely retained terminal topology.  For each of the five witness
spines and both sides:

```text
full core side      y=-2 or y=+2
rung line           y=-1 or y=+1, respectively
removed spine       k-5 centers
full core           k-5 centers
carrier ray         k-5 target-correction centers
borrowed leaves     prescribed blocker plus at most one adjacent leaf.
```

The prescribed blocker translation is unchanged from its original endpoint
slide.  It must fill beta or gamma on the rung line.  The second leaf must be
one of the constant-size transported leaves already derived from the failed
connector windows; no new source leaf is admitted.  Its translations are
exactly those placing the whole component on the rung line while satisfying the
other role's singleton-owner equations.

The declared path is

```text
carrier -- beta -- full core -- gamma -- far spine.
```

All old components outside the blocker, second leaf, and split spine must
transport unchanged.  There are no other edits.

## Hard Cap

```text
witness spine types       5
dogleg sides              2
blocker roles             2
role attempts            20
width checks             60
```

The adjacent second-leaf source list remains:

```text
H:r2:c11                 length 1
V:c14:r2..3              length 2
H:r2:c5                  length 1
V:c15:r5..6              length 2
H:r8:c14                 length 1
H:r15:c17                length 1
```

One witness has no adjacent source leaf.  Coordinates shown are at `k=7`; all
transported names are exported.

## Complete Obstruction

The 60 prescribed-blocker checks terminate as follows:

```text
overlaps intended carrier/core/spine geometry       26
merges with intended geometry                       16
beta singleton-owner equations fail                  9
gamma singleton-owner equations fail                 8
owner equations hold but blocker is off rung line    1
valid transported blocker role                       0
```

For the 20 complete role assignments, the first failing width/reason is:

```text
overlap failure       10
beta equation failure  5
gamma equation failure 5
```

Thus the prescribed blocker never occupies either dogleg rung role through all
of `k=7,8,9`.  No second-leaf target translation is consequently legal and the
materialized chain count is zero.

The checker contains the complete downstream validator for any admitted chain:
exact target count, unit cells, straight declared components, injective
component transport, interval-star acyclicity, singleton intersections,
connected incidence tree with `nodes-1` edges, forced forest, and insertion
nesting.  These gates are not reached because the mandatory first rung does not
exist.

Every result replays by regenerating the exact tuple

```text
(witness type, dogleg side, blocker role, k),
```

and any materialized choice would additionally include the transported second
leaf and its local rung signature.

## Line Status

The witness-derived affine-surgery line is exhausted:

```text
counter component
existing endpoint extension
one-leaf endpoint slide
two-leaf hinge
nonleaf spine split
immediate offset connectors
borrowed-leaf immediate offset
two-layer borrowed-leaf dogleg
```

Each stage has a complete declared grammar and replay artifact, and the final
dogleg has no connector interface.  No arbitrary next edit, farther offset,
third leaf, or wider search is justified.  The next lower construction must
begin from a different abstract incidence topology rather than another repair
of the affine root/spine skeleton.
