# Two-Leaf Hinge Exchange Obstruction

## Witness-Derived Grammar

The source artifact has exactly six `multiple_star_intersection` witnesses and
one `nonblocker_parent_tree_changed` witness at `k=7`.  No other endpoint-slide
failure is admitted.

For a multiple intersection, the named hinge is the member of the offending
pair other than the carrier and blocker.  For the parent-change witness, hinge
candidates are endpoints of its changed non-blocker edges other than the carrier
and blocker.  A hinge is retained only if the affine owner maps transport it as
a leaf of one constant length through `k=7,8,9`.

Five witnesses are rejected symbolically before coordinate testing:

```text
four name the long horizontal root R_k as hinge,
one names the long vertical V:c(3k-2):r9..(3k-4) branch,
neither is a leaf.
```

Exactly two two-leaf types remain.  Each keeps the blocker translation already
fixed by its source witness; there are no new translation choices.

## Type A: Parent-Change Hinge

```text
carrier  V:c(3k-12):r4..(3k-1), extended at its start
blocker  H:r2:c(3k-13)..(3k-13), translated by (0,-1)
hinge    H:r2:c(3k-10)..(3k-10), translated by (0,-1)
```

Both leaves originally have parent

```text
R_k = H:r0:c2..(3k+1)
```

at `(1,3k-13)` and `(1,3k-10)`, respectively.

## Type B: Multiple-Intersection Hinge

```text
carrier  V:c(3k-9):r4..(3k-1), extended at its start
blocker  H:r2:c(3k-10)..(3k-10), translated by (0,-1)
hinge    V:c(3k-7):r2..3, translated by (0,-1)
```

Again both leaves have parent `R_k`, with old attachments `(1,3k-10)` and
`(1,3k-7)`.

The required replacement topology deletes both old root edges and requires

```text
blocker -- hinge -- gamma_k -- external parent,
```

where both displayed incidences are singleton physical owners and `gamma_k`
denotes the unique external attachment vertex.  All other affine parent edges
must remain unchanged.

## Complete Census

There are exactly two transported chains and one rigid translation per chain.

```text
                 Type A   Type B
k=7              forbidden unit cell
k=8              forbidden unit cell
k=9              target-count loss from overlap
stable survivor  no       no
```

The target count before overlap is exact:

```text
affine + carrier(k-5) - blocker - hinge
       + moved(blocker) + moved(hinge)
= 3k^2+7k.
```

At `k=9`, a moved leaf overlaps another preserved center or the carrier ray, so
the set union has fewer than `3k^2+7k` vertices.  At `k=7,8`, the exact union
already has a preserved diagonal pair or three preserved vertices in one cell.
No candidate reaches the replacement attachment or forced-forest gates.

The checker nevertheless implements exact count, unit cells, straightness,
exact moved components, injective component transport, acyclic stars, singleton
intersections, unchanged fixed parent edges, the internal hinge edge, unique
`gamma_k`, removal of both old attachments, forced forest, and insertion
stability.  Every evaluation replays from

```text
(k, carrier, side, blocker, hinge, rigid translation).
```

## Narrowed Next Topology

The excluded witnesses show that the needed hinge is not another leaf.  The
next symbolic operation is a **nonleaf-spine split bypass**:

```text
split the named root/vertical spine at the carrier projection,
relocate that removed segment as an equal-size perpendicular bypass,
translate the blocker leaf,
reconnect both spine pieces through declared singleton owners,
lengthen the carrier by one per step.
```

The relocation and blocker translation have net count zero; the carrier gives
the missing `+1`.  This topology must be specified before any further finite
coordinate grammar is attempted.
