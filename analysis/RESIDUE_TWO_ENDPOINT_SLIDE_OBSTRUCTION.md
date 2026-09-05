# Two-Interval Endpoint-Slide Obstruction

## Grammar Derivation

The endpoint-extension census determines blockers without a neighborhood
search.  For each oriented affine endpoint at `k=7`, its blocker candidates are:

```text
occupied ray:    components containing a ray vertex
forbidden cell:  non-carrier components contributing old vertices to that cell
component merge: non-carrier components adjacent to the ray
```

Only candidates that are leaves in the audited rooted tree at `k=7,8,9` and
have one constant length under both affine owner maps are retained.  This gives
exactly `20` carrier/blocker pairs.  Every blocker has length one or two.

For each pair, the grammar translates the complete blocker by exactly one of

```text
(-1,0), (0,-1), (0,1), (1,0).
```

The carrier receives its `k-5` endpoint ray.  There are no other additions or
deletions, so the hard-capped grammar has exactly `20*4=80` chains.

## Required Geometry

At each width the candidate is

```text
(affine preserved centers - blocker) union translated(blocker) union carrier ray.
```

The checker requires:

1. Preserved count `3k^2+7k`.
2. No forbidden unit cell.
3. Every component straight.
4. The translated blocker is an exact component.
5. Every other affine component transports injectively.
6. Every interval-star is acyclic and every pair intersects at most once.
7. Every incidence edge not involving the blocker is unchanged.
8. The blocker has degree one, its old attachment vertex is gone, and its new
   attachment is singleton.
9. The complete forced graph is a forest.
10. Carrier rays, translated blockers, and new parents transport through
    `7->8->9`.

## Complete Census

The first terminal status of the `80` chains is:

```text
forbidden unit cell                 55
wrong count from translated overlap 18
multiple star intersection           6
non-blocker parent tree changed       1
stable realization                    0
```

Every chain is also evaluated independently at every width:

```text
k=7: forbidden cell 55, overlap 18, multiple intersection 6,
     non-blocker parent change 1
k=8: forbidden cell 49, overlap 27, translated blocker merged 4
k=9: forbidden cell 24, overlap 56
```

Thus no individual width realizes the slide, and no coordinate chain survives.
The JSON stores every width evaluation.  Its replay key is
`(k, carrier, side, blocker, translation)`.

## Narrowed Next Topology

A single blocking leaf cannot move without colliding with another local
constraint.  The next symbolic topology is a **two-leaf hinge exchange**:

```text
carrier endpoint extension       +1 per step
rigid translation of blocker
  plus one adjacent hinge leaf    0
new singleton attachment          0
net correction                   +1 per step.
```

The hinge leaf must be derived from the terminal multiple-intersection or
non-blocker-parent witness; it is not an arbitrary second edit.  Before another
census, the symbolic operation must name the two transported leaves, their old
parent edges, the rigid translation, and the one replacement parent owner.
