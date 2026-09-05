# Affine Endpoint-Extension Obstruction

## Declared L2-L3 Alternative

The affine score is `3k^2+6k+5`, short of the target by `k-5`.  Therefore a
single existing affine interval would have the exact target score if one of its
endpoints were extended through the `k-5` consecutive collinear cells beyond
that endpoint:

```text
(3k^2+6k+5) + (k-5) = 3k^2+7k.
```

Under `k -> k+1`, this extension changes length from `k-5` to `k-4`, so it
contributes exactly one beyond the affine gain:

```text
(6k+9) + ((k-4)-(k-5)) = 6k+10.
```

No component is introduced.  If its incidence edges were unchanged, the
audited affine parent map and leaf elimination would transport verbatim.

## Finite Endpoint Types

At `k=7`, the affine tree has `4k=28` intervals and exactly `56` oriented
endpoint types `(interval,start/end)`.  The audited old-node owner maps transport
each interval through `7->8->9`; the endpoint side is retained.  These are all
possible stable types beginning at `k=7`.  Intervals first introduced at `k=8`
or `k=9` cannot define the required three-width family and are not extra source
types.

For completeness, the checker also classifies both endpoints of every affine
interval independently at each width:

```text
k=7: 56 endpoints
k=8: 64 endpoints
k=9: 72 endpoints
```

There are no placement choices, deletions, or compensating edits.  A replay key
is exactly `(k, component id, side)`.

## Complete Obstruction

```text
k=7
  ray out of grid                         4
  ray contains an old preserved vertex  22
  forbidden unit cell                   25
  affine component merge                 5

k=8
  ray out of grid                        18
  ray contains an old preserved vertex  27
  forbidden unit cell                   19

k=9
  ray out of grid                        21
  ray contains an old preserved vertex  41
  forbidden unit cell                   10
```

Thus every independently eligible empty ray at `k=8` and `k=9` already creates
three preserved vertices or a preserved diagonal pair in a unit cell.  At
`k=7`, five rays pass that local gate, but every one joins its carrier to a
neighboring affine component.  None reaches an unchanged parent tree or forced
forest, and none of the `56` transported endpoint chains survives all widths.

The checker nevertheless implements all later gates: exact target count,
straight components, injective old-component transport, acyclic interval stars,
singleton pairwise intersections, equality with the affine incidence edge set,
and global forced-forest completion.

## Narrowed Next Topology

The obstruction identifies the missing operation: an endpoint cannot advance
unless a neighboring component moves.  The next L2 object should be a
**two-interval endpoint-slide**:

```text
carrier endpoint extension     +1 per step
blocking leaf translation       0 (one delete, one add)
declared leaf reattachment       0
net correction                  +1 per step.
```

The blocker must be a constant-size leaf so its translation has a stable
interface.  Its old singleton attachment is deleted, its centers are translated
without changing cardinality, and one new singleton attachment reparents it
after the carrier endpoint advances.  This is the narrow topology to specify
symbolically before any further coordinate census; the endpoint grammar should
not be widened independently.
