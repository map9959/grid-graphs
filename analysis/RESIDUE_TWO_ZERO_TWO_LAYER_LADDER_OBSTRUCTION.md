# Two-Layer Residue-Zero Terminal Ladder

## Declared Grammar

Put `m=3k` and `n=m+2`.  Delete the old residue-zero bottom cap and retain the
remaining forced forest.  A stable packet has seven declared sites:

```text
three cells on the outer bottom rail,
three cells on the outer right rail,
one singleton rung in the deleted old bottom row.
```

The terminal `2 x 2` corner contributes one forced cap vertex.  Consequently a
packet word of gain `g` gives replacement count `gk+1`; the required `7k+1`
count forces `g=7`.

The finite grammar contains:

```text
4 orientations
x 8 bottom masks
x 8 right masks
x 4 rung states (none or one of three offsets)
x 4 singleton cap masks
= 4096 descriptors.
```

This is a hard bound, not a search cutoff.  Exact gain seven saturates all
packet sites, so only 48 descriptors remain: both rail masks are `111`, one of
three rung offsets is selected, and one of four cap masks is selected in each
orientation.

## Local Success

Every exact descriptor at `k=7,8,9` has the target forced count.  All its unit
cells are valid, all forced components are straight, and the count interface
gains exactly seven vertices per three-column successor packet.

## Global Obstruction

The saturated right mask concatenates to a vertical outer rail of length `3k`.
The retained residue-zero forest still contains its rightmost vertical
interval.  Their forced-star supports overlap at every interior parallel site:

```text
|support(outer right rail) intersect support(retained right interval)| = 3k-5.
```

Thus the pairwise intersection is not a singleton.  Since the retained support
is already connected through its rooted component, the parallel rail closes
cycles.  No rung offset, corner cap, transpose, or reflected orientation can
change this intersection.

The best exact materializations have forced cycle rank `3k-5`:

| `k` | `n` | exact descriptors | star intersection | minimum cycle rank |
|---:|---:|---:|---:|---:|
| 7 | 23 | 48 | 16 | 16 |
| 8 | 26 | 48 | 19 | 19 |
| 9 | 29 | 48 | 22 | 22 |

Hence all 144 requested materializations fail singleton star intersections,
tree incidence, and forced-forest acyclicity.  The obstruction is complete for
the declared seven-site two-layer packet grammar.

## Exact Next Topology

The next topology must exchange both parallel caps.  In addition to the old
bottom cap, delete the retained rightmost interval of length `3k-5`.  The
retained count then falls by another `3k-5`, so the replacement obligation is

```text
(7k+1) + (3k-5) = 10k-4,
```

with successor gain ten.

The corresponding non-affine packet has ten sites:

```text
three bottom-rail cells,
three right-rail cells,
one bottom rung,
one right rung,
two inner connectors separated from both rails by unforced pivots.
```

Deleting the old right interval removes the `3k-5` parallel attachment.  The
bottom and right rails can then be separate straight interval hubs, joined by
the two inner connector stars through singleton pivot intersections.  A fixed
base cap must account for the `-4` constant, while each successor appends one
ten-vertex packet and transports the incidence parents unchanged.
