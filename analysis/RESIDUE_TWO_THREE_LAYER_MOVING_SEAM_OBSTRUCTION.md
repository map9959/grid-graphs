# Three-Layer Moving-Seam Obstruction

## Algebra Before Enumeration

Put `m=3k` and `n=m+2`. Delete the residue-zero bottom cap and right retained
interval, exactly as in the exhausted double-cap branch. The retained count is

```text
3k^2-3k+4.
```

The target `3k^2+7k` therefore requires `10k-4` replacement vertices. Retain
the existing sixteen-vertex terminal cap and use `k-2` interior packets. The
packet gain is forced before any phase word is enumerated:

```text
g(k-2)+16 = 10k-4,
g = 10,
10(k-2)+16 = 10k-4.
```

## Compact Phase Grammar

Each three-column packet has two arms. An arm has three outer-rail sites and
three sites on each of three inner tracks, hence twelve available sites. It
selects five:

```text
two outer sites, omitting the moving seam,
one site on inner track 0,
one site on inner track 1,
one site on inner track 2.
```

Thus the two-arm packet has capacity 24 and gain 10. For one arm, declare

```text
s(t) = p + d*t mod 3,
p in Z/3,
d in {-1,+1},
inner offset j = s(t) + q_j mod 3,
(q_0,q_1,q_2) in (Z/3)^3.
```

The three independent `q_j` values are the collision phase shifts. There are
`3*2*3^3=162` arm words. With independent bottom and right words and four cap
masks, the hard bound is

```text
162^2 * 4 = 104,976 descriptors.
```

The monotone unit-cell gate is arm-local. It leaves 39 words on each arm at
every requested width; all 39 also have straight components. Thus only
`39^2*4=6,084` joint materializations require incidence computation. This is a
factorized exhaustive classification, not a search cutoff.

## Deterministic Census

| `k` | `n` | descriptors | joint checks | locally valid | min star intersection | min cycle rank | survivors |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 7 | 23 | 104,976 | 6,084 | 4,624 | 2 | 40 | 0 |
| 8 | 26 | 104,976 | 6,084 | 4,624 | 2 | 48 | 0 |
| 9 | 29 | 104,976 | 6,084 | 4,624 | 2 | 55 | 0 |

Every locally valid descriptor has the exact target count, straight preserved
components, and the stable ten-vertex recurrence. None has singleton star
intersections, an incidence tree, or an acyclic forced graph.

## Exact Obstruction

The third inner track raises packet capacity from 12 to 24, so count saturation
is no longer the obstruction. Exact gain ten still requires three inner sites
per arm per packet. Straightness and unit-cell validity reduce each arm to the
39 phase words above. Across this complete admissible set, at least one pair of
parallel or diagonal interval components has two common star-support vertices.
The best possible maximum pairwise intersection is exactly two at all three
widths. Phase shifts can move this double attachment between track pairs, but
cannot turn it into a singleton.

Consequently the incidence graph cannot be the required singleton-edge tree,
and the forced graph has positive cycle rank. The three-layer relaxation has
removed the earlier capacity and multiplicity-three failures but not the
double-attachment obstruction.

## Branch Assessment

No candidate survives this genuine three-inner-track moving-seam grammar. A
further bounded boundary-track enlargement is not justified: the available
capacity already exceeds the required gain by 14 sites per packet. Progress now
requires a wholly new base construction whose interior incidence parents move,
or a different deletion that removes the old parallel carriers, rather than
another cap or boundary-track phase refinement.
