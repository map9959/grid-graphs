# Exact Residue-Zero Double-Cap Exchange

## Counts

Let `m=3k`, `n=m+2`.  Delete both:

```text
bottom cap:             {(m-1,c) : c != 1},       size 3k-1,
right retained interval:{(r,m-1) : 2 <= r < m-3}, size 3k-5.
```

The retained forced count is `3k^2-3k+4`, so the replacement obligation is

```text
(3k^2+7k) - (3k^2-3k+4) = 10k-4.
```

Use `k-2` repeated interior packets and a sixteen-vertex terminal cap:

```text
10(k-2)+16 = 10k-4.
```

## Declared Packet Grammar

Each interior packet has ten sites:

```text
three outer-bottom rail cells,
three outer-right rail cells,
two distinct positions in the deleted bottom-cap layer,
two distinct positions in the deleted right-interval layer.
```

The two positions on each inner arm are named rung and connector.  The new
inner row or column between them and the outer rail remains unforced, so all
attachments cross an unforced pivot.

The packets occupy coordinates `2..3k-5` on both arms. The cap supplies the
six omitted outer-rail coordinates, three remaining deleted-cap coordinates,
and one of four terminal `2 x 2` corner choices. Each cap has sixteen vertices.

The raw hard bound is

```text
4 orientations x (8 x 8 x 4^4) packet descriptors x 4 cap masks
= 262,144.
```

No raw enumeration is performed.  For `k>=7`, the equation

```text
(k-2)g + c = 10k-4,   g<=10, c<=16
```

forces `g=10`, `c=16` in the declared cap family. Thus both rail masks are
`111`, all four auxiliary sites are present, and each pair of auxiliary offsets
is distinct. This leaves the exact finite set

```text
4 x (3*2) x (3*2) x 4 = 576 descriptors.
```

## Complete Obstruction

Every exact descriptor has the required replacement and target counts.  At
each checked width, all 576 descriptors also pass all unit-cell checks and have
only straight forced components.

However, selecting two of every three positions periodically on an arm always
creates an adjacent pair: masks `110` and `011` contain one internally, while
`101` creates one across the packet boundary.  That adjacent inner interval
is parallel to the saturated outer rail, separated by the unforced pivot
layer.  Their forced-star supports intersect at both interval positions.

Therefore every locally valid descriptor has maximum pairwise star
intersection at least two.  None has singleton intersections, tree incidence,
or a forced forest. The best forced cycle rank is `4k-8`.

| `k` | `n` | exact descriptors | locally valid | min intersection | min cycle rank |
|---:|---:|---:|---:|---:|---:|
| 7 | 23 | 576 | 576 | 2 | 20 |
| 8 | 26 | 576 | 576 | 2 | 24 |
| 9 | 29 | 576 | 576 | 2 | 28 |

The successor count interface is exact `+10`, but no stable incidence-parent
interface exists in this grammar.

## Exact Next Topology

The next topology must have packet capacity strictly above ten, so exact gain
ten does not saturate both rails and both inner arms.  The minimal extension is
a phase-alternating twelve-site sparse-rail ladder:

```text
the same ten sites,
one additional pivot-separated reservoir leaf on each arm,
select ten of the twelve sites per packet.
```

Omit one site from each outer rail and replace those two counts with the two
reservoir leaves.  Move the rail gaps through the three packet phases so no
parallel rail component spans consecutive packets.  The inner auxiliary masks
must use the complementary phase, leaving all inner components singleton.
This retains successor gain ten while making singleton star intersections
topologically possible.
