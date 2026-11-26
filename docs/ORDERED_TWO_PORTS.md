# Two ordered hops per vertical cut cannot attain the exceptional bound

Let `n=119+42t`, `k=39+14t`. In any one-gap upper witness in the
canonical north-isolate chart, **some cut between adjacent tile columns
has at least three forced mark-to-mark hops**. This holds on either
axis and for every isolate position. It is a maximum-congestion
constraint, complementary to the [sum of excess hops](NONPERIODIC_COMPONENT_DEBT.md).
The earlier sum allowed the excess to be spread over cuts with two hops.

## State and gluing

A hop is an adjacent marked pair, or two axial marks separated by
one unmarked site. Contraction to this graph preserves connectivity of
the marks and cycles in a candidate: diagonal marks would already
force a square cycle. Each hop crosses at most one vertical tile cut;
no two can cross that cut on the same physical row.

Scan a catalogued triple of columns from north to south. Retain shared
marks, the rooted partition on its physical forced edges, and the
actual components of the middle column. On each cut name its first and
second hops separately in north-to-south order. Record the physical
row modulo three and whether the edge is direct, skips the site west
of the cut, or skips the site east of it. Each local component retains
its distinct incident hop names and whether it has a perimeter tooth.
Discard cycles, components with two teeth, and marked components with
neither tooth nor exit. A toothless component reaching an open cut can
continue; reaching a cut does not root it.

In the west-to-east transfer the incoming partition is a tuple of class
labels for those ordered hops: zero is the common perimeter root;
equal positive labels are the *same* pending component. Insert each
incoming hop as an edge into the actual local component. Reject edges
which close a cycle and any still-unrooted class with no outgoing
hop. Record the outgoing partition and which outgoing class (or tooth)
inherits each old class. For example, attaching two ordered incoming
ends to the same new unrooted piece is legal for two distinct pending
trees; it is a cycle for two ends of one pending tree. A rooted end
cannot attach to a component already having its own tooth. The board
starts and ends with the empty cut.

Besides hop order, row phases and geometry, consecutive columns match
the two north and two south tile masks on the shared seam. The isolate
`(2,2+3q)`, `1<=q<=k-2`, is the same throughout the horizontal scan:
carry `q-i`, clipped to `[-4,5]`, and use its exact catalogue phase
where the isolate is visible. At `+5` allow waiting or entering `+4`;
after `-4` the halo is clean. All eligible distances are covered,
including the end fringes. The cited cached star catalogues are hash
checked against their verification records.

The column graph closes its homogeneous middle step under **any number
of extra longitudinal tiles**. For each endpoint and partition it
stores a minimum or maximum deficit and stops only at a verified fixed
point. In particular it does not identify old and inserted marks.
Matching ordered, phase-labelled hops does not require exact equality
of their absolute heights between different column witnesses. This
is a relaxation suitable for exclusions; an accepting walk is not
a tree construction.

## All lengths and the exact deficit

Compose seven western fringe columns, `25+14t` bulk columns, and seven
eastern fringe columns. Retain the bulk states reachable from the west
and from which the east can be finished after *some* number of steps.
Axis 1 has 395 reachable states and axis 2 has 212. **Only three on
either axis are coaccessible.** All are beyond the isolate, with
pending northern hop and rooted southern hop, and common rim word
`(6,6,192,192)`. Of all initial distance choices only `q=1` enters
this surviving cycle. With each hop encoded as `3*(row mod 3)+type`
(direct 0, west skip 1, east skip 2), the cycle is

```
(7,2) → (1,5) → (4,8) → (7,2)
```

These tuples are *geometries*, not component names. Every transition
costs exactly six. Min-plus and max-plus replays agree:

| `t` | relaxed terminal cost | required |
|---|---:|---:|
| 0 | 234 | 198 |
| 1 | no terminal state | 270 |
| 2 | no terminal state | 342 |

After 42 more bulk columns the live state vector has identical support
and every entry is larger by exactly 252, in both replays. Composition
proves this for all later lengths. In the supported congruence class
the relaxed cost is `234+84t=6k`, exceeding `198+72t` by `36+12t`.
In the other two classes there is no path. This argument does not sum
unrelated upper bounds and does not use an `UNKNOWN` as an exclusion.

## Keeping track of the actual heights and component identities

The drift check also compares the positions of the first (and second)
incoming and outgoing hops. For rank `j`, add, at each physical row,
the difference of the indicators that the `j`th west and east hops have
been seen. For two present hops the final sum is the east height minus
the west height. Clipping at ±8 preserves all values of magnitude less
than eight: each such counter moves only between the two event times,
and in just one direction. On every recurrent step both hops advance
**four physical rows south**. The old unrooted class really reaches a
tooth and a different one is born; the reappearance of the same
partition does not mean the same tree remains unrooted. For `t>=2`
the required advance `4*(25+14t)` already exceeds the available
`3k-1` edges in height. An independent marked-graph traversal of a
rooted region checks four consecutive two-hop bulk transitions and
the four recorded tooth payments.

One conclusion does not require a two-hop cap over the entire board:
if `12<=q<=k-12`, there must be a cut with at least three hops between
cut `q-6` and the east edge (cut `i` is east of column `i`). Start with
**any** incoming classes and traverse offsets `+5,...,-4` in bulk.
Only seven stationary profiles survive; their north pair is `(6,6)`,
south pair `(73,73)`, with one or two direct hops in row phase zero.
Every subsequent clean bulk transition is a self-edge, cost three,
with zero displacement. None of those states reaches the empty east
boundary through the final seven columns.

```
export PYTHONPATH=target/pb-python
python3 -B -m analysis.research_program.ordered_port_audit
for axis in 1 2; do
  python3 -B -m analysis.research_program.ordered_port_square "$axis" --min
  python3 -B -m analysis.research_program.ordered_port_square "$axis" --max
done
```

[`OrderedCutBound.lean`](../lean/GridGraphs/Geometry/OrderedCutBound.lean)
checks the induction arithmetic given the finite transfer facts and
the height bound. The graphs are computed in memory; there are no new
board-sized proof files. Three or more hops on a cut can introduce a
different partition and need not follow this cycle. Consequently this
does not yet exclude general one-gap equality.

## Extension to three ordered hops

For the same one-gap chart, **every equality witness must have four or
more hops on some cut**. Merely allowing a third hop does change which
closed paths exist, so the two-hop graph cannot be reused unchanged.

The three-hop transfer keeps six distinct local incidence bits (three
per side), the ordered prefix partition, and the same masks and phases
as above. It retains the accumulated deficit in the column state:
different prices for the same interface are never filled in by taking
an interval. Closure of the homogeneous length step must finish with
no new state **at any cost**. In the square transfer each interface then
stores a bitset of attained costs. An edge of deficit `c` shifts its
source bitset left by `c`; alternatives take the bitwise union. Zero
bits means no path. Absolute hop heights may still differ between
column witnesses, so these are spectra of a necessary relaxation.

Of 1,545 west-reachable bulk states on axis 1 (942 on axis 2), just
12 on each axis can reach the closed east boundary after some number
of bulk steps. Only `q=1` or `3` can enter from the west. Starting with
25 bulk columns, apply 14 more per increment of `t`. At `t=3` **the
whole vector** on those 12 states equals its `t=0` vector shifted left
by 252, with absent states still absent. Since both the bulk and east
operators commute with that shift, the following terminal spectra hold
for every `s>=0`:

| `t` | exact closed deficits in the relaxation | equality budget |
|---|---|---:|
| `3s` | `{234+252s}` | `198+216s` |
| `3s+1` | `{324+252s}` | `270+216s` |
| `3s+2` | empty | `342+216s` |

At side 623 (`t=12`) this leaves only deficit 1242 versus the required
1062. It does not bound a one-gap candidate containing a four-hop cut,
or a two-gap candidate. As an independent check on the new port,
explicit adjacency-list traversal agrees with the gluing routine on
all 36,450 combinations of a three-in/three-out incidence partition,
local tooth flags, and incoming partition, including the outgoing
identities of surviving classes. Lean's `three_port_gap` checks the
budget inequality given the finite spectra and shift.

```
export PYTHONPATH=target/pb-python
python3 -B -m analysis.research_program.three_port_glue_audit
python3 -B -m analysis.research_program.three_port_square 1
python3 -B -m analysis.research_program.three_port_square 2
```

At [four ordered ports](ORDERED_FOUR_PORTS.md) the equality price
survives in the relaxation.
