# A synchronized exclusion on the exceptional square progression

For `n=623+42s`, `k=(n-2)/3`, equality with one north isolate at
`d=5,11,...,71` is impossible. This finishes axis 2, by the
[folded strip cover](FOLDED_STRIP_ENLARGEMENTS.md). Axis 1 at larger
indices is a separate problem.

**Seed.** For each odd `q=1,3,...,23`, fold the square to width 81.
On axis 1 expand fourteen-bond blocks at `(48,8)`; every retained deep
tile (depth at least four) also satisfies the axis-2 restriction
`not (m&16 and m&40)`. Thus an axis-1 witness here would also be an
axis-2 witness. On axis 2 expand bonds `(62,62)`. Take the union over
the twelve isolates of the four plaquette rows starting at row 28.
From column 24 east the top tile row has mask 6, followed by mask 7
through row 28: each of these straight lines reaches a distinct north
tooth. Inserted columns have this property too.

**Induction.** The invariant at row `28+4j` has an 81-column template
with `3j` extra columns at bond 8 and `k-81-3j` at bond 62. Its four
plaquette rows have the stored domains, and the suffix starting at
physical column `24+3j` reaches the north teeth. To transfer, first
unfold three columns at the eastern bond and scan a width-84 slab;
the remaining padding stays at bonds 8 and 65. Both cropped ends in
the vertical direction may leak. Contract the known north connections
to the common perimeter, once per suffix line. The transverse strips
use full physical masks and forest partitions. The resulting four-row
handoff still consists entirely of mask 7 east of the shifted front.
Fold the three columns back at the *western* bond; union the output
domains into the input template. After 28 and then 5 changed entries
the third pass adds none. This is an inductive superset of physical
fillings: no agreement of independently chosen accepting paths is
needed for the exclusion.

**Larger isolates on axis 1.** For `25≤q≤55` the axis-2 restriction
need not hold in the north fan. With the interval union at width 81,
fourteen-bond blocks at `(60,48)` verify it on every deep tile from
row 28 down. Seed the same induction from the axis-1 domains with
single-bond cuts `(60,60)` and use the axis-2 catalogue only in the
slabs. With rooted suffix starting at column 56, both implementations
reach a closed template and reject all four terminal heights.

**Parity beyond this interval.** Every even `q≥58` is also excluded,
by a separate induction near the north boundary. In row `y` the fan
has the following forced tile word:

```
448^a  384 264 24  56^c  24 12 6  7^r
a=3y-2,  c=q-6y-2,  r=k-a-c-6
```

Seed rows 7 and 8 at width 81. If `k-q≥25`, use base isolate 56 and
insert `q-56` tiles at 28 and `k-q-25` at 68. Otherwise use base
isolate `81-(k-q)` with only a western insertion; its index is even,
between 58 and 78. Insert the extra height at 60. Both seed rows
are forced throughout these insertions. The step template has
`(a,c,r)=(16,20,16)` and arbitrary extra columns in all three runs.
With **only** its first two rows imposed, the width-three strip check
forces the next fan row, transferring `(3,-6,3)` to the lengths.
All three expandable positions stay strictly within constant runs
of all three rows. This propagates until `c=14,16,18`; for each case
a 13-row rectangle with open north/south ends is empty, allowing
arbitrary outer padding. No score constraint or artificial roots
are used. Together with the earlier even-index cover, only **odd
`q≥57` on axis 1** remain for `k≥207`.

**Terminal.** Choose `j=floor((k-48)/4)`. Exactly 20–23 rows remain,
and both pads stay nonnegative up to this step for `k≥207`. With the
actual southern teeth restored, all four terminal rectangles are empty.
Rust forward transitions and Python opposite-half joins agree. Lean
checks the common-square arithmetic and induction implication; the
domain computations are external exhaustive checks.

**Side 665.** On axis 1 the previous even-index cover includes `q=24`;
the remaining intervals `25..109`, `110..163`, `164..219` have empty
vertical strips at starts `203,203,218`. Two gaps are already excluded.
The physical rail has 442224 edges and scores 148039, one below the
unrestricted upper bound. Thus `P(665,665)=148039`.

```
PYTHONPATH=target/pb-python python3 -B -u -m analysis.research_program.distance_five_sync
PYTHONPATH=target/pb-python python3 -B -u -m analysis.research_program.middle_isolate_sync
PYTHONPATH=target/pb-python python3 -B -u -m analysis.research_program.north_fan_sync
PYTHONPATH=target/pb-python python3 -B -u -m analysis.research_program.side665_front_ledger
(cd lean && lake env lean GridGraphs/Geometry/SynchronousFront.lean)
```
