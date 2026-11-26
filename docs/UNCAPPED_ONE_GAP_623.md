# No one-gap equality at side 623

**The normalized one-gap chart is empty on both axes, with no bound on
connections per cut.** In particular deficit 1,062 is impossible. This
test does not even impose the deficit constraint. It uses `k=207` tile
columns and rows, with all `1≤q≤205` north-isolate positions covered
(distance `2+3q`). It does not apply the one-gap tooth condition to the
distinct two-gap bridge.

The [side-623 proof ledger](EXCEPTIONAL_623.md) treats those bridges
separately and obtains the exact square optimum.

## Coupling

Start each physical tile plaquette with its certified mask quadruples
for the chart, axis and isolate offset. In an isolate interval use the
**union** of all physically applicable offset tables at that location;
different locations may initially choose different offsets. This
relaxes, rather than freezes, the common isolate. The initial domains
do not pin the rim masks or row/column accounts of the earlier
[numerical controls](UNCAPPED_SEAM_TARIFF.md).

In a vertical band of three consecutive tile columns, the two adjacent
cut tests see exactly the same middle tile column, at every physical
row. Run **one forest on all nine sites of the band frontier**. Its
partition is updated across both seams; it is not a pair of separate
partitions with coincident class counts. Force every grid edge incident
to a mark. Attach each marked crop tooth to a common root so that
joining two teeth or closing a physical cycle is rejected. A marked
component that disappears must already have a tooth or have touched
an open transverse edge of the band (so that it might still root
outside). Treat the two real ends of the band as physical boundaries,
not open sides. Use the same test on horizontal bands. The sweep
width is a *spatial band width*, not a limit on traffic along a cut;
there is no port list, traffic counter, or charge truncation.

Keep a mask quadruple in a plaquette only if some complete feasible
path through the current band uses it at that location. Project these
supports back onto the single **physical** array of plaquette domains,
so the next band must use the updated possibilities on its overlaps.
A real board restricts to a feasible strip path in *every* step;
inductively none of its quadruples can be deleted. Thus one empty
band is sufficient for exclusion. Conversely, merely reaching local
consistency would not construct a board.

The replay alternates the directions and scan order with width two,
for at most 40 passes, and then uses width three. It does not require
a fixed point before increasing the width. The following covers
gave an empty vertical three-column strip during the first width-three
pass. Starts are zero-based.

| axis | permitted `q` (inclusive) | start |
|---|---|---:|
| 1 | 1–103 | 191 |
| 1 | 104–154 | 188 |
| 1 | 155–205 | 204 |
| 2 | 1–205 | 161 |

The starts identify where the propagated contradiction became visible,
not standalone three-column exclusions with all surrounding cuts free.

## Verification

The Rust solver keeps forward-reachable stripe partitions and traces
co-reachability backwards through the same transitions. An independent
Python checker computes two **physical half-forests** from opposite
ends. At a proposed meeting it unites their root nodes, inserts each
forced crossing edge between corresponding sites and tests the resulting
component flags. It reproduced all four empty strips, including the
indices. The implementations share the certified catalogue input.

As a positive control the solver accepted the masks of a physically
replayed side-623 rooted region padded on the west by empty tiles.
Padding only adds unmarked leaves; this control has **eleven** hops
on one cut. Its fixed mask domains test forest acceptance, not equality.
A globally consistent mask line connecting two teeth was rejected.
All transfer tables are computed in memory.

```
export PYTHONPATH=target/pb-python
python3 -B -m analysis.research_program.coupled_mask_audit
for range in 1:103 104:154 155:205; do
  python3 -B -m analysis.research_program.coupled_mask_check 1 207 "$range"
done
python3 -B -m analysis.research_program.coupled_mask_check 2 207 1:205
```
