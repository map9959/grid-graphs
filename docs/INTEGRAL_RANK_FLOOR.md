# Integral test of the first no-pitch stratum

On side 103 at `M=3647, F=43` the [junction ledger](SKELETON_CROSS_RANK.md)
requires a single coarse spanning tree with all three residual slacks
zero after the mandatory vacancy debit. There is now a restriction on
the **undirected incident edges at the same junction**, in addition to
the old outgoing-arrow tests. For actual realized coarse degrees `h,v`
on the two axes define `T=sum min(h,v)`. The certified range for this
stratum is **50 through 72** in this test. The subsequent
[joint face/segment exclusion](SEGMENT_FACE_EXCLUSION.md) rules out this entire stratum.

### Physical price

A junction owns marked midpoints on only one axis. At least `min(h,v)`
of its realized paths must consequently start through a blank midpoint.
That midpoint is between a marked junction and a marked far midpoint
(otherwise not all three bonds are forced). Distinct charges are distinct
blank joins in the physical forest, even after the off-skeleton marks
are added. Write `B` for all blank joins, `U` for isolates, `N` for
nontrivial components and `H` for vacant boundary incidences (corners
twice). Contracting marked runs gives `B=R-N`. Counting compulsory
edges gives `3M+R-(4n-H)=n²-U-N`. Thus

```
T ≤ B,       B+U+2N+H = n²+4n-3M.
```

For `n≥7`, `H≥5`: four different corner neighborhoods each need a
vacant neighbor to avoid diagonal marks; if these were the only holes,
no perimeter bond would be missing. Consequently every above-comb
`3k+1` forest satisfies `T≤3k-5-3 floor((3k-13)/10)`, in particular
`T≤73` at 103. This argument is independent of phase regularity and `F`.

At the first floor a junction between two realized horizontal edges
must own horizontal stubs. Otherwise its two H neighbors both point
inward and it is a one-site internal V gap in an H line. Zero gap
slack makes the junction vacant, whereas either realized edge would
require it marked. Once the axis is known, an unfilled predicted
slot on a realized edge would waste one first slack. Thus **both**
slots are marked; transpose for vertical edges. In particular a
four-way coarse branch is impossible. The maximal horizontal and
vertical segments of the tree then number `T+1`: their incidence
graph is a tree with one edge per junction using both axes.

### Exact bounds, not a rounding test

The [previous fractional certificate](ORTHOGONAL_CUT_RANK.md) had
57 measurable outgoing-direction totals. Keep those totals, but
allow an arbitrary profile of incoming edges at each of the 1225
actual junctions. Require one outgoing edge except at NW, a unit
profile distribution per vertex, and agreement of each directed
edge at both ends. Minimize `T`; even this relaxation has exact lower
bound **greater than 160** for those totals. A rational dual is
checked against all **36,448 profiles**. Therefore *no* decomposition
with those totals can realize the score, not just the previously
exhibited mixture. The twenty particular trees have turn costs
248 through 488.

For a candidate with **free** direction totals use a different lift.
Split each sector junction star by the actual subset of its four
coarse edges used. An incident edge must be owned if the junction
is vacant or its assigned axis points along that edge. Pair the two
endpoint profiles by location, direction, junction marks and owned
slots. In each pair require the three bonds to be forced exactly
when the edge is used, consistent signs on the directed path, and
zero first slack. Couple the endpoint data to the mark triples at
**both** midpoints. The objective on the split stars is the physical
`min(h,v)`. Every actual forest supplies these frequencies by counting
and symmetry averaging. The lower and upper duals on 11,580 rows and
27,886 variables give respectively `T≥49.51546661381` and
`T≤72.10530780748`; round only after the rational residual check.
The residual allowance uses `x≤103²`: location sums, word transitions,
complete-line counts and all split frequencies of a physical board
can each be chosen within this bound. These duals do not assume the
old fractional arrow totals.

### SAT model and cut projection

`integral_rank_floor.py` has one Boolean mark per site. Orient every
compulsory edge exactly once with outdegree at most one. A sheet bit
flips on consecutive directed bonds crossing the direction cut
between directions 3 and 0. A simple directed grid cycle has odd
such parity (one full signed turn), so it is excluded. Conversely a
forest can be rooted and sheet-labeled along its paths. Force every
junction except NW to point along three successive bonds to another
junction. This enforces the actual common coarse tree. The line
clauses impose the zero slacks on the same marks in both directions.
Nonjunction pitch lines must miss a tooth: completing all teeth
without being pitch would join the already connected coarse tree.
We also impose the established **unrestricted** rim-gap bound of
seven, not the canonical six-gap bound.

`integral_floor_cross.py` shares *all* survivor marks with a compressed
square. Both seam edge sets use one spanning tree with actual grid
edge variables. Require it to contain the supported raw edges; its
restriction to raw edges must be maximal. To certify maximality,
propagate a common component ID along **every raw edge**; each sink
of the raw part of the oriented tree fixes its ID to its own vertex.
Following parent paths proves each ID is a connected class. The number
of raw rejected edges is therefore the true joint cycle rank. Owners of
those edges are paid only once. Refills are exactly the originally
unmarked vertices of full degree in this same tree. Projection is safe:
extend supported edges to a maximal raw forest, then to a spanning
tree. At 103 the attained net loss must be at least 79 by the exact
side-102 upper. No cheap cut is assumed to exist in the CNF.

The coupled board `(51,51)` exclusion for the union of all 20 pinned
coarse trees passed `drat-trim`. A broader 103 source exclusion
also passed `drat-trim`: **at most 12 coarse rows containing any
realized horizontal edge** is impossible. Everything about the
vertical edges and all individual row locations is free in this
test. Transposition gives the column counterpart. In any spanning
coarse tree a row with no horizontal edge forces some vertical edge
in every column, so at least one axis uses all 35 lines. The
unrestricted-within-floor solver runs were `UNKNOWN`, not exclusions.

### Replay

```
python3 -B -m analysis.research_program.coarse_turn_chart
python3 -B -m analysis.research_program.coarse_incident_lift
python3 -B -m analysis.research_program.coarse_incident_lift --upper
rustc -O analysis/research_program/skeleton_arborescence.rs -o target/skeleton_arborescence
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.integral_floor_check
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.integral_rank_floor 10 1 20 4 4
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.round_floor_mixture --union --cross
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.integral_rank_floor 103 43 60 --row-limit=12
```

The source-mask projections of the paired CNF on side four match all
eight physically eligible masks among all 65,536 tested. At side ten,
a SAT witness has 40 marks; its `(4,4)` compressed graph had cycle
rank one and its actual 80-edge spanning tree scored 33. Large CNFs
and proof traces are temporary; UNSAT is reported only after proof
verification.
