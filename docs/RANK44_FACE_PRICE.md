# No-pitch side 103: the second off-skeleton floor

At score 3647 the [physical ledger](SKELETON_CROSS_RANK.md) gives
`C+X=F-42`. Here `C` counts skeleton junction components including
isolated junctions, `j` counts actual joins of these components and
`X` is the total slack after the mandatory vacancies. At `F=44` the
following are all the possibilities. Each last entry is an exact
integer-scaled upper on the score of a **putative candidate** divided
by `10^12`, including all dual residuals.

| `C` | `j` | `X` | allowed (face mask, corner partition) states | conditional upper |
|---:|---:|---:|---:|---:|
|1|0|1|1854|3644.857149010587|
|2|0|0|7952|3641.250046984351|
|2|1|0|8812|3641.933350245657|

### Physical inequalities

Give each coarse corner its actual skeleton component label. In each
face insert the skeleton edges, identify corners of equal label, and
then add the edges forced by the four interior sites. Reject a cycle
or labels contradicted by a skeleton connection. Charge a face the
decrease in the number of its distinct corner classes on adding the
interior edges. These charges sum to at most `j`: the added edges in
different faces are disjoint, and, after contracting the skeleton,
two separate paths joining the same two classes would give a cycle.
Other joins may need several faces. Exactly 860 extra local states
can pay a join in the last branch. For the same perimeter and input
partition a strictly larger acyclic refill with a refining output port
partition dominates, since it introduces no cycle with the exterior.
Side words and same/different endpoint labels on an internal edge
are measured consistently from both sides. The global candidate gives
all these local data; the chart does not assert the converse.

**Line exception inequality (any length).** Assign empty-stub junctions
the V axis when reading horizontal lines. Then at most `X` horizontal
lines fail the zero-slack line language in `skeleton_floor_words.py`.
Indeed a wasted predicted slot on a realized edge or two missing
predictions on one failed edge costs that line a unit of the first
slack. A gap between H runs that is not a single vacant V with two
hits costs one of the undoubled gaps (third slack). Otherwise an unhit
vacant V in an H-active row costs an extra zero-hit vacancy (second
slack): it cannot be mandatory for a no-V column. In a no-H row,
all junctions are V and no horizontal hit is possible. At least one
is vacant by no pitch; each further vacancy costs an extra unit.
These witnesses on different rows are disjoint within each slack.
This gives an unrestricted word channel for at most one exceptional
row when `X=1`. The transpose follows by reading the transposed
board, assigning empty stubs afresh. No empty-stub ban is used.

**Coupling.** A line transition on consecutive junction letters
`(l,z,r)` and `(L,Z,R)` reads the word `(z,r,L,Z)` on the coarse
edge. Both adjacent faces, where present, read those very four marks
in that same order. Match counts by face location, top/bottom offset
and complete ordered word. Single-letter marginals do not impose this
law. With just partitioned face prices and the old cut constraints,
the numerical objectives were approximately 3648, 3647 and 3647.

### Verification

`rank44_faces.py` sets the old chart's off-skeleton mass to 44,
junction sinks to `C-j`, exits to `j`, and adds the above projections.
It checks signs and recomputes every reduced cost using integers,
bounding every positive residual at the physical count bound `103²`.
Line flows count physical transitions (or their symmetry average);
rank-face variables are orbit-normalized face counts. The three
`rank44_dual_*.json` files permit replay without a numerical solver.

```
python3 -B -m analysis.research_program.rank44_faces --replay
python3 -B -m analysis.research_program.rank44_audit
(cd lean && lake env lean GridGraphs/Geometry/PitchSkeletonPrice.lean)
```

The audit checked 10,436 no-pitch line controls, 148,944 labelled
face transforms, and all 18,496 face-side readings in a full-size
symmetry test. The exclusion uses rational inequalities, not a SAT
timeout or rounding of a fractional solution. Together with the
[previous floor](SEGMENT_FACE_EXCLUSION.md), any remaining no-pitch
3647 candidate needs `F≥45`. No restriction here eliminates pitch
candidates or increases the physically attained 3646.
