# Side 103: exclusion of the entire no-pitch `F=43` floor

A 3647-mark no-pitch forest at `F=43` is impossible. Here `F`
counts marks outside the union of the pitch rows and pitch columns.
This is a conditional exclusion, **not** an unrestricted 103-square
upper of 3646. It uses the [floor conditions](SKELETON_CROSS_RANK.md)
`C=A=1`, `j=X=0`. It does not exclude `F>43` with `F-j=43`.

### Partition and direct tests

The [integral model](INTEGRAL_RANK_FLOOR.md) gives `50≤T≤72` and no
four-way junction. Its straight-segment incidence graph is a tree with
`T` edges, so the exact segment count is `S=T+1`, from 51 through 73.
After transposition every column has a vertical edge. Count one per
active horizontal row and one per noninitial segment start in either
direction. This counts exactly `S-35`. The sweep fixes both sides of
the unary threshold and retains the verified 13-row lower bound.

With 12 seconds per branch, direct integral SAT gave 23 `UNKNOWN`s.
In the endpoint test, separate the `T` charged blank joins from
the physical budget `B+U+H≤78`. Each mixed junction has exactly
one realized direction along which it lacks its owned stub; charge
the blank midpoint on that path. Subtract one mandatory vacancy at
each corner by billing only the *second* vacancy in that pair of
corner neighbors. The remaining budget is `74-T=75-S`. Encoding it
directly yielded `UNSAT, s VERIFIED` at `S=73`; at `S=72` the
40-second test was `UNKNOWN`. The exclusion below does not rely on
a time limit.

### Joint corner price

Use the previous sector chart with both line languages, the
no-cheap-cut inequalities, wired `4×4` faces and the incident-edge
lift. At each corner of a coarse face record the five bits

```
(junction mark, inward horizontal stub mark, inward vertical stub mark,
 horizontal coarse edge realized, vertical coarse edge realized).
```

Measure the last two bits **jointly** in two ways: (1) read the face
marks and check the three consecutive bonds on each side; (2) read the
junction star and its two inward bits in the coarse-tree incidence
mask. For every face location type and corner offset the resulting
histograms must agree. The four readings at an interior junction refer
to different faces; transform masks as well as coordinates under all
eight square symmetries. `segment_face_audit.py` checks for every
physical coordinate that a fine junction label determines exactly
the required list of clipped face labels. It checks 118,656
transformed paths on admissible face masks. It also constructs orbit
frequencies independently by rotating a physical 103-square tree with
3638 marks and checks all 612 new equalities directly. This calibration
does not require that the test tree be a no-pitch maximum.

In fact **one projection** of these equations suffices. Count corner
occurrences with a vacant junction, a marked horizontal inward stub,
and an unrealized horizontal edge. On the face this is exactly the
four-site word `.#..` read starting at the junction. On the junction
side it uses the same two starting marks but reads absence from the
incidence mask. Sum over locations, corner offsets and values of both
vertical bits. `segment_face_turns.py` appends just that one equality
and maximizes **marks** without choosing any particular segment
placement, direction histogram or coarse tree. Replay checks dual signs and every variable coefficient
over the integers. All quantities for a physical input can be chosen
as counts or averages of counts, each at most `103²`. With scale
`10¹²`, charging every positive residual at this upper bound costs
`160259554` integer units. **Including** this allowance the result is

```
3646644258657743 / 10¹² = 3646.644258657743 < 3647.
```

The dual file is `analysis/research_program/segment_face_floor_103_dual.json`.
Some old chart rows assume an above-comb maximum, so the assertion is
that no candidate of score 3647 exists in this stratum, not that this
real upper applies to arbitrary lower-scoring forests.

### DRAT bridge for every exact count

Keep the same dual and temporarily omit the single aggregated
equation. Its right side is zero. The signed sum of the old
constraints, including the residual allowance, then shows that at
score 3647

```
270935416585 * (face_count - incident_count)
  ≥ 3647 * 10¹² - 3646644258657743 = 355741342257 > 0.
```

Thus some corner in the symmetry average must have a strictly
higher face price than junction price. The mark readings are shared,
so a face reports a failed path but the junction reports that edge
present. The vertical bit does not enter this price. One differing
bit is necessary but need not suffice to pay the whole deficit.

`segment_discrepancy_proof.py` constructs the disjunction of those
possibilities from the dual. Its CNF does **not** assume the new
marginal equalities. It reads the face bit from marks and the junction
bit from parent departures. Each compulsory bond has one orientation,
midpoints have at most one outgoing bond, and a junction departure
continues to the next junction. If neither endpoint departs onto a
fully forced path, its two end bonds use both midpoints' outgoing
slots, leaving no direction for the middle bond. Conversely a
departure forces all three bonds. The DRAT additions derive these
implications and eliminate the possible signed discrepancies. A
binary count of maximal segment starts fixes the tested branch.
**All 23 discrepancy CNFs passed `drat-trim`**. This is a hybrid
certificate: the necessary disjunction comes from the rational dual;
DRAT checks its incompatibility with actual marked paths. It is not
a standalone DRAT refutation of the original unrestricted square.

```
python3 -B -m analysis.research_program.segment_face_turns
python3 -B -m analysis.research_program.segment_face_audit
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.segment_discrepancy_proof
(cd lean && lake env lean GridGraphs/Geometry/PitchSkeletonPrice.lean)
```

Regenerate the direct SAT experiments with `PYTHONPATH=target/pb-python
python3 -B -m analysis.research_program.floor_segment_sweep --seconds 12`,
or `--surplus --lo 72 --hi 73 --seconds 40` for the endpoint. Scratch
CNFs and DRAT traces are not stored.
