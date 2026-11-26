# Side 77: exact optimum 2047

`zipper_rails.build(77)` selects 2047 vertices, with 5927 forced edges,
two components, and 5928 edges after spanning-tree completion. The
unrestricted periodic dual upper is `28673/14 = 2048 + 1/14`.

A score-2048 forest must put all four corners in **one** component.
Otherwise one can root two distinct components at corners and average
over square symmetries. The weighted corner row improves the upper by
`9/14`, giving `14332/7 < 2048`. In fact all four corners must be marked:
an unmarked corner with zero marked neighbors is isolated, and with two
such neighbors its unit square cycles. With exactly one such neighbor,
choose that corner as a sink: its physical star slack is `3/28`,
already larger than `1/14`.

There is also only **one component containing any edge**. Any other
nontrivial component would contain a noncorner marked site. Root it at
that site while rooting the corners' component at the top-left. Exact
enumeration of the physical dual star slacks gives a minimum of `41/336`
for a noncorner marked sink, more than the entire available `1/14`.
Thus the other components, if any, must be isolated grid vertices.

In the explicit 2047-site construction the top-left component is
separated from the top-right and has **no vertex on row 16** in the
forced graph induced by the first 17 rows (indices start at zero).
Thus no changes in rows 17–76 can yield 2048 without changing the
prefix. This is a restricted exclusion; it makes no assumption about
the prefix of a general optimizer.

```
python3 -B -m analysis.research_program.cap53_prefix 77
python3 -B -m analysis.research_program.rail_exchange
```

The latter tries the diagonal upper-left repair at each possible length
and up to five waiting rows; at score 2048 it tests all ways of removing
a mark on one detected cycle and adding one mark elsewhere. No forest
was returned. This does not exhaust repairs with multiple exchanges.

`tight_corner_sat.py` can generate necessary conditions on the whole
board with four different orientations (one per choice of corner root):
they share the same selected bits, with one exact physical dual budget
per orientation. The budget is 72 in units of 1/1008. The depth-limited
variant drops interior charges and cannot establish a witness. A SAT
assignment of the full relaxation must still be checked for cycles;
an UNSAT result needs an independently checked proof before it is used
as an unrestricted exclusion.

Two strengthened encodings are `--turns --planar` (lift the oriented
compass directions to their two-sheet cover and prohibit crossing
corner splits) and `--roots 1 --matching` (reserve complementary edge
choices for a rooted primal spanning tree and its dual tree). Both include
the no-nontrivial-extra-component rule and rectangle cycle exclusions.
The matching encoding was independently verified UNSAT, so
**`P(77,77)=2047`**. To see that no genuine forest is lost, extend its
unique nontrivial component to a spanning tree and orient toward the
top-left corner. All forced arrows agree with that orientation. The
complementary edges form a dual tree rooted at the exterior face.
Every grid edge is chosen exactly once: either by a nonroot primal
vertex toward its parent or by a bounded face toward its dual parent.
A forced edge cannot be chosen by a face. These choices satisfy the
added matching constraints; the rectangle exclusions are necessary
because a rectangle with its entire perimeter forced is a cycle.

Replay with the same packages and solver builds as for side 35:

```
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.tight_corner_sat --roots 1 --matching --out target/match77.cnf
sha256sum target/match77.cnf
target/cadical/build/cadical target/match77.cnf target/match77.drat
target/drat-trim/drat-trim target/match77.cnf target/match77.drat
```

Checked input SHA-256 `7507ba7eb2c1ba566299097fca8c5424394bf8c4f1b660a3d73c78461bd9edbe`:
148052 variables, 1023370 clauses; final checker status `s VERIFIED`
(38637746 resolution steps). This is an unrestricted finite exclusion,
not a result for every size congruent to 77 modulo 42.
