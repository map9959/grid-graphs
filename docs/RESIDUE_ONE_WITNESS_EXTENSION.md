# Side 31 is exact, and the side-28 gain persists

`P(31,31)=351`. More generally `P(3k+1,3k+1) >= 3k²+5k+1` for every
`k>=9`. Only the lower construction below is inductive.

```
python3 -B -m analysis.research_program.extend_forest_28 31 --grid
python3 -B -m analysis.research_program.patch_square --replay 31
```

Start with `forest_28.txt`. Coordinates start at zero. In a board of
width `n=3k+1`, insert three copies of column 10 just before column 10.
Then insert copies of widened rows 2,3,4 just before row 2. Deleting the
inserted strips gives back the original selected sites.

**Column seam.** Columns 9 and 10 are both selected exactly in rows
`0,3,...,n-1`. Across this vertical cut the only forced edges are in
those rows. Each is replaced by a path with three new internal vertices.
Each new internal vertex also has a leaf in each adjacent in-board row:
the empty rows on opposite sides of a gap of three are distinct. There
are no horizontal edges in the empty rows incident to the new columns.
Thus the modification subdivides edges and attaches leaves, preserving
acyclicity.

**Row seam.** Write `N=n+3` for the widened board's width. Widened row
1 marks just column 0. Rows 2 and 4 are the same word `A`, marking
`0,N-1`. Row 3 is `B`, marking `0,N-1` and the interval `2,...,N-4`.
The old seam between rows 1 and 2 has just the two forced vertical
edges at columns `0,N-1`. Inserting `A,B,A` extends these edges
to two disjoint paths. On the middle inserted row, the forced horizontal
path from column 0 through column `N-3` attaches to the left path;
it does not reach the right path, whose horizontal tooth ends at `N-2`.
The interior marks of `B` give distinct vertical leaves in the inserted
`A` rows. On each inserted `A` row only the two end marks have horizontal
teeth, and neither tooth meets a leaf from the interior of `B`.
All remaining new vertices are isolates. Hence no cycle is introduced.

The stated seam patterns are present in the base grid and persist:
after insertion the top rows again contain `A,B,A` at indices 2–4,
row 1 is unchanged, and central column marks are three rows apart
(one added at row 3). The next column insertion widens just the
middle interval in `B`. This proves the operation iterates indefinitely.

**Count.** Widening adds `3(k+1)` marks. The new rows add `2+n+2`
marks, for a total gain `6k+8`. This is the first difference of
`3k²+5k+1`, and the side-28 base has 289 marks. Every forced forest
extends to a spanning tree because the grid is connected.

At side 31 the solver-free verifier checks all 955 forced edges and
extends the six components to a 960-edge spanning tree with exactly
351 full-degree vertices. The separate unpooled rational patch dual
bounds every feasible forest by `351736329/1000000 < 352`, including
its residual allowance. These bounds match by integrality.

## Side 34: the unpooled patch LP crosses the next integer

The same unpooled rational upper test gives `10501272417/25000000`
at side 34. This is below 421 but above 420. A separately stored
nonnegative fractional primal satisfies all 18061 rows exactly with
score `10540589479812/25093601461 > 420`. Consequently no dual of this
LP can prove `P(34,34) < 420`, even with perfect rational recovery.
The primal is not a forest witness. Together with the 419 construction,
this test leaves only 419 and 420.

```
python3 -B -m analysis.research_program.patch_square --replay 34
python3 -B -m analysis.research_program.patch_square --primal34
```

**The larger value is attained: `P(34,34)=420`.** A separate physical
SAT search found two full boundary rows, 26 rows of vertical rails, and
a four-row cap. `verify_forest_34.py` stores those rows explicitly and
reconstructs the forced forest without SAT or LP software. There are
1154 forced edges on 1156 vertices and two components. One joining
edge completes a spanning tree with 420 full-degree vertices. Together
with the unrestricted upper `<421`, this settles side 34 and shows the
side-28 lower family is not always optimal.

```
python3 -B -m analysis.research_program.verify_forest_34
python3 -B -m analysis.research_program.patch_square --replay 34
```

## Extending the side-34 rails

For `n=3k+1`, `k>=11`, the 34-square witness gives the repeatable lower
bound `3k²+5k+2`. To grow it, insert three copies of row 2 before row
3. Then insert copies of columns 2,3,4 before column 2. Coordinates
are zero based.

The height seam has the same rail row on both sides, with selected
columns `0,3,...,n-1`. Thus only the rail edges cross this seam.
The inserted rows subdivide those edges and give horizontal leaves
to each new rail vertex. Rails are three columns apart, so their
leaves do not meet.

In the taller rectangle, columns 1 and 2 are empty except at the
two full boundary rows. The insertion subdivides those two crossing
edges. In the new three-column band, the middle column has one
vertical rail in rows `2,...,n-1` and the two flanking columns are
empty there. Its top attaches to the subdivided top edge through
row 1. Its bottom tooth at row `n` does not reach the bottom edge's
tooth at row `n+1`. All horizontal teeth of the new rail lie inside
the band. Thus the new edges add no cycle, and the old selected
vertices are retained. The same seam conditions hold at the next
size: the first two rail rows are identical, the bulk pitch is three,
and columns 1–4 have exactly the same vertical pattern with a
three-row-longer active interval.

The height insertion adds `3(k+1)` marks. The width insertion adds
`n-2` rail marks and six boundary marks, giving a total gain `6k+8`.
This is the difference of the claimed lower polynomial, whose base
at `k=11` is 420. In particular side 37 has a 494-site forest.

```
python3 -B -m analysis.research_program.extend_forest_34 37
python3 -B -m analysis.research_program.patch_square --replay 37
```

At 37 the matching unpooled rational certificate gives the unrestricted
upper `49437148231/100000000 < 495`. Hence `P(37,37)=494`.

At side 40 the construction has 574 selected vertices and 1594 forced
edges. Its six forest components complete to a 1599-edge spanning tree.
The unrestricted rational upper is `28734831141/50000000 < 575`,
including the residual allowance. Hence `P(40,40)=574`. Replay both:

```
python3 -B -m analysis.research_program.extend_forest_34 40
python3 -B -m analysis.research_program.patch_square --replay 40
```

## Side 43: the upper rounds to 661, but 661 is impossible

`P(43,43)=660`. The rail construction forces 1841 acyclic edges on
1849 sites. Joining its eight components produces a tree with 1848
edges and exactly 660 full-degree vertices.

The independent unpooled rational certificate gives
`33051173167/50000000 < 662` (including residual allowance
`1087/50000000`). The score-661 physical SAT formula is already UNSAT
before any lazy cycle clauses are added. This suffices: every genuine
forest would admit an orientation toward one sink per component, with
the top-left corner a sink in its component; all its 3-square masks
would be legal. Averaging its event counts over square symmetries gives
the dual budget used by `side28_sat.cnf`. Negative residual charges are
divided by orbit sizes to obtain physical per-occurrence costs. Rounding
each cost down at scale 168 only weakens the constraint. No symmetry
of the selected set and no particular rail structure is required.

CaDiCaL returned `s UNSATISFIABLE`; drat-trim independently returned
`s VERIFIED` using 2943007 resolution steps. Formula SHA-256:
`bb613f15326c79b463b847b40bbd237f5d9ca2fb9199e8c2cc020a04d694e78b`
(230662 variables, 1156762 clauses). The proof is regenerable; it does
not depend on an enumeration of candidate trees or a search timeout.

```
python3 -B -m analysis.research_program.extend_forest_34 43
python3 -B -m analysis.research_program.patch_square --replay 43
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.side43_proof --check
```

Use python-sat 1.9.dev24 with pindakaas 0.6.1, CaDiCaL `6b3d70b` in
`target/cadical/build` and drat-trim `2e3b2dc` in `target/drat-trim`.
