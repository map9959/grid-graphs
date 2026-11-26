# A sharp four-layer bound and a smaller-square reduction

For side `n≥20`, **at most `8n-40` marks** of any feasible square
marking lie in the outermost four layers. This is sharp, with a
physical tree completion. There is no hypothesis on the words on
these layers, the connections through the interior, or the end rows.
Layer numbers below start at zero.

## Why the four-layer count is uniform

Partition the annulus into four `4×4` corners and four straight
width-four arms of length `n-8`. Sweep them cyclically, retaining
the four sites at the initial slit and the four current sites.
Keep the current mask and the full partition on these eight sites;
fix the initial mask in an outer loop. Union sites along each
forced edge, rejecting a union within a component. To glue two
summaries, take their disjoint union and identify the four common
sites one at a time. A redundant identification creates a cycle
in the glued graph (equivalently, insert four matching edges and
then contract them). The summaries have disjoint edge sets.

For a corner, enumerate its 65,536 physical masks. Keep the maximum
score for each pair of face masks and partition of the face sites,
accounting for the shared site of the two faces. Include the incoming
seam edges when appending that summary. For a straight slice only
16 masks are needed. Close the slit by inserting its actual forced
edges. There is one further physical condition at each reentrant
corner: the innermost tips of the two arms cannot both be marked.
They are diagonal; together they would force a square via the first
site *outside* the four-layer annulus. All other edges to the blank
central square are pendant. Ignoring an arbitrary marked interior is
valid for the upper by monotonicity. No flooding or component labels
from a presumed interior pattern are used.

At side 20 the maximum is 120. On **each** straight pass for **every**
starting mask, the full price vector after one more slice equals the
old vector plus two, entrywise, by step eight. The shortest pass has
ten steps. Adding any number of steps therefore adds twice that
number uniformly before the next corner. The corner and closing
operations commute with addition of a constant. Induction over the
four passes gives `120+8(n-20)` for all `n≥20`. The simpler independent
open-elbow calculation gives the weaker `8n-36`: closing all four
seams and checking the inner corner tips matters here.

Backtracking the side-20 optimum gives two adjacent identical central
rows and columns, each with isolated mark bits at depths 0 and 3 from
either side. Duplicate the middle row and column. The forced crossing
edges at those bits are subdivided; the new tangential edges at the
inserted sites are leaves. The two cuts intersect in the blank core.
This pumps eight marks per side increment. The check also builds and
completes the pumped side-103 forest (`784` specified marks).

## How much a crop costs

Write `C(k)=3k²+5k+floor((3k-13)/10)` for the comb at `n=3k+1`.
Remove six layers to get side `n-12`. The exact budget is

```
C(k)-C(k-4) = 8n-36+e,   e=floor((3k-13)/10)-floor((3k-25)/10) ∈ {1,2}.
```

Choose any four consecutive layers starting at depth `d=0,1,2`.
Apply the cap in the sub-square of side `n-2d` (at least 20).
Let `B` count all marks on the other two removed layers. If `A` marks
can be added to the crop while keeping its forced graph acyclic, the
original score minus the new crop score is at most the comb budget
**minus**

```
S = 4+e+16d - (B-A).
```

Thus `S≥0` is a smaller-square reduction. If `S` covers the known
unrestricted upper-minus-comb gap on the smaller side, it proves the
comb upper for this input without induction. At 103 the smaller side
is 91, `P(91,91)≤2858=C(30)+1`, and `e=1`. Even with no recovery,
at most **four marks in layers 4 and 5 together** suffice. With
recovery, replace this count by unrecovered marks. More generally a
3647 witness must have `B-A≥5+16d` for **each** of the three choices.
The inequalities apply at later crops too; their savings add.

For recovery, project marked sites of the last removed ring straight
inward to vacant crop boundary sites, merging duplicate candidates.
Contract the old crop forest and insert all proposed new star edges
into a spanning forest of this multigraph (keep loops as rejected
edges). For each rejected edge withdraw every proposed owner of that
edge. All surviving new edges now lie in the spanning forest, proving
the remaining promotions simultaneously feasible. This is a lower
bound on recovery, not an assumption that every projected site pays.
In a replay with 25 depth-five teeth, all 25 were recovered. The
four-layer certificate alone, with this recovery, gave `S=5`.

## A shallower peel for punctured perimeters

Alternatively use the existing [two-layer cap](../lean/GridGraphs/Accounting/CarrierLayers/Annulus/Cap.lean)
`4n-9`, remove three layers, and recover marks in side `n-6`. The saving is
`3+e'-(B-A)` with `B` the depth-two count and `e'` the analogous
floor difference over two steps. In the five-path end-repair obstruction
five applications give saving 18. A perturbed example removed 430
marks against a budget of 406 but recovered 27 on the smaller square.

There is a second certificate when many marks flank punctured
perimeters. For a `3t`-layer peel take the rings at depths `0,3,…,3t-3`.
Assign an adjacent off-ring mark to a **straight marked** parent on
the ring if possible, without duplicate assignments. The parent's
two tangential neighbors must both be vacant by diagonal exclusion;
charge one incidence to each. Each vacancy receives at most two
incidences (one on the outermost ring). Indeed its two adjacent
parents cannot both have a mark on the same normal side: that
would complete a `2×3` perimeter cycle via the two marked parents.
At a ring corner the two candidate parents are themselves diagonal.
So if `H` sites of a ring are vacant and `U` vacancies untouched,
the ring plus assigned guards saves at least
`H-floor(cap*(H-U)/2)` against its full perimeter, where `cap=1`
on the outside and `2` elsewhere. Sum these credits; debit all
unassigned off-ring marks and apply any physical crop promotions.
This allows arbitrarily many displaced marks instead of just deleting
five fixed sites per layer.

## Reproduction

```
python3 -B -m analysis.research_program.collar_closed
python3 -B -m analysis.research_program.collar_elbow
python3 -B -m analysis.research_program.collar_vacancies
(cd lean && lake env lean GridGraphs/Geometry/CollarPeel.lean)
```

The transfer and physical replays are Python certificates. Lean checks
the reduction arithmetic. A forest can have many unrecoverable fringe
marks: on the side-103 comb itself the shallower test finds 59 fringe
marks and no accepted promotions. No implication from failure of the
end exchange to success of a peel for *every* marking has been proved.
