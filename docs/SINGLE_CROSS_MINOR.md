# Cutting directly to the solved multiple of three

Take any marked forest on side `n=3k+1`. Delete row `i` and column `j`
(interior or boundary), close the two gaps, and keep the surviving marks.
Let `Lij` be the number erased and `qij` the cycle rank `E-V+c` of the
new forced graph, including isolates in `V,c`. Then

```
M ≤ P(3k,3k) + min_ij (Lij + qij).
```

There is no pitch, phase, or exterior hypothesis. In the reduced graph
retain every forced edge whose endpoints were neighbors or which expands
to a forced two-edge path. All these expansions are internally disjoint:
horizontal midpoints are in the deleted column but not the deleted row;
vertical midpoints are in the deleted row but not the deleted column.
They therefore form a subdivision inside the input forest. Every
remaining edge has **exactly one** marked endpoint (two marked endpoints
would force the expanded path), and a blank midpoint. Extend the retained
forest greedily by the remaining edges. Exactly `qij` are rejected.
Erase their marked endpoints; every remaining forced edge belongs to
the resulting forest. Repeated endpoints need be paid only once.
Extend this forest to a tree on the smaller square.

An inexpensive one-dimensional corollary uses a row charge `a_i`:
count its marks plus its blank sites whose two vertical neighbors have
different bits (the second term is zero on a boundary). Define `b_j`
by transposition. Then `Lij+qij ≤ a_i+b_j` since each unsupported
edge is counted on its corresponding line. In particular any above-comb
forest must satisfy

```
min_i a_i + min_j b_j ≥ 2k+3+floor((3k-13)/10).
```

More precisely **every cross** must cost at least this much even using
the distinct rejected endpoints. Averaging the rank version gives
`mean qij ≥ M(n-1)^2/n^2 - P(3k,3k)`, since a mark is retained on
exactly `(n-1)^2` crosses. At side 103 the minimum loss required is
79 and the mean rank required is at least `90476/10609` for score
3647. These are necessary conditions, not lower bounds on every rank.

Run `python3 -B -m analysis.research_program.cross_minor_price`. It
also physically completes two examples with no spanning pitch row or
column. A shifted crop has a cost-35 reduction, whereas breaking scattered
teeth gives a best cost of 125 with this edge order. Thus absence of
pitch alone cannot force this particular repair algorithm below 79.
The latter example already has only 3551 marks: a coverage proof would
have to use density as well, or improve the physical repair.

## Credit for marks made feasible by the cut

Let `F` be the physical repaired forest; suppose erasure plus repair
cost `l` marks. Contract each component of `F`, including isolates.
Select a set `S` of blank sites with no neighbors in `S`, and put in
all the edges required by these new marks that are not already in `F`.
Let `d_s` count these edges at site `s`, `R` their joint graphic rank
on the contracted vertices, and `z=sum d_s - R` their nullity (count
loops and parallel edges). Then there is a physical reduction at cost

```
l - |S| + z  =  l + sum_s(d_s-1) - R .
```

Here and below "at cost" means at most. Extend a maximal forest of the
new edges on the contraction. Each of the `z` rejected edges has just
one owner in `S`. Withhold its owner; this deletes that edge without
damaging a compulsory edge. Every remaining new mark is feasible.
In particular for a hypothetical 3647 forest **every** cross and bank
must satisfy `R ≤ l - 79 + sum_s(d_s-1)`. This can test a whole bank
without selecting an optimal subset. The classes `y+2x mod 5` give
disjoint closed grid neighborhoods *within* a bank; different sites'
neighborhoods can still meet the same forest component, which is why
`R` must be evaluated after contraction.

`python3 -B -m analysis.research_program.cross_minor_refill` replays a
3602-mark, inclusion-maximal, no-pitch side-103 control: every other
site on the input would close a cycle. On cross `(37,49)` (zero-based)
60 marks are erased and 25 paid for cycle repair. In bank 1 the
12 individually addable marks jointly create just one cycle, so at
least 11 can be restored: `60+25-12+1=74`. The smaller tree realizes
3528 marks. Thus the improvement does not rely on marks already
available before the cut.

**Passing a certified cut through isolated perimeter layers.** Given a
core of side `m`, center it in side `m+6` and allow an arbitrary
feasible subset of marks on the outer perimeter, leaving the two
intervening layers unmarked. Any physical cross reduction in the
core extends across this layer at an additional cost of at most four
marks. The cross erases four perimeter sites. The surviving straight
pieces join up away from corners; their off-rim forced edges are
leaves (near-corner diagonals were already excluded). Thus only the
perimeter itself could cycle. Its old missing bond survives unless
one of its vacant endpoints is erased. In the latter case the other
endpoint survives, since the erased perimeter sites are nonadjacent.
Erase at most one neighbor of that vacancy to keep a missing bond;
the erased vacancy already saved one of the four marks budgeted.
The spacing still separates the forced edges of layer and core after
the cut, including if the core cut was on its boundary.

This gives cost at most `74+4t` for the control with any `t` such
layers. At `k=34+2t` the allowed cost `C(k)-P(3k,3k)` grows by at
least `4t` from 78. The replay includes both a surviving gap and a
destroyed gap. This extension assumes separation only for the added
layers; it does not imply that a general no-pitch forest has them.

## Local obstruction in the *original* maximum

For a tentative vertical tooth at `(y,x)`, call its two lateral
neighbors leaves if they and all their neighbors other than the tooth
are blank (clip at the board boundary). They become private leaves
when the tooth is filled. In a maximum forest:

* A vacant tooth with such leaves cannot have both vertical neighbors
  marked. Both axial bonds already exist, so filling it gains one.
  On a top/bottom boundary it need not even have a marked neighbor:
  if the sole axial neighbor is blank the site was isolated.
* Two vertically adjacent vacancies cannot both have such lateral
  leaves. Fill the pair. Ignoring leaves, this replaces a path with a
  missing middle bond by a complete path with at most two contacts to
  the exterior, so adds at most one independent cycle. No diagonal
  marked pair was introduced. On a simple cycle a turn must be marked
  (otherwise its neighbors are diagonal marks), and at least one of
  its two neighbors is blank. Unmarking the turn therefore removes a
  cycle edge. Net gain is at least one even if **neither** vacancy
  could have been filled alone.

In particular in five consecutive rows containing marks only in
columns `0 mod 3`, the middle row of a maximum is a full pitch row.
For any missing tooth there, either its two neighbors along the rail
are marked, or the tooth and a vacant neighbor supply the pair move.
This works in clipped five-row windows at either boundary too.
It follows that a **no-pitch 3647** candidate at 103 needs at least
21 different rows with an off-phase mark, with no gap of five clean
rows. The transpose applies to columns. More locally, each vacant
pitch tooth must see an off-phase mark in its own clipped `5×5`
box. This does not bound the number of dirty rows from above.

There is also a quantitative version for an arbitrary, not necessarily
maximal, no-pitch forest. In a block of `L≥5` clean rows, retain both
gate rows and complete all rails in the `L-2` internal rows. At most
one cycle is created per rail which did not already connect its two
gate sites: the completed rails attach to the caps only through those
sites. Rails with just one hole strictly away from the gates were
already connected. Thus a column with `d` holes in the central `L-4`
rows gains at least `d/2` after debiting new cycles (if `d=1`, a
second hole is needed to incur a cycle debit). All cycle turns are
outside the completed rows. Repair there as above: this leaves a
spanning pitch row and gains at least `ceil((L-4)/2)` marks. Both the
unrestricted upper and the [all-height pitch upper](WIRED_PITCH_SEPARATOR.md)
therefore apply to the **improved** count.

More generally allow `e` off-phase marks anywhere in the block, gates
included. Erase them first. Let `Z` count the missing interior teeth
and `u` the number of pitch columns with some pair of consecutive
vacancies between and including the two gates. Every other column
already has a forced longitudinal path between its gate sites. Those
paths form a forest with the cleaned caps, hence the complete slab has
cycle rank at most `u`. Normalizing the slab gains at least `Z-u-e`
and produces a pitch row. In a 3647 candidate `Z-u≤e` in **every**
such block. The central `L-4` rows give `2(Z-u)≥Z_deep` by the same
per-column argument. Without a pitch row each of these rows either
has a hole or contains an off-phase mark, so **`3e≥L-4`** even for
blocks with mixed phases. The count `e` is marks, not rows.

For a compressed forest apply the two local moves simultaneously on any
one column phase: disjoint intervals of length one or two on each
rail leave the other rails' lateral leaves untouched. After all moves,
the total cycle rank is at most the number of pairs, and the graph is
still diagonal-free. Thus the gain is at least the number of intervals,
even if their exterior cycle paths overlap. Use earliest finishing time
to pack the intervals on each rail. The six choices include transposes.
`python3 -B -m analysis.research_program.tooth_vacancy_exchange` checks
the cyclic two-for-one example and the packed physical reductions.
`diagonal_score --tooth-optimum` includes the corresponding necessary
clauses when searching for a global maximizer.

Counting the two axes on the same junction grid gives the
[joint pitch skeleton ledger](PITCH_SKELETON_LEDGER.md). In particular
the disjoint mixed-block requirements force at least 22 marks *off
both* pitch axes in a no-pitch 3647 candidate.

## Refilling an entire band against arbitrary cap components

For another necessary cut test erase a column `x` and one row in the
first `H≥4` rows, with `H<n`. Let `S` count old marks in those `H`
rows. In the retained cap erase `E` marks on column `x`; on its first
row erase `G` marks outside a chosen pitch phase of the new width
`3k`. Repair the column seam by the single-cross rule at cost `p`.
Group the `k` gate centers by their **actual** cap components, including
unmarked sites; let `j=k-#classes`. The following loss is attainable:

```
S - kH + E + G + p + j.
```

Refill the `H-1` available rows by one outer full bar, one blank
row, and `H-3` pitch rows. Each new rail meets the cap in one gate
site. In the outer bar unmark the centers of the redundant rails,
leaving exactly one attached rail per cap class. Every removed
center has a blank below it, so this actually disconnects its rail;
the horizontal bar stays connected. The new rows contain `kH-j`
marks. No constraint was placed on the old discarded rows, on
location of the column, or on the rank in the retained cap. A 3647
candidate must give at least 79 in this test for *every* phase,
band, column, and orientation. For a two-ended internal band the
incidence graph instead has one edge per rail between two gate
partitions, and only its cycle rank has to be repaired.
Replay: `python3 -B -m analysis.research_program.cross_rail_slab`.
