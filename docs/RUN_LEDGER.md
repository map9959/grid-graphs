# A common run count on the open residue-two tail

Let `n=35+42t >=119`, and suppose the integer upper target `U` is
attained. Use the proved [single-star and boundary results](ODD_SINGLE_DEFECT.md).
Write `g` for the number of perimeter gaps and `I` for the count of
isolates of the **forced graph on all grid vertices**. Then

```
I = 2-g,       r = 8n/7-2,       J = r-1,
```

where `r` counts maximal connected marked runs (including singletons)
and `J` counts unmarked vertices with two marked neighbors. In the
two-gap case the forced edges already form a spanning tree. In the
one-gap case the unique isolate is the charged star itself.

## Why a zero-charge isolate cannot occur

A perimeter site is not isolated: it lies on a forced perimeter edge.
For an interior isolate the centered `3x3` mark mask has an empty
cross (center and four neighbors), and the center star has no outgoing
arrow. Every patch must have zero charge on the remaining branches.
Inspect these conditions with the radius-two neighborhood of the center.
For each possible centered mask, enumerate just the outer ring of
this `5x5` box, clipped to the board. Reject a diagonal adjacency of
marks (it forces a square cycle), a mismatch with the two known frame
rings, or a positive charge on any fully visible patch. Other stars
need not be checked. This is a **necessary local test**, not a full-board
search. It eliminates every isolate with center charge zero.

For example, far from a side, the centered star and patch tables alone
permit an isolate only at residues `(2,2)` with diagonals `68` or `257`
(two opposite corners marked). Neither extends through the surrounding
zero-charge patches. Near a side, every remaining candidate has normal
distance two and center charge 72. Conversely, at the permitted
distance-two charged-star sites, the neighbor toward the perimeter is
unmarked. With that bit zero, the only local event of weight 72 is
`(no outgoing arrow, all five mark bits zero)`: it really is an isolate.

`isolate_ledger.py` checks the finite mask implication for each frame
word with one or two gaps, including words already excluded. The axis
samples retain end distances 0 through 8 and three interior residues.
Their radius-two halo determines every clipped star and patch type,
every frame bit and the shape of the window. In a larger square the
new axis coordinates only duplicate interior residue classes: 42 is
divisible by three and the far-end distances remain fixed.

With two gaps the sole 72 is spent on the perimeter exit, so `I=0`.
With one gap the sole 72 is the interior star and gives `I=1`.
In either case there is only one nontrivial forced component by the
single-defect theorem.

## Counting and reversing the reduction

Put `M=U` and `B=4n-4-g` (marked boundary incidences, corners twice).
The already established edge count `3M+r-B=n²-1-I` now fixes `r`
independently of the frame. No diagonal pair of marks is possible,
so runs are straight and an unmarked site with two marked neighbors
has them opposite. Contract the runs and suppress these two-neighbor
sites to join edges; discard unmarked leaves and isolates. The result
is a tree on the `r` runs, so `J=r-1` (parallel joins count separately).

This gives a converse target for construction: for a permitted frame,
arrange exactly `8n/7-2` maximal runs, with no diagonal marks, leave
exactly `2-g` sites uncovered by their closed neighborhoods, and make
the join multigraph a tree. Expanding its edges and restoring leaves
gives a forced forest, and solving the edge identity for `M` gives
exactly `U`. No orientation or SAT assignment is needed for this
sufficiency direction.

## A color check on the join tree

For checkerboard colors `c=0,1`, write `M_c,B_c,N_c,I_c,J_c` for
the marked sites, boundary incidences, board sites, isolates and joins.
Counting marked-to-unmarked incidences from color `c` gives

```
J_(1-c) - I_(1-c) = 3 M_c + r - B_c - N_(1-c).
```

Indeed there are `4 M_c - B_c` incidences before removing the `M-r`
marked-marked edges, each with one endpoint of color `c`. Count the
rest from the unmarked endpoints, with joins counted twice and
isolates not at all. Here NW is even, `B_0=2n+2-g`, `B_1=2n-6`:
each corner word omits one odd boundary site and each gap one extra
even site. In particular `J_0 ≡ I_0 (mod 3)`. This constraint is not
by itself a contradiction.

```
python3 -B -m analysis.research_program.isolate_ledger 119
python3 -B -m analysis.research_program.isolate_ledger 161
# at 119: target r=134, J=133; rail r=136, J=65+69
# at 161: target r=182, J=181; rail r=184, J=89+93
```

The rail numbers come from the actual `U-1` marks, not the target
equations. The two checks illustrate a specific construction task:
gain one mark while eliminating two runs, with the joins becoming a
single tree. Neither an all-size construction nor an impossibility
proof for those arrangements is yet known.

## An obstruction to any interior one-for-two repair of these rails

Let `X` be `zipper_rails.build(n)` and keep its perimeter unchanged.
Write `n=35+42t`, `F=5+7t`, `M=6+6t`. A repeatable candidate is
to remove `(F+5,3F+2)` (first full band's middle singleton), fill
`(n-6,M+2)` (the cap bridge), and extend a top tooth at `(2,3)`.
The sites are mutually more than two steps apart. Their old marked
degrees are 0,2,1 respectively, and the additions create no diagonal
contact. Thus the score increases by one, marked adjacencies by
three, and runs decrease by two. But the deleted center is uncovered.
In fact for any such candidate with the prescribed score/run counts
and unchanged frame, `J=r-1+I`, by counting forced edges, so even
one isolate forces a cycle in the run multigraph. At 119, 161 and
203 the actual edited join graph has two components and cycle rank
four, with three isolates of the forced grid. It is not a tree.

More generally **no deletion of one interior mark and insertion of
two interior marks on this rail family can achieve the score and run
target while preserving coverage and avoiding diagonal contacts**.
This includes edits whose locations drift or separate as `t` grows.
Indeed the marked adjacency gain must be three. The two new marks
can contribute at most four edges total, so the removed mark `x`
has at most one marked neighbor. Let `L` consist of sites whose closed
unit neighborhood originally intersects `X` only in `x`. Every site
of `L` must be covered after the edit because the two-gap frame requires
`I=0`. The following small integer-set check proves, for every eligible
`x`, that `L` is nonempty and **no one admissible insertion covers `L`**.
Thus both insertions must cover some site of `L` and both lie within
Manhattan distance two of `x`. This localization is derived, not assumed.

`rail_swap_uniform.py` operates on exact integer sets of triples
`(t,i,j)` with unbounded `t>=0`, where `(i,j)=x`. In the affine
description the zipper has `F` front rows and `3+5t` complete bands
followed by one partial row. The left rail coordinate in band `b`
is `3F-3b`. For each of the twelve possible insertion offsets the
verifier intersects shifted mark sets, checks the four diagonal
neighbors after deletion, and subtracts centers whose lost sites
remain uncovered. Of the 54 unordered non-diagonal pairs, 15 can
restore coverage somewhere. Splitting those sets on the finitely
many neighboring mark bits counts every gained and lost marked edge;
the **maximum net gain is two**, below the required three.

```
python3 -B -m analysis.research_program.rail_swap_uniform
# affine mark set equals physical rail at 119 4831 sites
# affine mark set equals physical rail at 161 8791 sites
# offset pairs tested 54 coverage-restoring pairs 15 largest net marked adjacency gain 2 required 3
python3 -B -m analysis.research_program.run_rail_swap 119 161 203
# at 203 the explicit candidate has 13928 marks, 230 runs, 3 isolates,
# 232 joins, 2 join components and cycle rank 4
```

The first command uses `libisl` for exact integer-set emptiness, not
finite interpolation. The second independently checks the actual
marked grids. Even a no-deletion single insertion cannot gain three
marked adjacencies. A successful perimeter-preserving repair of these
rails must therefore remove **at least two marks and add at least
three**, or a construction must change the frame or start elsewhere.

## A covering two-for-three repair misses by one cycle

For `n=35+42t`, `t>=2`, write `F=5+7t` and `M=6+6t`. Use cap-local
coordinates relative to `(n-6,M)`. Delete `(1,2),(3,1)` and insert
`(2,0),(2,1),(2,2)`. This extends the cap's four-mark horizontal rod
to seven marks. It gains one mark, loses two runs, and **leaves no
uncovered site**. Unlike the one-for-two trial, it meets the entire
numerical ledger, including `J=r-1`. But the new rod joins both the
rail at column `-6` and the rail at column `4`; those rails already
join via the bottom bar. In the forced grid the rectangle bounded by
local rows 2 and 5, columns −6 and 4, is a simple cycle of length 26.
Every edge of its boundary has a marked endpoint on every tail size.

We checked all interior two-for-three substitutions with edits anywhere
in the union of three translating rectangles. Relative to their
respective origins, the inclusive row and column ranges are:

| Origin | Rows | Columns |
|---|---|---|
| front merger `(3+F,3F)` | −5..4 | −10..11 |
| drifting band `(10+F,3F−3)` | 0..6 | −7..8 |
| bottom cap `(n−6,M)` | −7..3 | −9..9 |

Their row intervals are separated by at least three steps, so the
changes in marked adjacency and the tests for diagonal contacts and
loss of coverage are independent across windows. Within each window
count the old edges incident to deletions once, count new edges incident
to additions once, and check whether every formerly covered site losing
its last old mark is covered by an addition. Combine the three window
tables at exactly two deletions, three insertions and net adjacency
gain three. **Just the cap edit above survives.** Exact affine-set
checks verify every old mask in the windows plus a two-step halo at
all `t>=2`, and global baseline coverage. This tests all allocations
*among these windows*, not all edits on the board.

```
python3 -B -m analysis.research_program.double_rail_window
# three-window allocations: 1 pass all local ledger/coverage/diagonal checks
# uniform 26-edge forced cycle verified for every n=119+42s
# n     marks  runs  isolates  joins  join components  cycle rank
# 119   4832   134   0         133    2                1
# 161   8792   182   0         181    2                1
# 203   13928  230   0         229    2                1
```

Thus a natural next construction target is a **count-neutral rerouting**
that breaks this explicit cycle and joins the two components while
preserving coverage. The necessary counts themselves no longer need repair.

## Moving the cap tip to the front merger

Start from the covering seven-mark cap above. In the same cap coordinates,
remove its right endpoint `(2,2)` and insert a mark at the merger
`u=(F+3,3F+2)` in board coordinates. This preserves the score and run
count: the deleted endpoint has one marked neighbor and the insertion
extends a singleton-side end of the central tooth (one marked neighbor).
The cap edge from `(2,2)` to `(2,3)` is no longer forced. The new mark
joins the central upper tooth to the right rail through `u+(0,1)`.
The tooth at column `3F+2` reaches the top bar through row one, and
the right rail at `3F+4` reaches the bottom bar. Hence the old top and
bottom components really are joined, not merely brought closer.

The price is exact. The two cap sites `(1,2),(3,2)` lose their only
covering mark, while the mark at `u` closes two `2x2`-cell squares,
with opposite vertices `u` and `u+(2,±2)`. Their boundaries give
distinct forced 8-cycles. The fixed-offset mark predicates and both
long tooth paths are checked as affine integer-set identities for
all `n=119+42s`. For example, at 119 direct replay gives 4832 marks,
134 runs, one connected component containing edges, two isolates, and
cycle rank two. This is not a tree.

There is also a general obstruction for **one interior relocation**
from this covering cap, wherever the destination is. Cutting a forced
cycle edge by deleting just one mark requires deleting its unique marked
endpoint. With the perimeter fixed exactly six cap marks qualify. Each
has at least one private site (one whose closed unit neighborhood contains
only that mark). A covering replacement must lie in the intersection
of the private sites' closed neighborhoods, even if arbitrary long moves
are allowed. For all six cutters the uniform check finds no previously
empty interior replacement that avoids diagonal marks *and* has the same
marked degree after deletion. Equal degrees are required to keep `r`
constant at fixed score.

Finally allow **two deletions and two insertions** distributed between
the merger and cap rectangles defined above. Require an insertion in
the merger, destruction of the original cycle, coverage, no diagonal
contact, and preserved marked adjacencies. The separate window profiles
add without overlap; none meet these conditions. The profiles are
uniform by the previously checked halos and the fixed cap offsets.
This last exclusion is restricted to the two windows.

```
python3 -B -m analysis.research_program.neutral_rail_reroute
# all t>=2: cap cycle cut and top/bottom joined; two uncovered cap sites and two forced 8-cycles
# all t>=2: 6 interior one-mark cycle cutters; no covering single relocation anywhere preserves the run count
# at 203: 13928 marks, 230 runs, uncovered [(198,32),(200,32)], one nontrivial component, cycle rank two
```

## Paired relocations with an unrestricted destination

For every `n=119+42s`, **two interior relocations cannot repair either
of the last two candidates** while retaining the two-gap frame. Here
two relocations mean two distinct old marks deleted and two distinct
previously empty sites marked, simultaneously; cancellations amount to
fewer edits. This exclusion is not restricted to the merger window.

Start with the covering seven-mark cap `Y`. Every interior mark has
a private site; therefore any covering one-for-one replacement must
insert within two steps of its deletion. In fact, in the cap coordinates
used above, the entire board admits just these four diagonal-free
covering replacements, uniformly in size:

| Delete | Insert |
|---|---|
| `(-1,0)` | `(0,-1)` |
| `(2,-6)` | `(3,-7)` |
| `(2,-3)` | `(3,-4)` |
| `(2,4)` | `(3,5)` |

This list alone does not exclude a simultaneous two-for-two change.
To account for cooperation between edits, group changed sites using
Manhattan distance at most two as adjacency. Distinct groups have
independent coverage, diagonal-contact and marked-edge tests: any
two edits affecting one closed unit neighborhood are at most two apart.
Choose a destroyed edge of the cap rectangle. All its formerly marked
ends are deleted, in the same edit group. This group cannot reach the
upper tooth component: with four edits its radius from the cycle is at
most six. The upper bar and its teeth lie at rows `<=F+2` and are at
distance greater than two from every other mark; this separation is
also checked directly on the affine mark sets. A connecting insertion
is required outside the cap group, which thus has at most one insertion.

There are now at most three edits in the cap group. Enumerate all its
possible deletions within four steps of the rectangle (an overestimate).
For each deletion set breaking the rectangle, compute the newly
uncovered sites; none of the sets can be left without an insertion.
A single replacement must lie in the intersection of their closed
neighborhoods. After checking diagonal contacts and that the cycle
is still broken, exactly the second and fourth swaps in the table
survive; **none deletes two marks**. Each loses one marked adjacency.
The remaining deletion/insertion would thus have to be a covering
single replacement, acting independently, gaining one adjacency and
connecting the separated groups. There is no such entry in the global
catalogue.

For the later two-hole pattern the two insertion cases are especially
simple. Its private cap sites `(1,2),(3,2)` have just one common cover,
`(2,2)`. Restoring that mark reduces the proposed repair to at most two
relocations from `Y` (the already-inserted merger tip counts as one).
Without restoring it, **both** insertions are needed in the cap. On the
two merger 8-cycles every marked vertex except their new tip has a
private site there. Deleting such a vertex without a merger insertion
breaks coverage. Removing only the new tip there disconnects the
upper teeth again; additions at the cap cannot reconnect them.

```
python3 -B -m analysis.research_program.paired_cap_relocation
# remote covering one-for-one moves touching both marked groups: offset classes 0
# covering cap cluster: zero insertions impossible; ... two swaps, adjacency change -1 each
# 119 / 161 / 203: actual covering single replacements 4; possible new joins 0
```

The uniform check compares the affine sets of legal deletion centers for
each insertion offset with the four listed coordinates by exact integer
set differences in **both** directions. Independent finite replays use
flood fill on physical rail marks. The conclusion raises the required
size of an interior count-neutral repair from these candidates to at
least three relocations; it does not decide other constructions.

## Three relocations: the cap and bridge budgets cannot both be met

On every `n=119+42s`, three distinct interior deletions and three
interior insertions **cannot** repair the seven-mark covering cap,
even with simultaneous edits at unrestricted distances. Nor can they
repair the subsequent two-hole rerouting. The perimeter remains fixed.
Here is a reproducible profile certificate rather than a full-board
tree search.

Write a profile `(r,i,e)` for removals, insertions, and net change in
marked adjacencies **within an edit group** (edges to the background
are included). At fixed score the required run count is preserved
exactly when `e=0` in total. Use clusters connected at Manhattan
distance at most two. Distinct clusters cannot affect the same closed
unit neighborhood or diagonal constraint, and their adjacency changes
add. Each original mark of the covering cap has a private site, so
every deletion must be within two steps of an insertion in its cluster.

Choose a broken edge on the 26-cycle. Its formerly marked ends belong
to one cluster. This cluster cannot also bridge the old components:
even six edits span at most ten steps, well short of the upper teeth.
It must have at least one insertion to preserve coverage, and at least
one insertion must remain outside it. With at most three deletions and
two insertions it lies within eight steps of the rectangle. Enumerate
its deletions starting with the marked ends of the cut edge. Insertions
must cover the newly uncovered sites, avoid diagonal contacts, leave a
cycle edge broken, and be connected to those deletions in edit distance
two. Deduplicate the resulting edit sets:

| Cap profile | Number |
|---|---:|
| `(1,1,-1)` | 2 |
| `(2,2,-2)` | 1 |
| `(2,2,-1)` | 2 |
| `(2,2,0)` | 3 |
| `(3,2,-3)` | 5 |

Any successful path between the old groups must cross on a chain of
new marks, successive marks at distance at most two. Pick the chain
between the last retained upper mark and the first retained lower mark.
There are at most two insertions available to this cluster. Its first
insertion must therefore be within two of the upper and four of the
lower group. A second insertion in the cluster, even if not on that
chain, is within six of the first (at most two intervening deletions).
Generate all its deletions within two of the additions, check the
private sites, diagonal contacts and touching both old groups after
deletion. This is necessary for a bridge, not a sufficiency claim.
The only resulting profiles are `(0,1,1)`, `(0,2,2)`, `(0,2,3)`,
`(1,2,0)`, `(1,2,1)`.

**Uniformity check.** Cap marks, interior permissions and the two-step
halo are fixed in translated coordinates. For the bridge, a radius-ten
diamond suffices (6 to the second insertion, 2 to its deletion, 2 to
the marks affecting coverage). Enumerate the profiles first at `t=2`
through `5` in `n=35+42t`. For every larger `t`, let `A` be the affine
integer set of eligible first-insertion centers. Compare the mark set,
upper-group membership and interior permissions with those at `t-1`
translated by each of `(0,0),(0,42),(7,21)`. For each translation
dilate its disagreement set by the radius-ten diamond. Exact integer-set
intersection of `A` with **all three** dilated sets is empty: every
eligible neighborhood has an identical smaller-board representative.
This proves completeness for all `t`, not extrapolation from four boards.

Subtract any compatible pair of profiles from `(3,3,0)`. Negative
remaining counts are impossible, as are deletions without an insertion.
The only additional nontrivial coverage question is two deletions and
one insertion: both deleted marks must be within two of that insertion.
A separate affine test of every offset pair finds none restoring coverage
without a diagonal contact, anywhere on the board. In the cases with
no leftover edits the net adjacency change is wrong. Thus no combination
can cut the cycle, connect the components, and meet the ledger.

For the two-hole candidate, restoring the old cap tip or removing the
new merger tip reduces to at most three relocations from the covering
cap. Otherwise both cap holes must be filled by separate additions near
them. At least one merger insertion is necessary: every marked vertex
on its two forced squares except the retained tip has a private site.
That last insertion must cover a private site of a deleted mark on the
first square and permit breaking the second. All deletions must be
within two of an addition: the retained merger tip is the only possible
exception to private coverage after its insertion (checked on its
two-step neighborhood). The cap profiles are then `(1,2,-1)`,
`(1,2,0)`, `(2,2,-2)`; the only merger profile breaking both squares
is `(1,1,0)`. None sums to `(3,3,0)`. Both of these local neighborhoods
are fixed for all `t>=2`.

```
python3 -B -m analysis.research_program.triple_rail
# covering 2-out/1-in displacement pairs anywhere: []
# every bridge halo at t> 5 reduces by 42: True
# no compatible coverage-preserving cap/bridge/remaining allocation at (3,3,0)
```

This gives a lower bound of **four** relocations for a fixed-perimeter
repair from either candidate. It does not rule out different rail
families, a changed frame, or a longer coordinated rerouting.
