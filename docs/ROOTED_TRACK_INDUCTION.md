# One-gap equality permits at most two expensive tracks in a south packing

Let `n=119+42t`, `k=(n-2)/3=39+14t`. Normalize a putative one-gap
upper witness to the north isolate and frame `0133`. Pair tile rows
`(3,4),(5,6),...,(k-2,k-1)` (zero-based). These disjoint six-site
strips avoid every possible isolate halo. On each strip tie all actual
crop teeth to a single virtual root: they attach to the same perimeter
path, so a cycle after tying is forbidden. Other marks are free.

At the cut just before the last six east-end plaquette steps, record the
last two tile masks, the last column of marks and the partition of its
six vertices and the virtual root by forced connectivity to the west.
For each such state the minimum prefix deficit in the certified tile
relaxation is exactly `b+s*t`, where `s` is **0 or 14**. Call the
physical track expensive if its actual prefix state has slope 14.
This refers to connectivity as well as marks; it does not assume that
the witness itself has minimum cost.

After the east suffix the two minima (cheap, expensive) are:

| Transverse type | Cheap | Expensive |
|---|---:|---:|
| 3–10 | 5 | `k-2` |
| 11 | 5 | `k-3` |
| 12 (bottom edge) | 10 | `k+3` |

**Induction check:** use the side-119 certified quadruples. Between
the two six-step fringes every tile step has the same bulk catalogue
and root rule; root ties on the bottom track are retained. Inserting 14
tiles inserts 14 such steps. For each endpoint, predict its slope by a
first increment, then propagate each slope class separately for 14 steps.
Every incoming line has at least the predicted intercept at the next
length and at least the predicted slope, and a line achieves both.
Thus the min-plus recurrence proves the state formulas for every `t`,
not just at the two initial lengths. The end fringes need no repetition.
The 13 clipped coordinate types and deep-axis filter are as in the
[tile catalogue proof](TILE_CASES_245.md). This is exact for the strip
relaxation and only necessary for a square.

There are `(k-3)/2` paired tracks including the bottom track.
All tiles have nonnegative deficit. Three expensive tracks would cost
at least `5*(k-3)/2+5+3*(k-8)`. Subtract the one-gap equality budget
`5*k-1+floor((k-5)/7)`; the difference is `5*t-10`.
Thus for **every `n=245+42j`**, at most two tracks of this packing can
have an expensive state, on either axis and at any isolate distance.
This does not force three expensive states. A way to finish this approach
would be to force costly states using the *joint* compatibility of
neighboring strips, including routes that leave and reenter a strip.

Replay (no SAT solve and no new proof files):

```
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.rooted_track_induction
```

## Coupling the southern strips

**Shared marks and rooted acyclicity in a band do not by themselves
force three expensive tracks.** For `k=39+14t` set `L=floor((k-12)/8)`.
There is a *single* filling of the southern `6L` tile rows, full width,
including both corners, with all `3L` packed tracks cheap on both axis
branches. This covers asymptotically three quarters of the tile rows.
All plaquettes wholly in the band obey the one-gap mark catalogues,
including those across track boundaries. All forced edges in the band
are checked together after tying the marked crop teeth to one root.
This is a regional projection; it does not fill the north, or require
the interior marks to lift to common zero-charge arrow and face data.

Here is the filling. In tile row `q=3a+b` up from the bottom, start
with `s=k-2-b-4a` copies of mask 7. Then write the word for `b`:
`(3,8,264)`, `(33,32,384)`, or `(16,16)` respectively. Fill the rest
with 448 and truncate to width `k`. Clear the outermost physical
column of bits at either end. The row deficit is six, except for four
in the bottom row. Thus each track costs at most 12, strictly below
the expensive minimum `k-3`. The band costs `36L-2`, below the whole
board's equality budget. The diagonal transition is why this example
couples many strips without requiring marks in different strips to
repeat at identical positions.

**Induction certificate.** Process three tile rows at a time, bottom
to top, and insert each physical forced edge once. Reject an edge if
its ends already belong to the same component, including the virtual
root. After group `a`, write `s'=k-4-4a`. On its top physical row the
first `3s'+2` vertices belong to the root; all other vertices lie in
distinct nonroot components. This exact partition and the top marks
are sufficient for cycle detection in the next group.

Only four triple-row checks are needed. Reduce `s'` to 12 by removing
interior all-7 tile columns from the west margin. For `a>=3` reduce
the east span `k-s'` to 16 by removing interior all-448 tile columns.
These removals are in the homogeneous part at least six tile columns
from the ends; the clipped catalogue types and every transition word
are unchanged up to copies of a homogeneous word. For `a>=3` all
group rows and the preceding interface are already of bulk transverse
type. For `a=0,1,2` keep the east span exactly (4, 8, 12).
In either homogeneous margin the marked rows are straight horizontal
paths three sites apart, with unmarked pendant neighbors. Lengthening
them subdivides paths and adds leaves or isolated sites. On the incoming
west interface all duplicated sites are rooted, with only leaves of
the new group incident there; on the east they are distinct unmarked
frontier sites. No new connection between paths is introduced. At the
outgoing top the all-7 prefix therefore adds rooted vertices, and
the all-448 suffix adds singleton frontier classes. This proves the
partition induction independently of either margin length. The four
reduced widths are catalogue charts, not assertions about physical
upper witnesses on those small boards.

```
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.neighbor_diagonal
```

The remaining issue for this test is the **north closure**. The
transition moves four columns west per three rows north, and the
construction runs out of west margin before it covers the square.
It does not decide whether a complete equality candidate can avoid
a third expensive track.

## Can the transition reverse?

Define the west arm length of a tile row to be the length of its
initial `6,7,...,7` prefix, zero if its first tile is not 6. On
moving **north** in the star-free rows this length never increases.
This applies to arbitrary fills on either axis, without a cost cap.
Indeed, write consecutive tile masks as `(a,b)` above `(c,d)`.
At the west boundary `a=6` implies `c=6`, and `a=c=6,b=7` implies
`d=7`. At every subsequent position `a=b=c=7` implies `d=7`.
These are direct membership checks in all 130 certified plaquette
catalogues with northern tile-row index at least 3 (ten transverse
types, thirteen longitudinal types). Induction along the row proves
prefix containment, even when the rest of each row contains other
transitions. In particular a west arm which disappears cannot restart
farther north in these rows.

In the homogeneous bulk an arm also **cannot stop at one fixed
interior column for four consecutive rows**. Retain three columns of
tiles: the last 7, the first non-7, and its successor. For each pair
of neighboring rows retain only compatible quadruples on both seams.
Tie the westernmost marked site of each 7 to the perimeter root (its
omitted straight arm gives an independent forced path). Insert all
physical forced edges of these nine-site-wide rows, retaining the exact
frontier partition. The finite graph has 9, 5, 2 and 0 reachable states
after one, two, three and four rows respectively. Here both plaquette
origins must have bulk type `(6,6)`, and the left end of the window is
interior to the straight arm. The absence of a fourth row is an
exhaustive graph calculation, not a SAT timeout.

For the particular incoming diagonal state there is a sharper, but
conditional, finite graph. Allow up to eight arbitrary transition tiles
between 7 and 448, per-row deficit up to 15, and shifts from -3 to +3.
States retain the word and full rooted partition, translated only in
the homogeneous margins. On each axis there are ten reachable states
and ten edges. Peeling dead ends leaves only the cycle
`(16,16) → (3,8,264) → (33,32,384) → (16,16)`:
four columns west, three rows north, deficit 18. Its deficit rate 6
exceeds the asymptotic whole-square budget per tile row `36/7`.
The cap 15 does **not** follow for individual rows from that budget.
As a cross-check, allowing arbitrary words and costs in the two rows
above each of these three interfaces, and closing both homogeneous
margin lengths under additional steps, admits other westward words
but no stationary or eastward first step. This does not prove the
three-phase speed for every subsequent unrestricted row.

```
export PYTHONPATH=target/pb-python
python3 -B -m analysis.research_program.interface_order
python3 -B -m analysis.research_program.interface_drift 1 8 15
python3 -B -m analysis.research_program.interface_drift 2 8 15
python3 -B -m analysis.research_program.interface_lookahead
```

Thus a reflected turn of this same west arm cannot close the square.
An equality witness could still end the arm early or use a different
interior pattern. The unresolved question is how the components of a
terminated arm attach in the west fringe without violating the total
budget or the one-isolate condition.

## What happens when the west arm terminates?

**The diagonal band described above cannot extend to a one-gap upper
witness at any `k=39+14t`.** The obstruction is joint connectivity to
the east and west. With only the western four tile columns retained,
the graph can instead reach a terminated self-loop in two rows costing
four deficit, then pay zero per further row. This is a projection: its
eastern cut is open. It cannot be used as an equality construction.

For the full-width obstruction take the last diagonal group with
`s=k-4-4a>=12`. Its actual west length `s` is either 13 or 15. On this
frontier the row reads `6,7,...,7,16,16,448,...,448,192`; its rooted
partition is given by the group induction above. Every 448 in this
suffix must remain 448 in the next row north in bulk transverse type;
the final 192 must remain 192. These implications are checks on the
*unfiltered* positional quadruples. Consequently all freedom is in the
first `W=s+2` tiles. Keep **every** possible row there, consistent with
the plaquettes and the axis, and insert its three physical lanes into
the rooted frontier. Detect cycles including those using opposite
ends. Do not cap the cost or require a single transition per row.

Keep ten tiles in the mandatory suffix, including the east fringe.
This represents any longer suffix: inserting interior all-448 columns
subdivides its horizontal marked path and adds pendant neighbors, with
no new connection between paths. On the outgoing top lane those
inserted vertices are unmarked singleton frontier classes. The
catalogue type of an inserted bulk plaquette is unchanged. This
compression only uses tiles *forced* by the incoming suffix.

| `s` | states reachable | edges | states with west arm terminated | maximum further rows |
|---:|---:|---:|---:|---:|
| 13 | 14,707 | 18,391 | 12,491 | 9 |
| 15 | 74,436 | 93,927 | 63,310 | 12 |

Both axes give these counts. Repeatedly removing states without a
successor leaves nothing. The seed's physical tile-row index from the
north is `i=(k+3s)/4`. At least `i-6` more rows are required before
leaving the repeated bulk chart: this exceeds 9 for `s=13` (first
`k=53`) and 12 for `s=15` (first `k=39`). Even unlimited deficit does
not complete this particular band. The incoming state is a hypothesis;
the computation does not oblige an arbitrary square to realize it.

**A necessary inequality without the diagonal hypothesis.** Number tile
columns from zero. In a bulk tile row `i`, suppose a straight suffix
of masks 448 ending at the clipped east mask 192 starts at column `j`
(take the maximal suffix), with `2<=j<=k-7` and `6<=i<=k-7`.
Then **`i-5 <= 3(j-1)`**. Indeed its start cannot increase going north.
It cannot reach column 1: the only adjacent west mask would be 384,
making a continuous marked path between distinct west and east teeth.
Nor can it remain at any start for four rows. At a fixed start keep
columns `j-2,j-1,j` with the middle mask different from 448 and tie
the east end of each 448 to the common root via its own straight arm.
Insert every forced edge and retain the full partition. At `j=2` also
tie the actual west teeth. The reachable plateau states die after
height three at **every** position type: test `j=2,...,8`, with 8
representing all remaining bulk positions in range. Hence the `i-5`
rows through index 6 can use at most three rows at each of `j-1`
possible starts. This rules out a whole region of east-arm positions,
even with free marks everywhere to the west. Whether equality forces
an arm into that region is open.

```
export PYTHONPATH=target/pb-python
python3 -B -m analysis.research_program.fringe_suffix_bound
for a in 1 2; do
  python3 -B -m analysis.research_program.fringe_termination "$a" 4
  python3 -B -m analysis.research_program.fringe_termination "$a" 15 13 --closed
  python3 -B -m analysis.research_program.fringe_termination "$a" 17 15 --closed
done
```

## Can the exact deficit budget force the east arm?

Two full-square **band projections** pass the exact budget without a
forbidden east arm, on both axes and for **every** `k=39+14t`. No
diagonal or special incoming frontier is prescribed. The isolate is
at north distance 5. These are separate assignments, one for each
partition direction, not a common model of the full-square constraints.

Partition the tiles into bands three or four tiles wide (with a two-tile
band also used in the induction). Each band runs the entire length of
the square. All its physical catalogue plaquettes share the same masks,
and the actual forced graph in the band is a forest. No two of its
marked crop teeth are connected, even on opposite boundaries. **Every
component containing a mark either reaches a tooth or touches a cut
to another band.** The DP ties teeth to a common root, retains the
frontier partition, and records two bits per component: contains a mark,
and has touched a root or cut. A marked component that disappears without
the second bit is rejected. Another checker reconstructs the components
from the chosen physical marks and verifies the conditions directly.

* In the vertical partition the entire east-edge band is one forest from
  north to south. Its easternmost mask is **never 192** in rows
  `6,...,k-7`. Hence no east arm of the indicated kind exists there at all.
* In the horizontal partition the west and east teeth interact across
  the full width within each band. In the same rows the tile at column
  `k-8` is not 448. Any east suffix must then start at `j>=k-7`,
  outside the forbidden region.

The score counter is an **equality**, not a loose upper allowance. At
`k=39` the designated band deficits, in order, are

| Partition | First three tiles wide | Eight four-wide bands | Last four wide | Total |
|---|---:|---:|---:|---:|
| vertical | 20 | 19 each | 26 | 198 |
| horizontal | 46 | 16 each | 24 | 198 |

For the all-size check, each reference band has a repeatable slice at
longitudinal tile index 12. Repeating it restores the **same** labelled
frontier partition and component bits. It costs zero, except in the
horizontal north band where it costs one. Insertion is in bulk
longitudinal type, away from the fixed isolate and before the probe near
the east end. Extending all bands by `14t` tile steps therefore preserves
their requirements. In the transverse direction insert `t` groups before
reference band 15, each containing three bulk bands of width four and
one of width two. In the vertical projection the group costs
`3*20+12=72`; in the horizontal projection it costs `3*16+10=58`, plus
14 for the north band's length increment. All transverse fringe types
are unchanged. Thus both constructions realize
`198+72t = 5*k-1+floor((k-5)/7)` exactly. Bitset DP finds the required
costs and backtracks the slices; the replay checks the catalogue hash,
marks, components and cost for `t=0,1,2`. The self-loop and group rule,
not the number of sampled sides, prove the extension.

```
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.arm_budget_bands
```

The missing condition is compatibility **across the cuts**. Components
allowed to escape a band must in fact attach to one tooth in the
assembled square, and the plaquettes straddling each cut must also be
valid. The examples show that independent band costs, even exact and
with no enclosed rootless marked components, cannot prove arm forcing.
The [joined-band test](JOINED_ARM_BUDGET.md) enforces those connections
through the eastern three quarters and measures the extra deficit at
the final shared cut.
