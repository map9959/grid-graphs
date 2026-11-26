# A free band of arbitrary height cannot beat straight rails

Let the width be `n=3k+1 >=13`, with rail columns `0,3,...,3k`.
Between two ordinary rail rows insert **any** `H` free rows. All
upper rail terminals are tied to a common tree outside the band.
Suppose the resulting forced edges are acyclic. Let `M` count
free marks and let `m` count components meeting the lower rail
terminals but not the wired upper tree; several lower terminals in
one such component count once. Then

```
M + m <= H(k+1).
```

Straight vertical rails attain equality with `m=0`. This is a
rectangular inequality with *both* dimensions unbounded.

**Orientation.** A free mark in either end row must be in a rail
column, by diagonal exclusion against the adjacent ordinary row.
Each rail terminal consequently has exactly one edge into the band,
at its rail center, even if the free site there is unmarked. Orient
each component meeting the upper tree toward its upper contact
(two such contacts in one band component would close a cycle).
For a lower-only component choose one of its lower terminals as
sink. Root any remaining components arbitrarily. All upper rail
spokes point out through the top, and exactly `m` lower spokes
point out through the bottom.

**Certificate.** Use oriented star and acyclic `3 x 3` patch counts.
On each top/bottom star the outside neighbor is marked exactly in a
rail column. Consistency rows match endpoint marks and arrow direction
across edges, patch overlaps, and star-to-patch marks. The objective
counts marks plus downward exits on the last row. No assumption on
whether two unmarked free sites are in the same component is needed
by the relaxation. No reflection is used.

On each axis the fine labels distinguish the first and last four
sites (three for patch origins) and the three middle residues.
Marginal incidences are pooled by residues; the fine label determines
whether each local incidence exists and its coarse endpoints. Thus
adding three rows or columns only changes normalizations, not matrix
coefficients. Each normalization is the product of an affine height
count and an affine width count. The rational dual at `11 x 13`
has nonnegative slack in every column. At `(H,n)=(11,13),(11,16),
(14,13),(14,16)` its upper is respectively `55,66,70,84`. These four
coefficients of evaluation determine the entire bilinear polynomial,
which is exactly `H(n+2)/3`. This proves the bound for `H=11+3u`,
`n=13+3v`. For **any other or smaller height**, insert enough straight
rail rows at the wired end to reach a covered height. This adds exactly
`k+1` marks per row, creates no cycle and does not change `m`.

```
python3 -B -m analysis.research_program.seam_rank_chart 11 13 0 --replay
```

**Square consequence.** Suppose `n>=19`, the top row is fully marked,
and rows `2` and `n-7` (zero based) have exactly the rail profile.
Every other mark is free; row 1 is necessarily empty. Then the exact
maximum designated score is the [four-row comb score](FOUR_ROW_COMB_CAP.md).
In particular the distance between the prescribed profiles can grow
with the side, and no bottom bar is assumed.

To prove this, straighten the band between the two profiles. Together
with the top bar it had partitioned the lower terminals into a wired
class (possibly containing none of them) and `m` other classes.
Contract each class to a vertex, retaining the upper root also if
its class has no lower terminals. The bottom cap, glued to these
classes, is a forest. Tying all classes to the root needs `m` links,
each of which creates at most one cycle. Such a cycle must traverse
the free bottom cap between two distinct rail terminals (the links
themselves form a tree). This path enters at a rail center and must
turn to change columns. At its first horizontal edge either that edge
has a single marked endpoint or, if both endpoints are marked, the
preceding vertical edge has just one: three marks on the turn would
include a diagonal pair. If the turn is at the entering contact, its
predecessor is marked, so the two-horizontal-marks case is impossible.
In each case the sole marked owner is a cap site. Deleting that one
cap mark breaks the cycle and cannot make another. After at most `m`
deletions the cap can therefore be attached to the straight rails,
which gain at least `m` marks. The temporary links are only a way to
compute the all-wired terminal partition; the actual straight rails
plus upper bar realize it by a tree.

It remains to price six wholly free bottom rows with all upper rails
wired. The frontier transfer has identical full maximizer vectors up
to a shift of 63 at widths 19 and 49 (334 states). The ten base widths
`19,22,...,46` give the comb score after adding the fixed marks. Since
the transfer phase is the same, each extra 30 columns adds 63 to the
cap maximum. The comb itself meets both required profiles.

```
rustc -O analysis/research_program/double_cap.rs -o target/double_cap_free
target/double_cap_free 0 6 65 1
```

## Two profile rows suffice; no perimeter condition

In fact the comb is exact for every `n=3k+1 >=19` among forests
whose rows `2` and `n-7` have the stated rail profile. **No other
row, column or perimeter mark is prescribed.**

Here is the rank accounting that removes the top-bar assumption.
First, without any wiring, `M <= Hr`: use the same rectangular
certificate with unrestricted upper spokes and objective marks only
(`seam_rank_chart 11 13 0 --unwired --replay`). The same padding
argument applies. Now let `t` be `r` minus the number of seam
components meeting the `r=k+1` upper terminals; let `m` count
lower-only components. Wiring all upper terminals creates `t` cycles
in the sense of cycle rank. They can be broken by deleting at most
`t` seam marks: any path within the band between different upper
rail terminals turns, and the first horizontal edge or its vertical
predecessor has a single marked owner, as above. Deleting that owner
reduces cycle rank by at least one. The `m` previously lower-only
components remain separate from the wired upper tree; each still
has at least one lower terminal (its compulsory contact is not
removed by unmarking a free site). Apply the wired inequality after
deletion to get `M+m-t <= Hr`. Combining with the unwired bound gives
`M+lambda*(m-t) <= Hr` for every `0<=lambda<=1`.

Let `c_U,c_D` be the numbers of terminal classes of the two free
caps on their own. The upper cap together with the seam merges `t`
independent upper classes, or a cycle would already exist. Its lower
terminals therefore occupy at most `c_U-t+m` classes. The bottom
cap can merge at most `c_U-t+m-1` pairs, i.e.
`r-c_D <= c_U-t+m-1`. Consequently

```
M <= Hr + lambda*(c_U+c_D-r-1).
```

Price each outer cap **independently** by `10*marks+9*classes`,
using `lambda=9/10`. The frontier retains marked bits, component
partitions and a flag for contact with a terminal; pay the class
bonus once when its last representative leaves the frontier.
There is no external upper attachment for these cap computations.
Add both optima, subtract `9(r+1)` and add `10(H+2)r` for the
seam and its two prescribed rows (`H=n-8`). This bounds the
physical score in tenths. At widths `19,22,...,91` the total is
between the comb and the comb plus five tenths. For every larger
width, the stage vectors after physical columns 60 and 90 agree
*entrywise up to addition*: shift 300 at depth two and 720 at depth
six. The transfer is period three there and the final truncation is
unchanged. Thus the excess over the comb repeats after width 30
from width 64 onward. Rounding gives the upper, and the physical
comb gives the lower.

```
rustc -O analysis/research_program/annular_frontier.rs -o target/annular_frontier
python3 -B -m analysis.research_program.seam_rank_cost --two-profiles
```

**An unrestricted consequence.** In any forest let `e` count marks
off the rail columns in the two specified rows, and `f` count missing
rail marks there. Its score is at most `comb(n)+e+2f`. This holds in
each rotated or reflected frame. Remove the `e` marks and add the
`f` missing ones. Each insertion increases cycle rank by at most
three: if the site was isolated its first edge is free, otherwise
at least one incident edge was already present. Every new cycle can
be broken at a cost of one mark without changing the prescribed rows.
First deal with diagonal pairs. One mark in each such pair must be
an inserted rail mark (the old marking was acyclic); the square
through its unmarked horizontal neighbor has an edge owned by the
other, unprotected, mark. Deleting that mark lowers cycle rank.
Once no diagonal pairs remain, a turn of a cycle must be at a marked
site and at least one turning edge is owned by that site alone.
Not all turns can be at protected sites: between successive turns
along a horizontal segment on a prescribed row, distinct rail
columns have two consecutive unmarked sites and hence a missing
edge. Delete an unprotected turn and repeat. The repaired score is
at least the original minus `e+2f`, proving the claim. In particular
an improvement growing linearly over the comb would need linearly
many profile errors in **every** frame, irrespective of the bulk.

### Both cuts can move independently

For `n>=19` it suffices that **some row at depth at most six from the
top and some row at depth at most six from the bottom** have the rail
profile. The conclusion is the comb **upper**; the union of these
classes attains it by the original comb. The same applies to columns.

For either exterior cap let `a` be its height, `c` its number of
terminal classes and `b=r-c`. Its mark bonus over `ar` is at most
`k-1` if `c=1`; otherwise it is at most `floor((3k+7b-13)/10)`.
To verify, pad to six rows by inserting straight rails on the
terminal side. This changes neither `c` nor the bonus. In the
six-row frontier maximize `10*marks+7*c`, keeping the number of
completed terminal classes truncated at two as a separate state
(but paying every class in the objective). With one class the
maximum is `70k+57`, and with two or more it is at most `70k+54`.
The complete weighted vector including the truncated count repeats
after columns 99 and 129 with shift 700. Direct checks through width
130 cover the start and all ten residues in that recurrence.

```
python3 -B -m analysis.research_program.seam_rank_cost --six-cap-price
```

If both caps have at least two classes, apply the seam inequality at
`lambda=7/10`: the total bonus over `nr` is at most `(13k-26)/10`.
The comb's bonus is `floor((13k-23)/10)`, so rounding suffices.
If one cap has just one class, use `lambda=1`: the other cap pays
one for each merger, leaving at most `floor((3k-13)/10)` bonus when
it has at least two classes. Together with `k-1` this is the comb
bonus. If both are connected their combined net bonus is at most
`2(k-1)-k=k-2`. This argument leaves every site between the two
cuts free. In particular a construction beating the comb must
entirely avoid the rail profile in the first seven lines of at least
one side of **each** opposite-side pair.

### Even incomplete rails can be straightened

For `n=3k+1 >=22`, the depth allowance above is now **nine** on
each side. No change to the seam argument is needed: the entirely
free nine-row cap satisfies the *same* bonus bounds over `9r` as
the six-row cap over `6r`. The verifier scores each prefix by
closing its live terminal classes once each and tests all 39 widths
`19,22,...,133`; four are independently compared with direct final
closures. In particular the two maxima of `10*marks+7*c` at width
133 are 4487 and 4484. The complete normalized frontier at column
120 equals that at column 90, with additive shift 1000 for the
un-normalized score. Appending 30 columns adds exactly that amount
to each class maximum; pad any shallower exterior cap with rails.
The size threshold 22 keeps even the two deepest cuts distinct.

More importantly, the prescribed cross sections need not already be
complete. For a candidate cut at row `i`, let `q_i` count **only marks
off the rail columns** in rows `i-1,i,i+1` (omit any outside the
board). For an allowed top/bottom pair `i,j`, any forest of score `S`
satisfies

```
S <= comb(n) + q_i + q_j .
```

Delete these off-rail marks. Fill the missing rail centers in both
cut rows. At each insertion its existing lateral neighbors were
isolated: their two normal neighbors are unmarked, their neighbor
on the far side is off-rail, and the center had not yet been marked.
Other inserted centers are three or more columns away. Those lateral
edges therefore create no cycle, and the at most two normal edges
increase cycle rank by at most one in total (if neither was already
forced, the center initially was isolated). There are no diagonal
mark pairs after insertion. As in the turn argument above, every
cycle has an unprotected turn with an edge owned by that mark alone.
The cycle can be broken by deleting it. Each missing center thus pays
for its own possible repair; no charge for missing rail marks is
needed. The resulting marking has both complete profiles and at least
`S-q_i-q_j` marks. This proves the inequality, also after transposition.

Consequently, even a forest avoiding **every exact comb profile** in
the old seven-line test cannot improve on the comb if two opposite
cut neighborhoods have only rail-column marks, however many rail
marks are missing. At side 103 a score of 3647 requires a positive
off-rail count in at least one neighborhood of *every* such opposite
pair in both orientations.

```
rustc -O analysis/research_program/annular_frontier.rs -o target/annular_frontier
python3 -B -m analysis.research_program.nine_cap_price
```
