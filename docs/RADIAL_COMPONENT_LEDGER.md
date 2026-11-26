# An unrestricted square inequality with the boundary partition retained

For side `s=3k+1≥4`, let `I` be the number of marked sites of any
feasible forest. On its perimeter let `H` count vacant sites, `g` edges
with two vacant endpoints, `K` marked corners, and `c` distinct forced
components meeting the perimeter, counting isolated sites. Then

```
12I + 4H - 2g - 3K + 6c ≤ 4s² + 14s - 12.
```

Straight complete vertical rails at columns `0,3,…,s-1` attain equality.
This is an unrestricted inequality **with boundary terms**. Dropping
those terms does not prove the comb upper.

**Local certificate.** Take the four outer layers, so that the first
and fourth are the rims of sides `s` and `s-6`. Let `T` count the
outer three layers, and `c*` the number of components in the four
layers that touch at least one of those two rims. Primes refer to the
inner rim. The closed physical transfer gives

```
12T + 4(H-H') - 2g - 4g' - 3(K-K') + 6c* ≤ 48s-60.
```

The four blank sites just inside the reentrant corners can be
retained: they make only leaves unless two diagonally adjacent sites
are both marked, which was already impossible on the square. Thus
they do not join different physical rim classes. The sweep retains
forced-edge partitions, rejecting every redundant union. Each class
is flagged if it met either rim; pay its bonus once on disappearance.
Charge each missing rim edge on its second endpoint. No mark or gap
spacing is prescribed.

For sides 10 through 58 (step three) the integer maxima are exactly
`48s-60`. At both 61 and 64, in each of the eight straight half-arms
the complete current vector is dominated by the vector three
columns earlier plus 36. The intervening three column operators
are identical, with the same ordered frontier (the opening cut
stays live). The respective pump positions, zero based, are
`18,9,3,8,3,8,3,8`. Increasing side by six inserts three regular
columns in each half-arm. Corner operations and seam closure are
unchanged: in a straight column the four depths are scanned in
order, and only same-depth tangential neighbors cross its ends.
Monotonicity and translation of max-plus scores therefore cover
every larger side on the two progressions. The scalar increases by
at most `8·36=288`, precisely the increment of `48s-60`.

**Induction.** The shared rim alone is a forest with `g'` components:
it is a cycle with exactly `g'` edges deleted. Contract each of those
components before gluing the band to the inner square. The incidence
multigraph between their boundary-touching classes is a forest.
Hence `c ≤ c* + c' - g'`; some glued components may miss the outside
perimeter. Subtract the two square functionals and apply the local
certificate. The right side has difference `48s-60`. A full-square
frontier gives maxima 108 and 282 at the two bases 4 and 7.

**Equality classification.** Up to transposition the only equality
markings are the full vertical rails at columns `0,3,…,s-1` with any
subset of the noncorner top and bottom teeth unmarked. Each deletion
costs one mark, adds one hole, two missing bonds and two isolated rim
vertices, leaving the functional unchanged. There are exactly
`2·4^(k-1)` such markings. Direct base counts are 2 and 8.

For the induction, equality requires equality on the inner square.
Prescribe its rim from the preceding description, leaving each
optional bit free. Flag a defect if an inner tooth is missing or
if the candidate outer marking differs from the claimed family.
Subtract six for every isolated inner-rim nonrail vertex which is
also isolated in the band. Its inward neighbor is blank by the
induction hypothesis. Each such vertex is a separate glued
component not meeting the outer rim, so the subtraction is paid by
the gluing slack. Without this correction the defective branch can
tie. With it, the defective maximum is at most `48s-61`. The check
covers sides 10 through 100 directly, then sides 103,106,109,112
with six-column dominance in every half-arm. A size increase of
twelve preserves the prescribed phases and inserts six columns per
half-arm. Hence equality forces an undamaged inner rim and the
stated outer form. This classifies equality of the boundary
functional, not equality of the unrestricted tree score.

**Use in a larger square.** If the exterior including the shared rim
has `e` components meeting that rim, then `c≥g-e+1`, again by the
incidence forest. Thus without knowing the deeper partition one may
use `12I ≤ 4s²+14s-18 -4H-4g+3K+6e`. At side 103 with the outer
nine layers of the ordinary comb, the 85-square has
`H=112,g=56,K=4,e=28`. With its 1181 collar marks this gives 3646
even if all strictly interior marks change. The opportunity is to
bound the *joint* exterior functional `12T-4H-4g+3K+6e` at arbitrary
length while maintaining its real port constraints.

**A test on a hypothetical counterexample.** For score at least
`C(k)+1` the full-square slack is at most
`6k-12 floor((3k-13)/10)-6-4H+2g+3K-6c`. At 103 the first three
terms give 102. The established seven-gap bound, `K≤4`, and `c≥1`
imply `H≤30`. Consequently one vacant run cannot meet the immediate
neighbors of two different corners. Each corner requires at least one
vacant neighbor, so there are at least four vacancy runs and `g≤H-4`.
As at least one gap is necessary, `H≥5`, giving slack at most 90.

That slack pays **all sixteen** nested three-layer bills, down to
side 7: at each step it pays the nonnegative local scalar deficit
and exactly `6(c*+c'-g'-c)` additional units. Therefore some entire
annulus has local deficit at most five. On the physical 3646 comb
the sixteen bills are `31,65,0,…,0`, with zero gluing losses; at
133 they are `35,85,0,…,0`. This illustrates why a cheap annulus is
useful information but is not by itself an exclusion.

**Canonical rim.** Choose a maximizer with as many rim marks as
possible. A straight-side vacancy with both tangential neighbors
marked, at distance at least two from either corner, can be filled;
indeed fill all such vacancies at once without decreasing the score.
First clip marked inward sites one step tangentially from a hole's
foot. Two clips cannot flank the same selected hole: both would
already join the same forced rim path through the same inward foot.
The foot at any clipped hole now is isolated (a deeper donor there
was diagonal to the clip). Thus at least one independent new
inward edge per clip can be inserted. At every other selected hole
the foot is isolated or attaches solely through its deeper donor.
Delete that donor whenever adding the inward edge is redundant.
All tangential bonds at the selected hole already existed. The gain
is at least the joint rank of the inserted edges minus the number
clipped, hence nonnegative. A singleton vacancy at the corner itself
is impossible by diagonal exclusion. The remaining singleton holes
occupy at most eight corner-adjacent sites, and blocks of at least
two holes contain at most twice as many sites as missing bonds.
In particular a canonical 3647 example at 103 would have `H≤22`.

The corner normal form improves this to **16**. Among maximizers of
the rim count, maximize the number of marked corners, then the number
of marked favored ports (one arbitrarily chosen immediate neighbor
per corner). Testing all 4-by-4 corner masks against alternatives
with the same port bits and refining exterior connectivity leaves
189 masks. Every survivor marks the corner and exactly one neighbor;
if the favored port is vacant, the next site on that arm is vacant
too. Thus at most one singleton vacancy per corner remains, and
`H≤2g+4`. Apply the [six-gap canonical bound](RESIDUE_ONE_RIM_TARIFF.md).
If horizontal ports are favored, a nonfull horizontal side must
contain a missing perimeter bond. Replay the exact enumeration with
`python3 -B -c 'from analysis.research_program.rim_patch_dominance import cubes; cubes(4,4,True,True)'`.

There is a cheaper mark-only variant for iterating at many depths.
Let `G,G'` count missing rim bonds excluding those incident to a
corner. A separate transfer gives, for `s=3k+1≥61`,
`2T + H-H' -G-G' ≤ 8s-13` without any partition data. The
`concentric_price` driver sums this inequality over consecutive
three-layer reductions, rather than assigning the same holes a
new charge each time.

```
rustc -O analysis/research_program/radial_ledger_base.rs -o target/radial_ledger_base
rustc -O analysis/research_program/concentric_debit.rs -o target/concentric_debit
target/radial_ledger_base 4
target/radial_ledger_base 7
CONCENTRIC_RIGID=1 CONCENTRIC_ISO=1 target/concentric_debit 10 100 12 4 0 0 0 3 -1 -3
CONCENTRIC_RIGID=1 CONCENTRIC_ISO=1 CONCENTRIC_PUMP=1 CONCENTRIC_PERIOD=6 target/concentric_debit 103 112 12 4 0 0 0 3 -1 -3
target/concentric_debit 10 58 12 4 0 0 0 3 -1 -3
CONCENTRIC_PUMP=1 CONCENTRIC_PERIOD=3 target/concentric_debit 61 64 12 4 0 0 0 3 -1 -3
CONCENTRIC_PUMP=1 target/concentric_debit 61 64 2 1 1 1
python3 -B -m analysis.research_program.concentric_price
python3 -B -m analysis.research_program.radial_slack
python3 -B -m analysis.research_program.radial_projection
python3 -B -m analysis.research_program.canonical_rim
(cd lean && lake env lean GridGraphs/Geometry/RadialComponentLedger.lean)
```
