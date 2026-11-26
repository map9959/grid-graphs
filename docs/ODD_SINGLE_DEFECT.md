# A target forest on the open residue-two tail has exactly one charged atom

For **every** `n=35+42t`, suppose a forest attains the unrestricted integer
upper `U(k)`, `k=(n−2)/3`. Orient its forced edges toward a chosen corner.
In the physical residue-two stencil, in units of `1/1008`, **one star or
one patch has charge 72 and every other star and patch has charge zero**.
This is a necessary condition. It does not assert that such a forest exists.

## Why there is an exact defect budget

On this progression the unrestricted rational upper exceeds `U(k)` by
`1/14`. The corner and sink arguments in [the side-77 proof](SIDE_77_TEST.md)
apply without change: the corner multiplier and the eight-image averaged
star slacks depend only on the location type and the star. The period-three
type table is the same for every side here. Two corner components cost
`9/14`; an unmarked corner with one selected neighbor as sink costs `3/28`;
a noncorner marked sink costs at least `41/336`. Each exceeds `1/14`.
Thus all corners are marked, there is one component containing edges, and
every other component is an isolated vertex. Exactly one corner is a sink.
Consequently equality holds in the corner row. All other stencil rows
are identities, so the physical charges of the atoms in this orientation
sum to **exactly 72**. Although the stencil was averaged over symmetries,
these are integer weights on individual occurrences; no symmetry of the
forest is assumed.

The complete positive-weight list up to 72 is
`8,18,28,32,36,40,48,54,56,58,64,68,72`. Only 16 multisets sum to 72.

## Fourteen multiset exclusions valid at once for all sizes

Use period-six Cartesian buckets at depths six (stars) and five (patches),
with consistency pooled at depth two. Six records both parity and the
original phase. The eight-image averaged variable is a bucket sum, not
a common probability of each physical site. Multiplying by the number
of distinct transformed `(type,event)` pairs gives its total physical
count. Thus in each charge class the sum of these products equals the
prescribed integer multiplicity. Zero out forbidden sinks, unmarked
corners and unsupported charge classes.

All coefficients of this matrix are independent of `t`. A fine type
determines the coarse types of every constraint touching it. Reflection
on the middle residues is fixed since the side increment 42 is divisible
by six. Each one-dimensional fine count is either one, or `a+7t`
for a bulk phase with base multiplicity `a`. Each normalization is the
product of its two one-dimensional counts. The target score has Newton
coefficients `(440,1608,1176)` in `t`.

For fourteen profiles the saved rational multipliers obey the row signs,
give **nonnegative coefficients on every allowed column**, and yield
a negative constant RHS with both higher Newton coefficients zero.
The solver-free check is

```
python3 -B -m analysis.research_program.uniform_charge
```

The two remaining profiles in this relaxation are `(36,36)` and `(72)`.

## Why two half-defects are impossible on the odd tail

Return to **unaveraged integer counts** and choose the NW corner as sink.
Use one normalization per position type, count the marked stars, and
equate the two marginals at every star–star edge, patch–patch overlap
and patch–star incidence. At transitions where a phase has multiple
neighbors, sum over the connected components of the bipartite incidence
graph, so that both sides cover exactly the same physical pairs. A
zero-support marginal can delete its opposite terms by nonnegativity.
This test allows both charge 36 and charge 72 while deleting unsupported
events, so the deletions are necessary for either profile.

Reduce these equations modulo two. Quotient their column space by the span
of all remaining zero-charge atom columns. If the profile is `(36,36)`,
the RHS in this quotient must be the XOR of two charge-36 columns, even if
the two atoms have the same type. Gaussian elimination on 33,765 equations
gives zero-charge rank 7,655 and eight distinct charge-36 remainders.
No pair has the required XOR. Replay:

```
python3 -B -m analysis.research_program.odd_charge_parity --uniform
```

Only `t mod 2` is needed: the incidences and their coefficients depend on
the fixed near/far types, adjacent middle phases, and fixed reflection.
At side 35 the middle already contains more than a full cycle at each
depth. Adding 42 adds seven copies to each one-dimensional bulk count.
Adding 84 preserves every count modulo two, as well as its Cartesian
products. The target score is even throughout. Hence 35 and 77 cover
the two RHS parities for **all** `t`. A single charge-72 column *can*
have the required remainder; this does not exclude the final profile.

For contrast, in the attained even-side construction at 56, orienting
toward any corner gives two patches of charge `1/28`, at zero-based
patch origins `(1,51)` and `(2,52)` in `alternating_zipper.rows(56)`.
That construction realizes precisely the two-half-defect case excluded
here. This distinguishes the two rounding-tight tails by more than the
numerical `1/14` slack.

## What the single defect forces on the boundary

On every still-open side (`n>=119`), each side is fully marked at
distances `3,...,n-4` from its first corner. Read the first two sites
on the two sides out of a corner. The four bits must be one of
`0011,0111,1100,1101`. In particular the corner belongs to exactly
one of two long, straight boundary rods. The next ring, excluding
the boundary itself, has no marks: a mark there would be diagonal to a
marked boundary site and force a unit cycle.

These are checked *local* exclusions with a defect allowed anywhere
in the tested window, or outside it. Choose the tested corner as the root.
In a corner window at side 119, prohibit the four listed patterns and
check UNSAT. Separately require a hole somewhere at positions `3..11`
in the same window. To cover the rest of the straight side, use a
translated window and require a hole in one of three consecutive sites,
one per bulk phase. At distance at least 12 from both corners the
radius-five test has identical local types to that translation: the
star boundary depth is six, the patch depth is five, and `n mod 3` is
fixed. Rotation and reflection cover the other ends. The corner window
has fixed near distances throughout the progression.

```
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.odd_boundary
# root   3024 variables, 42998 clauses, s VERIFIED
# edge   2217 variables, 30307 clauses, s VERIFIED
# corner 3024 variables, 43001 clauses, s VERIFIED
```

Let `g` count perimeter edges with two unmarked ends. Each is located
in the two missing sites just after a corner. At least one is necessary:
otherwise the entire perimeter is a forced cycle. Enumerate the four
corner patterns, identify D4 images, and orient the perimeter component
containing the chosen root along its unique path to that root.
`python3 -B -m analysis.research_program.odd_frames` repeats the exact
parity/support test with those boundary atoms fixed, for every root.
There are **23 remaining D4 classes**, all with `g=1` or `g=2`; a
two-gap frame requires a star defect, not a patch defect. The straight
segments and their prescribed arrows are constant over each bulk bucket,
so the two RHS parity cases still cover every size.

This gives a useful integer target without orientations. Let `r` count
maximal connected runs of marked vertices (a single mark counts as a
run), and `I` count isolated vertices of the forced graph. The runs are
straight because diagonal marks force a cycle. There are `M-r`
marked–marked edges for `M` marks. Write `B` for the sum of marked
boundary incidences, counting corners twice. The forced edge count is
`4M-B-(M-r)=3M+r-B`. It also equals `n²-1-I`. The frame gives
`B=4n-4-g`; substituting `M=U` yields

```
r + I + g = 8n/7.
```

If `g=1` the whole perimeter minus that edge is one tree. Every
component left after deleting the perimeter vertices attaches to this
tree at most once. This is a structural restriction, not an exclusion
of the 23 classes.

### The exit costs the entire budget

Root the forced tree at any corner. All `4n-4` perimeter vertices are
in this tree. Each but the root has one outgoing edge. Exactly
`4n-4-g` of these arrows orient perimeter edges, leaving **`g-1`
arrows pointing inward**. Applying the star table to the four boundary
words gives minimum inward charge 72; admissible tangent and corner
arrows cost zero. The computation only uses the fixed near-end types
and the three bulk phases, so it applies to every still-open side.
`python3 -B -m analysis.research_program.perimeter_exit` replays it.

Thus with two gaps the unique defect is **exactly the inward exit
of the perimeter component not containing the root**. Every interior
star and every patch must have zero charge. With one gap no perimeter
star is charged: the remaining defect is either an interior star or a
patch. These constraints apply separately for every choice of corner
root and do not by themselves exclude either frame.

### Side 119: exclusion of every two-gap frame

The full `119 × 119` board cannot attain 4832 with two perimeter gaps.
Enumerate the four corner words with exactly two gaps and take one
representative per square symmetry (15 classes). Root at NW after
selecting the representative; the exit lemma holds for this rooting.
One CNF tests their disjunction: a selector pins the entire frame and
forbids the charged exit on the perimeter component containing NW.
All patches and all interior stars must have charge zero. Exactly one
boundary star must be charged. The arrow, turn-sheet and complementary
matching constraints are the necessary forest conditions described
above; no interior mark is fixed to the rail construction.

```
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.two_gap_board 119 600 all
# side 119 complete board; frame classes 15 variables 197288 clauses 2345643
# two-gap exclusion: s VERIFIED
```

CaDiCaL returned `s UNSATISFIABLE`; `drat-trim` checked the proof.
CNF SHA-256: `82f313bb31824e858dc46473bf25a6c312e89e862635d63fa4c7075e699c13dc`.
Thus a 4832 witness at 119 must have **one gap**. This finite exclusion
does not establish the same conclusion at every `35+42t`.

The same full-board test at **side 161** also excluded all 15 two-gap
classes (`361592` variables, `4302815` clauses, `s VERIFIED`).
Regenerate with `two_gap_board 161 300 all`; CNF SHA-256:
`59fb4cf04082b17e999543c65b359c0fb02de4e0989d9121c0aa82301230c3eb`.
Here `k=53` and `U=8792`, so only a one-gap frame could beat the
8791-site rail construction.

### Full-board decision test for the remaining eight one-gap frames at 119

Choose the open corner and its open side by a square symmetry so the
sole unforced perimeter edge is `(0,1)--(0,2)`. Each of the three
other corners independently chooses `0111` or `1101`, giving eight
representatives of the 64 physical one-gap words. The other 471
perimeter edges form one path through all 472 perimeter vertices.
Root at NW: the path fixes every perimeter arrow, regardless of
interior marks. No perimeter star may spend the defect, but an interior
star **or a patch** may. In particular one must not reuse the two-gap
restriction that forbids charged patches.

```
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.one_gap_board 119 1800
```

The full-board CNF (224627 variables, 2665205 clauses; SHA-256
`39aaf1594ce155e2530fd51b882f5b57dc0fea3020da9a8617d2b14edb5ede7a`)
uses a disjunction of the eight frames. The runner checks a satisfying
assignment by rebuilding its forced forest, or an UNSAT proof by
`drat-trim`. A solver timeout is not an exclusion.

**Completed: `P(119,119)=4831`.** The one-gap disjunction was UNSAT;
`drat-trim` returned `s VERIFIED` (25,047,108 resolution steps).
Together with the checked two-gap exclusion above this rules out 4832
without fixing an interior pattern. `side119` independently replays
4831 selected sites, 14159 acyclic forced edges, two components, and
a completed 14160-edge spanning tree with exactly 4831 full-degree sites.

### A uniform strip test for the two-gap exit

`exit_pump.py` runs along a complete side, retaining the previous two
mark columns, the connectivity partition of the frontier, which
horizontal arrows already point left, and the charged-exit category.
It checks every fully visible star (including its outgoing direction)
and every `3x3` patch. Only a single inward perimeter arrow may pay
72, and only outside the NW-rooted perimeter component. If the omitted
perimeter joins the lower corners of the strip, an external terminal
retains that connection during cycle checking. The bottom row's stars
are not charged since their lower neighbors are unknown.

After the fixed end layers, every transition depends only on column
modulo three. The checker compares **whole reachable-state sets** at
layers 42 apart in that middle interval. Equality allows insertion of
the same 42 updates arbitrarily many times before the unchanged suffix.
For example, on the frame `0211` (both gaps facing the north side),
rooting at NW gives the following result for **every `119+42s`**:
the exit on the north side must have column `2 mod 3` (zero based).

```
python3 -B -m analysis.research_program.exit_pump 7 119 0211
# repeat=(27, 69, 232), peak=232; zero=False, top phases=[2], short-end codes=[]
python3 -B -m analysis.research_program.exit_pump --screen 7 119
# uniform exclusions 0 of 15 frames
```

The second command checks all four sides and corner rootings and
intersects exit locations for roots in the same perimeter component.
Locations away from corners are only distinguished by phase; the
short sides retain exact offset. These location classes remain present
on enlargement. All 15 frames retain candidate exits. This rules out
a contradiction from **these projected exit-location tests alone**:
the four strip fillings need not agree where they overlap or extend
through the center. It is not a construction for the tail.

### Joining the strips eliminates five two-gap classes on the whole tail

For every `n=119+42s`, the two-gap representatives `0101`, `0103`,
`0121`, `0123`, and `0303` cannot attain the upper bound. This leaves
**ten of the fifteen** two-gap classes. The digits index `odd_frames.PAT`.

Use one induced annulus of width seven, including each corner square
just once. Marks and directed edges in an overlap are the same physical
variables. The turn-sheet constraints apply also along the inner fringe;
for each positive annulus decision an independent union-find checks
acyclicity on the whole annulus, and the verifier checks the star and
patch charges. Each negative rooted decision at the representative size
119 is re-solved and the resulting proof checked by `drat-trim`.

To extend the decision to every larger side, replace a straight piece
on **each** side, outside the corner overlaps. The signature of a piece
retains:

* both end interfaces (two adjacent mark masks and the left-going arrows
  of the current column at each end);
* the partition induced by the piece's edges on **all `2H` end vertices**
  together, where `H` is the strip width;
* zero charge or the phase of its single charged inward exit.

The entry column's vertical edges belong to the preceding piece, not
to both. Each step adds horizontal edges to the new column and vertical
edges inside it, rejecting a cycle. It checks the current column's
fully visible stars and the patches on the three visible columns.
The DP retains the left ports even after they leave the moving frontier.
Consequently a path through a different side which reconnects two
ports is not lost: gluing two edge-disjoint forests along specified
vertices creates a cycle exactly when their component identifications
make a redundant join. This depends only on their port partitions.
Sheet labels are auxiliary and can be reassigned on a glued forest.

The replaceable piece starts at column 12 in side-local coordinates.
Its transitions have period three. At width seven the complete
entry/exit relation after 36 columns equals that after 78 columns:
376 viable entry labels, 4,942 distinct end records and **60,417
entry/end pairs**. Equality is tested for each entry label, not after
forgetting the entry or checking only the cardinality. Monotonicity
is not needed: applying the same 42 updates to equal relations repeats
the equality indefinitely. The four pieces are disjoint. The unchanged
corners and the translated suffixes retain all local types, since 42
is divisible by three. Thus adding or removing these columns on each
side preserves the joint annulus decision in both directions.

```
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.joint_rim_test 7
# H=7: length 36 = 78 for ALL 376 entry labels; 4942 end records, 60417 entry/end pairs
# joint classes surviving 10 excluded 5 distinct rooted tests 56
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.joint_rim_test 8
# H=8: length 39 = 81 for ALL 1022 entry labels; 16554 end records, 239994 entry/end pairs
# joint classes surviving 10 excluded 5 distinct rooted tests 56
```

The width-eight test checks the same exclusions. For the survivors,
all four root choices separately admit a rim forest; the marks need
not be the same across different root choices, and no filling of
the entire interior follows.

### Four corner rootings on one common annulus

The ten survivors also pass the test with **one mark pattern shared
between all four roots**, at both widths seven and eight. This is
uniform for `n=119+42s`, `s>=0`.

For the straight-piece transfer, fix the two entry mark masks and
grow a single word of column masks. For each word retain the common
partition of the two ends and a relation `R` of possible (entry
arrows, end arrows, exit phase or zero). Four rootings may choose
four records from that **same** `R`. A union of relations from
different mark words before taking the four choices would permit
incompatible assignments. `shared_root_pump.py` instead keeps the
family of relations, dropping a subset only when another individual
word with the same interface marks and partition realizes its entire
superset. Extension by a fixed column preserves this domination.
Exact repetition of the undominated families thus permits replacement
of the straight pieces with all four rootings simultaneously. If
different entry-mask pairs first repeat at different layers, advancing
both equal families to the latest such layer preserves equality.

At the base width the SAT model identifies the mark bits of the four
rotated annuli, leaving each root its own arrows and exit. For each
frame, replay independently checks the common induced graph is acyclic
and each orientation obeys the edge, star, patch and charge conditions.

```
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.joint_rim_test 7 --shared
# H=7: shared-word relation 36 = 78; 107 entry mark pairs; peak 330 undominated records per pair
# shared survivors 10 additional exclusions 0
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.joint_rim_test 8 --shared
# H=8: shared-word relation 39 = 81; 245 entry mark pairs; peak 1037 undominated records per pair
# shared survivors 10 additional exclusions 0
```

Thus allowing different rim marks per rooting was not what kept these
ten cases alive. Their four orientations still need to arise from a
single forest through the untested interior.

### Depth of the connector and the full-board test at 203

In a tree there is a unique simple path joining the two disjoint
perimeter components without a perimeter edge. Its first and last
edges are normal to the boundary. For each corner root, the whole path
points toward the component containing that root. In particular, if
both components contain corners, each interior path vertex must admit
**both** directions along the path at zero charge on the *same* marks.
If one component contains no corners this reversal is not necessary.

`rim_connector.install` selects forced non-perimeter edges: degrees
are zero or two in the interior, and exactly one selected endpoint
is required on each perimeter component. A graph of maximum degree
two with just two odd vertices contains a path between them; the
rim forest rules out even disconnected cycles. The path is shared
between the four rootings. Its turns are actual grid turns, not
independently chosen direction counts.

```
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.joint_rim_test 7 --connector
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.joint_rim_test 8 --connector
# both: 10 UNSAT disjunction-free frame decisions, each s VERIFIED
```

No surviving frame can join the two components **within the eight-row
annulus**. This transfers to all `119+42s`: adding the connector test
asks for connectivity of the two designated perimeter components in the
rim, a property preserved by the shared-word replacement. In a rim
forest the two components, once connected, already determine the path
and its orientation to each root. Equivalently, one may inspect
connectivity between fixed representatives outside the replaceable
straight pieces; any boundary vertices omitted by the replacement are
on forced straight perimeter segments. Thus a whole-board connector,
if present, must visit a vertex at distance **at least eight** from
all four sides. This does not rule out such a deeper path uniformly.

At side **203**, the unrestricted-depth test also excludes all ten
frames. It uses one full-board NW rooting with the sole charged
perimeter exit, zero interior stars and patches, the tree/cotree
matching, and the explicit path. The reverse-direction constraints
apply only when corners occur on both components; reversal then
requires charge zero internally and 72 on the inward port at the
other endpoint. These are necessary conditions for the four rootings,
so UNSAT excludes the forest even without explicitly representing
four copies of the entire board.

```
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.interior_connector 203 600
# full square 203 frames 10 variables 664508 clauses 8183025
# all ten UNSAT, s VERIFIED
```

The CNF SHA-256 is `7ff44e7e0ba2f87b9f2d7035f665c7fad58be1166a5a920dfec39fa914ad5bd5`
(3,282,156 checked resolution steps). Combined with the five uniform
exclusions, a 13928 witness at 203 must have **one gap**. The rail
construction replay gives `(13927,41207,2,41208,13927)`.

### The two arms can meet in a zero-charge neighborhood through the center

Use the width-seven rim **together with** a five-column vertical strip
and a five-row horizontal strip through the center. Use one physical
bit for each mark, check acyclicity on this entire region, and test
all four corner rootings of the same forest. Require the connector to
use only vertices whose whole radius-two square neighborhood (clipped
at the board boundary) is tested. In particular its interior stars
and every `3x3` patch touching the path are checked, not just the
projection of its turns. Every fully visible interior star and patch
must have zero charge. The single paid exit is tested per rooting.

**All ten two-gap classes pass.** At 119 each replayed path reaches
depth 59 (the center). For example, in `0011` the path from `(0,59)`
to `(115,118)` has 174 edges and signed turn sum −1 quarter-turn.
Replay follows the unique marked-edge connector, verifies the actual
direction on every edge for each corner root, and checks the signed
turn sum against the clockwise boundary arc between the endpoints.
Class `0211` instead has a 168-edge connector with turn sum zero.

```
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.joint_rim_test 7 --connector --cross=5
# H=7 side: shared-word relation 36 = 57; 107 entry mark pairs
# H=5 core: shared-word relation 21 = 42; 117 entry mark pairs
# shared survivors 10 additional exclusions 0
```

This path-compatibility result holds on **every `119+42s`**.
To keep the junction centered, lengthen each half of a long corridor
by 21, not 42. Use pieces starting at longitudinal columns 12 and 69
at the base size; they avoid the junctions and corners. In addition
to the full port partition the transfer retains a second partition
using just the eligible path vertices (omit two rows on the hole side
of a rim piece, or on both sides of a core piece). For each common
mark word the four orientations still have to use the *same* record
of these partitions. The equalities above preserve both the full
forest and connectivity through eligible vertices. The periodic types
on translated arms agree since 21 is a multiple of three; the finite
junctions retain their local geometry. Replacing the pieces on each
arm and side thus retains a compatible connection as the square grows.

This supplies a forest on a cross and rim, **not** a filling of the
four intervening regions. In particular it coexists with the
full-board impossibility at side 119. A tail exclusion needs information
not enforced by this common-path neighborhood test.

### Filling the NW quadrant breaks the cross connector at 119 and 161

Keep the connector in the same radius-two-tested part of the rim and
cross as above. Now simultaneously solve for its marks and the entire
missing NW square. Thus the extension can choose *any* admissible cross
witness; UNSAT does not mean merely failure to extend one frozen model.
All four roots use the same physical enlarged domain (rotating the old
CNF would incorrectly give different quadrants to different roots).
All fully visible patches and all complete stars, including across the
old interface, are tested; oriented edges and cycle checks include the
new sites. The connector edge variables still range only over the old
path region.

```
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.quadrant_extension 119 0 --all
# side 119 added quadrant sites 2500 ...; ALL UNSAT VERIFIED
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.quadrant_extension 161 0 --all
# side 161 added quadrant sites 5041 ...; ALL UNSAT VERIFIED
```

`drat-trim` checked the disjunction of all ten frame classes at each
size; CNF SHA-256 respectively
`3ff122906203eec82237ecea0ef906f2ed78f10ddbe6f5f6a1a8a8f7fec5be57`
and `e1366a0df65a865fd3acce8425e25883b1376b6d6a1013434c429557872620b1`.
The displayed clause count is before the guarded frame assumptions.
As a control, `119 0 --all --free-path` removes the required connector
and yields a replayed partial forest for `0013`. The contradiction is
not an unrestricted quadrant exclusion.

The two outcomes agree across one `+42` step. This does **not** certify
the full quadrant test for arbitrary enlargement: the inserted band
has to cross the filled square too, so its port set grows. To test the
scope of the known transfer, `203 0 --seams=12` adds 2704 quadrant
sites but leaves the old replaceable pieces unobstructed in both axes.
All ten frames have verified connectors in that domain, each reaching
depth 101. In particular, extending just the fixed blocks outside those
seams does not reproduce the full quadrant contradiction.

### Allowing the connector to enter the filled NW quadrant at 119

With `--domain-route`, the selected path can use **every non-perimeter
edge** in the induced union of the cross, rim and full NW quadrant,
including edges on the fringe facing an unfilled region. Only the
eligible edge set changes: the four rootings still share the marks,
the connector still joins distinct perimeter components, and all
complete interior stars and patches must have zero charge. In contrast,
`--free-path` drops the connection requirement itself.

```
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.quadrant_extension 119 0 --domain-route
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.quadrant_extension 119 0 --domain-route --all
# ALL UNSAT VERIFIED
# p cnf 182879 3471437
```

`drat-trim` verified all ten individual exclusions and the disjunction;
the combined CNF SHA-256 is
`2c22be06c54412e6bbee49eeced6c70a6a665ba8fe7fb077eae6e6e388670393`.
Thus the side-119 quadrant obstruction does not depend on confining
the route to the old cross. This test does not allow transit through
the remaining three holes and establishes no repetition with size.

### A fixed NW band and a junction anchored at (59,59)

Backward trimming the combined side-119 quadrant proof (`drat-trim
-c`) retained 32,118 of 3,471,437 input clauses. Of the 2,500 added
mark variables, 1,260 occur literally in the core, reaching layer 21
from the boundary of the added square. These are not a minimal support:
there are auxiliary variables too. Instead of dropping clauses from
that proof, generate and independently check a fresh domain.

In zero-based coordinates keep the width-seven rim, rows and columns
57 through 61, and the outer 12 layers of the square `[7,56]^2`.
Leave its middle `26x26` square absent. At every larger size keep the
same NW square and the **same** junction coordinates. Only the east
and south arms lengthen. Permit every edge of the induced region for
the connector except perimeter edges. All ten frames together are
UNSAT at 119 and independently at 161; the width-eleven control at
119 has a replayed `0312` forest (182 connector edges). No monotonicity
in width is assumed, since new sites can also open new routes.

```
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.quadrant_extension 119 0 --domain-route --anchor=59 --band=12 --all
# ALL UNSAT VERIFIED, CNF SHA-256 27d36641589f3aab6a56fa3090aeefbecc7b436b569d419c96196683915285ef
# substitute 161: ALL UNSAT VERIFIED, 4cdf1e5e0d6b501a3b85b6dd0449bb46e81c56c59c53fce6c141b6a8dcd860d9
python3 -B -m analysis.research_program.anchor_band_transfer
# H=7 side: shared-word relation 36 = 78
# H=5 core: shared-word relation 21 = 63
```

For every `119+42s`, no upper-target forest can have its two-gap
connector contained in this anchored region. To shorten a larger
candidate, cut the three horizontal corridors east of the junction
starting at column 69, and the three vertical ones south of it starting
at row 69. The six replaceable pieces are disjoint and avoid every
junction, including those at the far rim. The two outer pieces in each
direction are straight perimeter strips; the middle one has width five
and transverse start 57. Boundary types on translated pieces agree by
D4 and the clipped-coordinate period three. The shared-word relations
above preserve all four orientations on common marks, exit charges,
and the entire end-port partition. Thus gluing preserves acyclicity
and the connection between the two perimeter components. Their gaps
are in the unchanged corner neighborhoods. Each shortening removes
42 on both axes; iteration would give a forbidden connector at 119.
This proves a **route restriction**, not an unrestricted frame exclusion:
a connector can escape through any of the omitted regions. Moving
the junction back to the midpoint as the board grows is not justified
by this transfer.

### One-gap defect location exclusions

On every `119+42s` one-gap target, rotate/reflect the open corner to NW.
The patch origin is the upper-left cell of a `3x3` box. **No patch
with origin in `[0,22]^2` can be the defect.** In the same square the
only possible charged stars are `(2,5),(2,11),(2,17)` and their
transposes. This is a necessary list; even these six are not certified
realizable on a full board.

```
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.one_gap_defect_sites 8
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.one_gap_defect_sites 16 --open
# root 0 s VERIFIED stars [(2,5),(2,11),(2,17),(5,2),(11,2),(17,2)] patches []
```

Reroot at the corner being tested. Only edges of the connected perimeter
path can reverse when the root changes; every interior star and every
patch retains its charge. The corner clauses therefore may prescribe
the perimeter arrows and the two outer rings from the frame. At an
open corner the path on the far side of the gap points *away* from
the corner. For a closed corner both local branches point toward it.
Frame choices beyond the window have no other effect. At radius 16
the tested corner domain is `[0,41]^2`, independent of side; its
charge tables depend only on fixed near distances and residues modulo
three. Transposition exchanges the two possible open-side choices.

The radius-eight replay also screens the closed corners, long sides
and bulk. Globally, a star must be at normal distance **two** from
a side and at longitudinal coordinate `2 mod 3`. A patch must have
both origin coordinates `1 mod 3` and its origin must be at least four
steps from each boundary of the `(n-2)`-by-`(n-2)` patch-origin grid.
The bulk test screens three consecutive offsets in each direction;
the side test screens depths 0 through 14 and three longitudinal
phases; the corner test covers the remaining pairs of near offsets.
Windows can translate by multiples of three once the clipped boundary
types stabilize (depth six for stars, five for patches). For coverage
near the transition, take the first candidate of a translated triple
at the tested coordinate itself rather than requiring a fixed tiling
of triples: equivalently translate the *individual* representative of
the matching phase, retaining its eight-site halo. Reflection of a
star coordinate uses `n-1-i` and of a patch origin uses `n-3-i`;
these preserve the respective allowed residues. No induction from a
finite full-board UNSAT result is involved.

For each window the solver enumerates possible sole-defect flags,
then `drat-trim` checks the CNF forbidding the resulting list. Other
sites need not form a full-board forest in this relaxation. In
particular the test does not eliminate the bulk patch phase.

### One physical patch across all four rootings

Intersect the four rooted GF(2) quotient tests on the **same origin and
the same nine mark bits**. For every one-gap frame and both tail parities
the following necessary rule holds, in addition to the window exclusions:
**`i+j` must be odd, and exactly one of the four corners of the `3x3`
patch is marked, with no other mark in it.** There is no further loss
from intersecting the four root tests compared to using NW alone.

```
python3 -B -m analysis.research_program.common_patch
# all eight frames at 119: 2640 -> 2640 (660 sites times 4 masks)
# all eight frames at 161: 5104 -> 5104 (1276 sites times 4 masks)
# same physical bucket/mask lists for every frame and parity: True
```

Here `i,j` denote zero-based origins in the normalized frame with the
open corner at NW. The patch-origin grid has side `n-2`; rotate the
origin on that grid and the mask on its own side-three grid. For each
root require the rotated event column to equal its target modulo the
span of its allowed zero-charge columns. This is a necessary parity
test, not a joint construction. Among previously admissible coordinate
phases (`1 mod 3` on each axis, margin four), there are four bucket
choices per axis: the two margins and the two period-six bulk phases.
The code checks all sixteen pairs even before clipping the open-corner
box. Increasing `n` by 84 preserves the two parity RHSs, bucket action
and coordinate parity, and introduces no new bucket. Applying the
open-corner exclusion then gives the reported physical counts.

### Mask-conditioned neighborhoods

At a closed corner place the corner at NW in local coordinates. Among
the 24 parity-eligible origins with both coordinates in `[4,22]`,
**mask 1 (only the NW cell of the patch marked) is impossible at
every origin**. In addition, mask 4 is impossible at `(4,7),(4,13)`,
and mask 64 at `(7,4),(13,4)`. Both closed corner words give the
same list. At the open corner all 96 pairs are excluded, consistent
with the earlier location-only exclusion. Rotate the masks along with
the coordinates at other corners.

```
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.patch_neighborhood
# open words 0,2:     each 0 replayed, 96 checked exclusions
# closed words 1,3:   each 68 replayed, 28 checked exclusions
# straight side:      28 replayed, 0 exclusions
# bulk:                8 replayed, 0 exclusions
```

Fix all nine marks, charge 72 at the designated origin, and charge
zero at every other fully visible patch and star. Impose the forced
perimeter arrows and the primal/dual edge matching. Each negative
group is checked by `drat-trim`; on each positive model the script
recomputes the physical charges and tests for forced cycles on the
interior of the window. A bulk model is only a local extension.

In each direction the window is `[0,40]` for a near coordinate,
or `[45,82]` translated with one of the two period-six representatives
61,64 for a distant coordinate. The code checks the forward and
reflected clipped types for both `119` and `161`. Beyond these,
fixed corner distances and bulk translations by multiples of six
preserve the types (as does reflection on the patch-origin grid).
Thus the mask exclusions apply to both tail parities, without claiming
that a locally feasible pattern extends through the full square.

### A one-gap charged star must be on a side incident to the open corner

Normalize the open corner to NW with the gap on its north side. On
every `119+42s`, a charged star **cannot** be on the depth-two row
along the south side or the depth-two column along the east side.
Thus of the four boundary sides allowed by the local depth-two test,
only north and west remain. This concerns a star defect, not a patch.

Use the full eight-row rim and one common forest. Once its perimeter
is a single forced path, rerooting from NW to any other corner reverses
only edges on that path. Hence all non-perimeter arrows, marks, and
patches are identical and the physical charged star is unchanged.
The checker solves for a NW orientation, rebuilds the forest by
union-find, changes the perimeter arrows to each of the four rootings,
and checks all edge orientations and charges in each. All complete
patches and all other complete stars have charge zero. No assumption
is needed about how an interior subtree reaches the perimeter.

```
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.one_gap_star_rim 119 8
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.one_gap_star_rim 161 8
python3 -B -m analysis.research_program.joint_rim_pump 8 --one-gap-star
# H=8: length 39 = 81 for ALL 1006 entry labels; 15540 end records, 232598 entry/end pairs
```

For each of the eight frames, on each side length, `drat-trim` checked
the disjunction of the excluded south/east locations. Each of the
two longitudinal phases (2 or 5 mod 6, measured clockwise) has a
replayed north and west example per frame; this does not assert that
every individual site of the phase works. Sites less than five steps
from a corner are already excluded by the corner window.

For the all-size step replace a straight middle piece starting at
column 12 on each side in its local coordinates. The transfer forbids
non-tangent perimeter arrows and remembers whether a **depth-two**
star spent 72, with its phase mod three; every patch is zero. The
whole entry/exit relation, including both mark/arrow interfaces and
the partition of all ports, agrees at lengths 39 and 81. In checking
exclusion of a whole side no distinction between phases 2 and 5 is
needed. Shortening preserves the charged side, its forced perimeter
directions and global rim acyclicity. The corner neighborhoods are
unchanged; replacing a forest piece permits reassignment of auxiliary
turn sheets along the glued forest. The three-periodic transition
then gives the same relation after any number of 42-column insertions.
The second base replay is an independent check on the other tail parity.

### Filling the quadrant at the open corner eliminates one star phase

Keep the eight-row rim and fill the entire NW quadrant, including the
midlines. Search over the rim marks as well as the new sites; a failed
extension is not merely failure for one frozen rim model. Test the eight
frames separately with the open corner normalized to NW. On both 119
and 161, inside that quadrant a depth-two star on north or west passes
only for longitudinal distance `5 mod 6` from NW. Both phases still
have partial forests outside the filled quadrant. Each positive group
has at least one independently replayed common forest for all four
rootings, not a witness at every site in that group. Every negative
frame decision was checked by `drat-trim`.

```
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.one_gap_star_rim 119 8 --nw=60
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.one_gap_star_rim 161 8 --nw=81
```

There is also a **uniform bounded-distance exclusion**. Discard the
rest of the rim and use just the fixed `83x83` NW window, testing
longitudinal distances up to 80 with a two-site halo. The four-root
replay retains perimeter arrows even on the artificial fringe. Only
the NW corner word and the NW-rooted perimeter directions enter the
exclusion; they are identical here for all eight frames. The other
three roots change arrows only on the perimeter path.

```
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.one_gap_star_rim 161 8 --nw=81 --corner-only
# 0111 s VERIFIED
# repeat at 203: identical CNF, 54440 variables, 1121163 clauses
# SHA-256 e07d0f0455669020efb59ba83d2c5c5e11a576b9977d952efab523d668cff3c9
```

The side increment 42 preserves all clipped stencil types in this
window: far ends are beyond both stencil depths even at 119, and
reflected bulk coordinates retain their phase modulo three. On west
the program uses clockwise coordinate `n-1-i`; because `n-1=4 mod 6`,
residues 2 and 5 each map to themselves. Thus at **every `119+42s`**
the defect cannot be `(2,l)` or `(l,2)` for `l=8,14,...,80`.
This extends the earlier open-corner window exclusion beyond distance
22. It is not an exclusion at unbounded distance, nor a proof that
the growing quadrant has the same decision at every size.

### Both quadrants adjoining a phase-five star

For a north-side star, take the union of the eight-row rim and all
rows `0..n//2`; for a west-side star use columns `0..n//2` instead.
The midline belongs to a single induced graph. Marks, forced edges,
and orientations on the two quadrants must agree, including across
their interface. The only nonzero charge allowed is the specified
depth-two star at longitudinal distance `5 mod 6` from NW.

At 119 **every** distance `5,11,...,113` passes for each of the eight
frames, on both sides: 152 verified frame/location pairs per side.
For each model the replay checks the requested frame and defect site,
reconstructs forced edges and excludes cycles by union-find, changes
the perimeter arrows for each of the four corner roots, and recomputes
the charges of every fully visible star and patch. The two quadrants
in one replay share one forest; different location tests can use
different forests.

```
export PYTHONPATH=target/pb-python
for side in north west; do
  python3 -B -m analysis.research_program.one_gap_star_rim 119 8 --half="$side" --each-site
  python3 -B -m analysis.research_program.one_gap_star_rim 161 8 --half="$side"
done
```

At 161 each of the eight frames passes on each side, with a replay at
`(2,155)` for north and `(5,2)` for west; this run does not enumerate
each of the 26 eligible distances. The domains contain 8,908 and
15,481 vertices at 119 and 161 respectively. Thus even simultaneous
extension across both adjoining quadrants does not explain the
full-board exclusions at those sizes or establish a tail formula.

### Three quadrants: the southeast quadrant distinguishes the extensions

With the open corner normalized to NW, keep the full eight-row rim
and the two quadrants adjoining the defect side. Fill either of the
two remaining quadrants, midlines included. Each solve ranges over
all compatible marks on the resulting single domain. For all eight
frames the result depends on which quadrant is added:

| Defect side | Third quadrant admitting a common forest | Third quadrant excluded |
|---|---|---|
| north | SW | SE |
| west | NE | SE |

This holds separately at **119 and 161**. Each negative decision
includes all eight frames and every eligible phase-five distance
(19 at 119, 26 at 161). `drat-trim` verified all four proofs.
At 119 the positive forests replay with defects `(2,71)` and `(95,2)`
respectively; at 161 the sites are `(2,155)` and `(83,2)`.
Replay checks the whole regional forest and all four corner rootings.
As a control, the rim plus just the `60x60` SE corner at 119 admits
both defect sides for every frame (`--third=far --se-only`).

```
export PYTHONPATH=target/pb-python
for n in 119 161; do
  for side in north west; do
    for third in near far; do
      python3 -B -m analysis.research_program.one_gap_star_rim "$n" 8 --half="$side" --third="$third"
    done
  done
done
```

CNF hashes (SHA-256, north then west):

* 119: `697a623a2e87b97f7048657747ba69e477262df6f43e2111855b2db2e946f2be`, `0b3659c73d75ad813cc827d6bd46669b57ede9015ec13de4d8b1987ad5179d94`
* 161: `c6e1abcffc50f93f18dcd60f8e84f72c58d1ce633cd207e7c26fcb4297b4665f`, `dd78af153a0ad7501aa62053413f76f446699a5af9c137274e6292ac8ce448db`

The contradiction persists across this `+42` step. No transfer for
the growing filled quadrants is established by these finite checks.

### A visible patch defect fails in every three-quadrant domain at 119

Keep the eight-row rim and fill all but one quadrant, retaining both
midlines. Require the patch to lie **entirely** in this induced domain.
The three quadrants share the physical mark and edge variables. The
NW-root orientation is necessary for a common forest under all four
rootings, so its checked impossibility suffices; no assumption of
independent quadrant fillings or of a fixed cross witness is needed.

For each omitted quadrant and all eight one-gap frames, the surviving
patch origins/masks were UNSAT. Removing the location, parity, and
corner-mask filters still gave four checked UNSAT proofs: 10,716 fully
visible origins per domain, sole charge 72 on one patch, all other
complete patches and stars at zero charge. This test does not require
a patch with origin in the unfilled region to be visible. It does not
settle the growing three-quadrant domains at other sizes.

```
export PYTHONPATH=target/pb-python
for q in NW NE SW SE; do
  python3 -B -m analysis.research_program.one_gap_star_rim 119 8 --patch-omit="$q" --any-patch
done
# each: s VERIFIED; origins 10716 excluded frames 8 of 8
```

Combined-frame CNF hashes, SHA-256:

* NW `e3e3d8bcda9ff56c3b0998ad53249d2c3fdb867b2aa23173eab79128b4e90cd7`
* NE `f8907d6afe8c3429ab4b10c6a66cb709fa30d0437d6304bec8d41c28469ac36e`
* SW `096b98c449d9dd8034d57963b3351ce3cff9704efd46fd4e690f914ff535b52e`
* SE `498834f219b95adb04d19d4de52770004adbdbed455839a322a9981063a368d8`

### Fixed-width test of the southeast proof cores

`drat-trim -c` rechecked the four full three-quadrant proofs and
retained 153811/158689 original clauses at 119 (north/west), and
295348/323972 at 161. Map clauses containing only mark bits to signed
physical coordinates. Among simultaneous row/column deletions of length
42 starting at `15,21,...,99`, the most literal-for-literal overlap
starts at 57: 44855 common clauses for north and 48561 for west.
Each intersection **is satisfiable**, with its assignment checked
clause by clause. This comparison does not identify auxiliary variables.
Keeping the rim but opening 43-wide seams centered on the cut (start
parameter 36) also admits all eight frames at 119.

To retain orientation and global rim acyclicity, make fresh CNFs.
For north, keep the eight-layer rim plus the first `B` rows and last
`B` columns. For west, transpose that region but retain the original
frame and gap. This is a fixed-width version of the three-quadrant
geometry. At `B=56`, the north and west 119 CNFs both exclude all
eight frames (`s VERIFIED`), while at 161 every frame has a replayed
common forest: examples have defects `(2,107)` and `(77,2)`. Thus
the **fixed-width contradiction fails under `119 -> 161`**.
Even `B=60`, which at 119 covers the *whole* three-quadrant test,
admits all eight frames at 161 (north `(2,23)`, west `(5,2)`).
By restriction this rules out a uniform contradiction for this nested
band family with any `8<=B<=60` and the same phase-five requirement.
It says nothing about a different domain or a new interface invariant.

```
export PYTHONPATH=target/pb-python
for s in north west; do
  for n in 119 161; do
    p=target/star_rim_${n}_8_0_0_${s}_far_${s}
    target/drat-trim/drat-trim "$p.cnf" "$p.drat" -c "$p.core"
    python3 -B -m analysis.research_program.one_gap_star_rim "$n" 8 --half="$s" --third=far --core-map
    python3 -B -m analysis.research_program.one_gap_star_rim "$n" 8 --half="$s" --third=far --band=56
  done
  python3 -B -m analysis.research_program.star_core_transfer "$s"
  python3 -B -m analysis.research_program.one_gap_star_rim 161 8 --half="$s" --third=far --band=60
done
```

### Side 161 exact

See also the uniform patch exclusion below; the finite proof here
independently decides both kinds of one-gap defect at 161.

The pending full-board one-gap proof has passed `drat-trim`:
`s VERIFIED`, 116,345,311 resolution steps. Its eight-frame CNF
has 412,115 variables and 4,899,689 clauses (SHA-256
`68f2f982b6b2b2dee47be984bb57479f80b703c27859447d256b5e4d04e2055c`).
Replay with `PYTHONPATH=target/pb-python python3 -B -m
analysis.research_program.one_gap_board 161 3600`. Together with
the checked two-gap exclusion and rail replay
`(8791,25919,2,25920,8791)`, this proves **`P(161,161)=8791`**.

### Seven layers exclude the one-gap patch case on the whole open tail

Normalize the gap to the north edge by NW. If the sole 72 units are
spent on a patch, then **every star has charge zero** in the NW rooting.
Restrict to the L formed by rows 0 through 6 and columns 0 through 6.
Only wholly visible patches and complete stars are charged. Allow either
one arbitrary 72 patch in the L **or no visible defect**; the latter
is essential if the charged patch lies elsewhere or crosses the inner
fringe. Do not impose the earlier patch parity, location, or mask filters.

Source of the region: `drat-trim -c` on the side-119 any-patch proofs
retained 7668,27690,8554,15264 input clauses for omitted NE,NW,SE,SW.
The physical mark variables used by those cores were concentrated on
the north and west arms (1889,1617,1990,2277 distinct sites respectively).
They only suggest a geometry, not a proof that auxiliary constraints
can be discarded. Fresh width-seven CNFs with optional defect are UNSAT
for all eight frames at both 119 and 161. At width five all frames
admit zero-charge L forests. Replay:

```
export PYTHONPATH=target/pb-python
for q in NE NW SE SW; do
  p=target/star_rim_119_8_0_0_rim_base_patch_omit_${q}_any
  target/drat-trim/drat-trim "$p.cnf" "$p.drat" -c "$p.core"
  python3 -B -m analysis.research_program.one_gap_star_rim 119 8 --patch-omit="$q" --patch-core
done
for n in 119 161; do
  python3 -B -m analysis.research_program.one_gap_star_rim "$n" 8 --patch-omit=SE --any-patch --patch-band=7 --outside-ok
done
python3 -B -m analysis.research_program.patch_band_transfer
```

At 119 the fresh CNF SHA-256 is
`78b77bec562284a13216c44623de71b2443e0c9d4d695ed10789f899f26652e2`;
11975 variables, 220800 clauses, `s VERIFIED`.

**Why shortening works.** In each arm take the straight piece beginning
at longitudinal column 12, transposing the west arm. The north perimeter
arrows point forward along the piece; the west ones point backward.
`joint_rim_pump.kernel` checks the patch charges of the three consecutive
columns, all complete star charges, and the forced forest transitions.
It enforces the stated perimeter direction and records whether the
piece spent zero or 72. Its relation keeps both mark-mask interfaces,
orientations of the horizontal cut edges, and the entire connectivity
partition on the two ends. The partition makes acyclicity after gluing
independent of the chosen representative of a piece. No turn-sheet
boundary data are needed: after gluing, orient the forced edges as
specified and propagate turn sheets on the resulting forest.

For **each direction**, the full relation at length 39 equals that
at length 81 (236 entry labels, 3672 end records, 57162 entry/end
pairs). These are set equalities, not equal totals. All interior step
types repeat with period three, so the equality iterates by 42. The
two pieces are disjoint; the NW junction is fixed and the NE and SW
end blocks translate with their respective board ends. Frame bits
and directional boundary conditions are unchanged. The clipped near
distances and the period-three bulk and reflected coordinates determine
all local types, including across the joins. Thus any larger target
forest with a patch defect would restrict, then shorten on both arms
to a forbidden width-seven L at 119, preserving the visible budget.

Consequently on every `119+42s` a **one-gap target must have a star
defect**. With the earlier rim exclusion it must be at depth two on
north or west. This leaves stars and two-gap connectors open; the
seven-layer proof alone does not decide the score.

### Exact depth-two star test on the seven-layer L

For the global, orientation-free run and isolate counts implied by
these results, see [the run ledger](RUN_LEDGER.md).

For the same L, now charge exactly one star on row 2 or column 2 and
set every complete patch and every other complete star to zero. Test
each previously eligible distance `ell=5,8,...,n-6`, measured along
its arm from NW, in each frame. On **the L alone**, precisely `ell=8`
is excluded, on either arm, for every `n=119+42s`. This is a limitation
of the L test: for example, larger corner squares already rule out
some L-feasible distances. These partial forests need not extend.

```
export PYTHONPATH=target/pb-python
python3 -B -m analysis.research_program.one_gap_star_rim 119 7 --star-L
python3 -B -m analysis.research_program.one_gap_star_rim 161 7 --star-L
python3 -B -m analysis.research_program.patch_band_transfer --star
```

At 119 the verifier replays 36 of 37 distances per arm per frame;
at 161 it replays 50 of 51. Union-find checks acyclicity; each of four
rootings of the common marks is checked edge by edge and charge by
charge. `drat-trim` checks the remaining distance on both arms jointly
for each frame at each size.

The oriented transfer requires the correct perimeter direction and
records a 72 charge only in row two of the strip, with its longitudinal
phase **modulo six**. In each direction lengths 36 and 78 give the
identical relation (185 entry labels, 2455 end records, 31704
entry/end pairs). The replaceable piece starting at 12 is disjoint
from distance 8, so shortening preserves the exclusion exactly.

For the positive part, proceed from the checked 161 base. On a board
of size `n+42` suppose the desired distance is `ell<n-53`. Take a
witness at `ell` on the size-`n` board and lengthen the clean piece
starting at `n-53`, leaving the charge fixed. Otherwise start with
the witness at `ell-42` and lengthen the clean piece starting at 12,
shifting the charge forward by exactly 42. In the latter case
`ell-42>=n-95>=66`, beyond the short piece. Both starts are multiples
of six, with the latter end-side piece a fixed distance from the far
corner. Extend the other arm through its clean piece at 12. Entry/exit
equality with zero charge on the replaced pieces preserves the unique
defect, all checked local configurations, and forest connectivity.
Thus survival applies to each stated distance, not merely to some
unspecified representative of each phase.

### Full-side-203 depth-two decision encoding

`depth_two_board` asks about the entire square, not the extension of one
preselected partial forest. The frame selector permits all eight closed
corner combinations with the one gap normalized to `(0,1)--(0,2)`.
One of 130 flags chooses the sole uncovered site: `(2,d)` or `(d,2)`,
`d=5,8,...,197`. The formula deliberately includes the previously
excluded distances. All nine-bit patches must have charge zero, and
every outgoing primal arrow has a zero-charge star. The isolate's
cross is empty, so it has no outgoing arrow. Omitting the charge
test at the NW sink and the isolate itself only relaxes the test.

There is a useful necessary connectivity constraint specific to this
frame. The forced perimeter is one simple path on all 808 boundary
vertices. Delete the edges of that path from a putative forced forest.
Each remaining component contains **at most one** perimeter vertex:
two such vertices in one component would give a second path between
them in the original forest. Thus assign each branch the two-bit color
of its attachment side, with a deterministic choice at corners. Force
equal colors across every forced non-perimeter edge. This does not
identify two attachments on the same side and is not a tree test.

The optional stronger version also orients a tree on the square faces.
The unused primal edges of any primal forest connect all faces to the
exterior in the dual. The exterior has degree one here; deleting it
leaves all bounded faces connected to the face `(0,1)` just under the
gap. Require every other face to point through an edge with two empty
primal ends, and forbid opposite arrows. The outgoing dual directions
lift to two compass sheets, flipping only on a `3/0` turn. A directed
simple grid cycle turns through one full revolution, incompatible with
that lift. On a tree the lift always exists by propagation from the root.
Thus this added condition enforces acyclicity without representing a
dual choice for each possible way to attach the isolated primal site.

```
export PYTHONPATH=target/pb-python
python3 -B -m analysis.research_program.depth_two_board 203 240
python3 -B -m analysis.research_program.depth_two_board 203 360 1
```

Any reported exclusion requires `drat-trim` verification; a satisfiable
projection is not an upper witness unless the marks pass the physical
spanning-tree replay at score 13928.

### Checked side-203 location update

**All 64 stars at distance `2 mod 6` are excluded on side 203.** Only
the 66 sites `(2,d),(d,2)` for `d=5,11,...,197` remain per one-gap
frame. The proof is the union of four checked disjunctions, each common
to all eight frames. Relative to the previously proved cutoff of 80
this removes 38 further physical locations per frame.

The `104 x 104` NW corner alone excludes **all 16** distances
`d=8,14,...,98` on **both** the north and west arms. The new distances
beyond the earlier cutoff are 86, 92 and 98. The eight distant frame
choices have identical local restrictions here. Replay:

```
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.one_gap_star_rim 203 8 --nw=102 --corner-only
# 0111 s VERIFIED
# (0, 1, 1, 1) four-root side/phase [(0, 5, True), (3, 5, True)] excluded [(0, 2, True), (3, 2, True)]
```

CNF: 85,688 variables, 1,772,401 clauses, SHA-256
`58cb9aefadb04ef5105c10a9d43bcea85aab2358c30d25d7319b24d606f5c5a9`.
Backward checking used 4,266,422 resolution steps. There are thus at
most **98 candidate sites per frame**, down from 104 after the earlier
cutoff. These are 33 distances `5 mod 6` and 16 distances `2 mod 6`
per arm. This does not mean all 98 sites extend. The fixed-window
exclusion in fact holds on the whole tail starting at 119: even there
the distance from coordinate 103 to the opposite end is 15, beyond the
largest stencil depth of six. The two near frame arms, their NW-rooted
arrows and the domain are fixed; all clipped reflected bulk coordinates
retain their period-three residues. Hence the same NW contradiction
applies without identifying interiors of squares of different sizes.

As a control, the triangular domain `i+j<=199` admits a local solution
with star `(194,2)`. Union-find on its 19,900 complete-star sites finds
no forced cycle. Thus even substantial growth along *both* arms need
not decide the far part of this phase.

```
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.depth_two_triangle 203 2 194 180
```

To go beyond distance 98, restrict the exact defect set **before**
generating clauses. A `149 x 149` NW square excludes
`104,110,116,122,128,134,140,146` on both arms together. This is one
necessary subdomain of every frame, not an attempted extension of
a frozen model. The 132,639-variable, 2,237,405-clause CNF has SHA-256
`5997fcff6a04cced483ac535e7cac52780e92f1415397f5b981431d4d2fae1b8`;
`drat-trim` verified 10,033,565 resolution steps. Together with the
smaller-window result this leaves at most **82 sites per frame**.

```
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.depth_two_triangle 203 2 146 150 -1 0 0 104
```

The two final disjunctions exclude the entire remainder of the even
phase. No tree hypothesis about marks outside the tested square is
added: all complete stars and patches in it come from the same
NW-rooted restriction, and its prescribed frame and perimeter arrows
are identical for the eight words.

| NW square | Distances, on each arm | Checked resolution steps |
|---:|---|---:|
| 104 | 8 through 98, step 6 | 4,266,422 |
| 149 | 104 through 146, step 6 | 10,033,565 |
| 173 | 152, 158, 164, 170 | 21,688,169 |
| 197 | 176, 182, 188, 194 | 28,942,217 |

```
export PYTHONPATH=target/pb-python
python3 -B -m analysis.research_program.depth_two_triangle 203 2 170 240 -1 0 0 152
python3 -B -m analysis.research_program.depth_two_triangle 203 2 194 300 -1 0 0 176
python3 -B -m analysis.research_program.depth_two_203_ledger
# after these four checks: 66 phase-five sites per frame;
# after the five three-quadrant checks below: zero
# physical lower-bound spanning tree: (13927, 41207, 2, 41208, 13927)
```

The ledger checks the hashes, disjoint site sets, frame restrictions,
checker logs, and the lower-bound tree. Pass `--drat` to recheck the
proofs. The same four fixed windows exclude those *same distances*
on every larger side on the tail: index 196 still has far-end distance
six at side 203, so the star and patch types on the complete sites of
even the largest window have stabilized. This does **not** eliminate
distances greater than 194 on larger boards.

In particular the side-203 isolate has **odd checkerboard color**.
Specializing the run ledger gives `J_even=3*M_odd-20775` and
`J_odd=3*M_even-20780`: here the odd color has 20,604 sites and
400 boundary incidences, the even color 20,605 sites and 407
boundary incidences, and there are 230 runs. Hence `J_even` must
be a multiple of three from 0 through 228; the other 229 minus
that number of joins have odd color. This is a necessary count,
not by itself a contradiction.

The full-board `one_gap_board 203 360 5` tests the remaining phase with
the isolate completed toward its side, forced outward tooth parents,
and the bulk join restrictions. Its 573,821-variable, 6,841,630-clause
CNF (`fdcfdb985b5a6242acdd3edb3f5eee41ed988507128990770b5bbf7f919998d5`)
returned `UNKNOWN`: there is no exclusion or witness from that solve.

### Side 203: testing phase five in the three-quadrant domain

**Final result: all phase-five distances are excluded as well, so
`P(203,203)=13927`.** See the [side-203 proof and complete
certificate ledger](SIDE_203_STAR.md) for all five disjoint batches.

Keep the full eight-layer rim, the entire north half, and the entire
east half (32,560 sites). Normalize the defect to the north arm, but
**do not discard the west cases**: transpose their *whole board* to
this convention, so the open NW corner has its gap on the west side
instead of north. The CNF therefore contains 16 frame words, the
original eight and their eight distinct transposes. Root at SE, fixed
by transposition. In the restriction 805 of the 808 perimeter arrows
are shared; the remaining three are conditional on the selected frame.
All complete stars and patches respect the single-defect budget and
all visible arrows are required to be consistent on the induced
fringe. A restriction of any target tree satisfies these conditions.

At distance **5**, `drat-trim` verifies UNSAT (6,401,470 resolution
steps; CNF SHA-256 `ed21cfa735106081567eb7d796c0e1336d472692400df0561e08296c98fb3ba0`).
Thus this is also a new exclusion of phase-five stars, at `(2,5)` and
`(5,2)` in every original one-gap frame. No evidence from a hypothetical
quadrant gluing is required.

```
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.depth_two_far_quarter 203 5 5 180
```

The four batches `11..53`, `59..101`, `107..149`, `155..197` (step
six) likewise returned `s VERIFIED`. These proofs include all frame
choices on both arms and exhaust the remaining sites. The earlier
`UNKNOWN` of the monolithic model has no bearing on the disjoint proofs.

See [the orientation-free charge identity](ONE_GAP_MARKS.md) for a
different exact formulation of the remaining decision.
