# Checked physical pieces of the one-gap isolated-star fan

**Current endpoint:** the physical square formula holds at every positive
side. `pendingFanIndices_empty` and the same-board failure theorem rule out
the final exceptional score. See the last section for the side-161 cuts.

All statements below use `n=35+42u`, with no lower cutoff on `u`.
`FanSeed.seed_of_score` starts from `L7.isolated_star_of_score`. Its
conclusions concern marks of the original acyclic forest, in a reflected
or transposed coordinate frame; the perimeter is not exchanged.

* The star is on a side incident to the gap corner. In the seven-layer
  L replay the far fringe cell `(4,31)` in folded origin coordinates can
  be dropped. This matters when an isolate on a nonincident side lies at
  transverse depth five in one of the arms.
* Write `d` for the longitudinal coordinate of the isolate, and `i=d-1`
  for its patch origin. `i` is 4 modulo 6. In row-major order the tile at
  `(1,i)` is **64**, and every aligned tile `(1,j)` to its east, through
  `j=n-4`, is **72**. These are masks 4 and 6 in the transposed fan-word
  convention. The first bit of `(4,j)` is set, as is the bit below it
  when `j>i+3`. `rooted_seed` traces each such line through the crop to
  depth five and exhibits its own perimeter attachment.
* `FanSlab.physical_step` proves the shrinking-fan transition from **two
  complete planted rows**. In the chart based on run lengths `(16,19,16)`,
  all three runs may have independent extra lengths. The next row has
  run lengths changed by `(3,-6,3)` and both transition triples are fixed.
  The check uses 15 physical rows, true side types and 39 mask bitmaps.
  Each horizontal pass starts at a real end; a repeated three-column
  block cannot justify its own masks with a cycle of unsupported matches.
  The theorem requires `k=57+x+y+z`, top origin `1 mod 3`, and the stated
  bulk row margins. It is not a small-width base exclusion.
* `FanFringe.lean` checks a `7×5` physical window: mask 448 at depth four
  forces 448 at depth one, for aligned columns `4..n-7`
  (`j+1` in `fringe_step`). It imposes no directions or
  component tags.
* `cap_of_score` checks the five final columns at a closed corner. In a
  chart looking inward from the south side, mask 73 at `(4,n-4)` forces
  a line from depth five to a south-side foot. If the input line already
  reaches a different foot through the crop, `unique_attachment`
  gives a contradiction. The condition on that incoming line is essential.

`lean/GridGraphs/Tests/OneGapFanCoverage.lean` imports these results, checks
their axioms, and specializes the location theorem to 35 and 77. The possible
distances are `5,11,…,29` and `5,11,…,71`, respectively.
`analysis/research_program/one_gap_fan_finite_probe.py 35 77` (run as a
module with `PYTHONPATH=target/pb-python`) also gets UNSAT at all 17 distances.
This last test is external: it retains a common owner for every forced edge
and costs on the physical square. It is not a Lean exclusion.

`FanBoot.handoff_of_score` uses only acyclicity, the score equality and
one perimeter hole. Write `q=(i-1)/3`, so the star is at `(2,2+3q)`.
For every possible `q`, `Teeth.west_teeth` forces the centers `(2,2+3t)`
for `t<q`: the elbow forces a second center on one arm, a first missing
center after two centers is impossible, and the other arm would run into
a closed corner. For odd `57≤q≤11+14u-2`, four folded charts now force
tile rows 6 and 7 (physical rows 19–24 across all interior columns).
Iterating `physical_step` gives both rows `y,y+1` for every
`6≤y≤⌊(q-15)/6⌋` in the same forest and frame.

### Physical long-fan frontier and speed windows

Put `k=11+14u`, `Y=⌊(q−15)/6⌋`, `f=q−3Y+3`. For `57≤q`,
`FanLong.lean` (`FanBoot.front_of_score`) gives `Front F w q k (Y+2) f`
from the score alone. The four north charts now replay the birth rows
as well as the shrinking rows. On `f≤t≤q` the upper component is sealed
at the physical cut `1+3(Y+2)` (no perimeter foot, only one possible
crossing). On `q<t<k`, every vertical edge back to that column's own
north foot is present. The first collision row uses an open 16-tile
rectangle; `east_step` carries the surviving stripe through the true
last tile. Coordinate `1+3t` here includes the physical interior origin.

`FanPhysicalSpeed.lean` and `FanRootSpeed.lean` check the physical
6/4, 13/7, 20/10, 27/13 dangling moves and the 4/3 rooted move
(rows advanced / columns lost). The current row is an input; later rows
in the window are not planted. Each uses the 13-mask hypothesis only
in the window. A tile label records the mask and 12 outgoing edge bits;
neighboring plaquettes match both complete labels on their common edge.
The rooted replay also rejects three local mask quadruples, checked
in 12×12 physical halos. Arrows are realized in the actual forest:
rooted lines point back up, while a dangling component with a unique
crossing must send its parent across it. No external SAT log or stored
plaquette-domain dataset enters these theorems.

**Exact residual in `FanSouthHandoff.lean`** (`FanBoot.south_handoff_of_score`):

1. Establish `Plateau F w (Y+2) (Y+6) (f−1) k`, and `DeepAfter F w
   (Y+6)`: each tile `(j,i)` with `Y+6≤j`, `j+7≤k`, `4≤i`, `i+7≤k`
   has one of the thirteen row-major masks in `Port.shapes`.
2. Those two facts imply `SouthEnd` for every `u≥12` (side 539 onward).
   Below this threshold `Speed.schedule_iff` checks the exact arithmetic
   schedule domain: `u≥6` and `q∉Speed.earlyExceptions u`.
   There are no schedules at `u=4,5`; for `u=6,7,8,9,10,11` the counts
   are respectively `3/19`, `8/26`, `27/33`, `36/40`, `45/47`, `53/54`.
   This completeness result is for the current five window sizes and cap
   predicate only. `SouthEnd` supplies a single
   physical suffix, including its attachments, at a real south rectangle
   with `14≤h≤43` remaining rows and at least `⌊3h/4⌋+3` suffix tiles.
3. Exclude that rectangle. `last_line_cap` already rules out a rooted
   final line with last-column mask 73 at tile row `k−2` (height two).
   Reaching the height-14..43 cap schedule does not itself reach height two.

For center length 17 (`q=6Y+19`, or `q≡1 mod 6`), `CollisionWide.plateau17`
derives the full missing `Plateau` from the two incoming rows, without
an axis filter. The 66×66 open window replays marks and owners from the
same physical forest, and `east_step` extends the first stripe column
through the actual east edge. `FanSouthCollision.lean` uses these same
incoming rows from the scored witness. In that residue class, only
`DeepAfter` and the applicable schedule remain for `SouthEnd`. The
other two center lengths still need the plateau.

The [long-fan coverage test](../lean/GridGraphs/Tests/OneGapLongFanCoverage.lean)
checks the public theorems' axioms. No unconditional long-fan exclusion
is claimed. The separate small-index problem is outside this reduction.
See [the external fan argument](ODD_FAN_SPEED.md).

The open-bulk implication “both axis filters plus zero local prices and
acyclic ownership imply `Straight`” does not hold. The
[bulk obstruction test](../lean/GridGraphs/Tests/OneGapBulkObstruction.lean)
checks a period-three horizontal stripe: its aligned row-major mask is
7 (not in `Port.shapes`); all three-by-three phases have zero patch and
star prices, and the bond owners have a strictly increasing rank. This
is only an open-bulk example, not a scored square. Deriving `DeepAfter`
must use actual boundary or seed information, or another invariant that
rules out this example.

For the shorter collisions, diagnostic probes at side 203 planted both
shrinking rows, the full stripe at `Y+2`, and the up/down arrows on its
rooted and dangling lines. A cropped window with the real east edge
still allowed a missing stripe mark at `(Y+4,f−1)` for `q=57` and at
`(Y+3,f−1)` for `q=59`. The same probes with the full width rejected
those deletions. This points to a missing two-sided constraint for
center lengths 13 and 15; it is not a Lean exclusion or a physical
counterexample.

### Southern cap closed; an eastern-column alternative

`SouthCapEastAll.eastRange_empty` (the `Strip.GridScan` namespace)
covers the entire interval `14≤h≤43`. The check for heights 21–43
is one `native_decide` over `Fin 23`; `southEnd_excluded` consumes
the result for a long fan with the physical halo. Reaching `SouthEnd`
is still a separate obligation.

There is also a geometric obstruction which does not inspect packed
states. In `EastRailObstruction.lean`, delete the wire from the
north contact to the apex. At each tile in the easternmost column,
suppose the NW site is marked and the site immediately east or south
of it is marked. In the first case the path can exit to the east rim.
In the second it descends to the next NW site: even a single blank
between two marks carries both forced edges. At the last tile the
south mark gives a south attachment. Either exit reconnects the ends
of the deleted wire, impossible for a bridge. This induction works
at any height ≥2. `EastRailPhysical.eastRail_escape` specializes it
to actual marks under the checked physical-cap geometry: some eastern
tile must violate the bit condition.

`EastRailCone.lean` gives a first propagation bound. Write
`S={3,7,9,73}` in row-major masks. A catalogue plaquette whose two
northern tiles belong to `S` has its southeast tile in `S`, except
for southern pairs `(146,144)` and `(144,129)`. Thus three adjacent
plaquettes below four `S` tiles force an `S` output at the right.
The exceptions would have to extend west as `146,144,129`, but
`146` cannot itself be an output. This proves propagation from
an arbitrary suffix at a cost of three columns per row. Checking
the local rule uses the 49 catalogue tags; the induction uses no
further finite check. It is slower than the required fan speed.

The stronger suggested rate (three columns per **four** rows) does
not follow from the particular fixed-height seam test in
`analysis/research_program/east_rail_fold.py`: with ten tile rows,
the physical eastern tags, bulk row tags and an `S` top, it forces
the desired suffix at width 18 but the same test leaves other masks
at width 22. These are residual domains, not counterexamples.
A speedup needs more information, e.g. growing the depth with the
width or retaining which lines already attach to the perimeter.

### Keeping multiple north feet

`RootedRailStep.no_crossbar` uses `unique_attachment` on two actual
north paths: a horizontal run of three forced edges between their
ends would connect two distinct perimeter vertices. `extend_line`
keeps the actual north foot across a blank at the bottom of mask 9
when the next tile begins with a mark.

Using both facts, `RootedRailAdvance.advance_four` proves that under
four consecutive rooted 73 tiles the fourth output is again a
**rooted 73**. For each column use the ordered pair `(m,b)` of masks
one and two rows below the planted row. Matching the two plaquette
rows rules out a crossbar, and leaves a four-level quantity that
increases at every step up to 3. Only `m=73` has level 3. The local
table implication has one 49-tag `native_decide` check; `advance_suffix`
iterates it without another finite check. `RootedRailPhysicalStep` proves
the catalogue input for the six plaquettes on a scored cap.

`RootedRailFinish.wide_run_excludes` composes this induction with
`eastRail_escape`. In tile coordinates it requires a rooted suffix
starting at `(y,c)`, catalogue admission in the rectangle below it,
`y+14≤k`, and `c+3*(k-2-y)+3≤k`. It does not postulate mask 73 or a
root line on any later row. This width hypothesis is too strong for
the general north handoff.

`analysis/research_program/rooted_rail_cone.py` is an external
diagnostic of the faster proposed step. It tracks whether each site's
vertical path to its north foot stays unbroken and removes words
bridging two such paths. With depth 10 and the true eastern tags, the
rooted 73 suffix at row 4 began at column 3, 6, and 12 for widths
18, 22, and 30. These are support sets, not whole-board witnesses:
this particular local filter does not establish the required
three-column loss over four rows.

### What a counterexample now has to contain

`failure_from_score` retains the rim orientation and the location of
the isolated star from the same scored seed that supplies the speed
windows. For `k=11+14u≥59`, that witness cannot reach `SouthEnd`,
including when `q<57`: the bound `57≤q` was not needed by the cap
itself once the size and last rooted tooth are given.

Put `f=max(3,q+1)+12`. When `4f≤k+3`, for every start `a` between
`f` and `⌊(k+3)/4⌋`, a counterexample must fail in a 10-by-10 window
with top left `(4+4j,a+3j)`. At the **first** failure the incoming
suffix is still a physical `Front`; all earlier windows on that route
were straight. Moreover, starts spaced 16 columns apart yield
different physical bad tiles: `4*column-3*row` stays in disjoint
intervals, regardless of the row at which the first failure occurs.
`RootCorridorPacking.lean` proves this for arbitrary `u` without a new
finite replay. It gives a necessary multiplicity of bad tiles, not
positive price at those tiles.

Outside that room bound, a short index needs `u≤18`. For long indices
the alternative is an arithmetic schedule exception, absence of the
collision plateau (only center lengths 13 or 15), or a physical
incoming front at a non-straight move window whose successor still
has a schedule to a cap. The speed proof no longer needs a shape
hypothesis over the whole lower square. `SquareFormulaFanResidual.lean`
checks the conditional assembly: excluding these failures suffices for
`ExactSquareFormula`. No exclusion of all such failures is known here.

### The roomy rooted branch is impossible

Let `h,w` be the remaining height and width of a fully north-rooted
73 suffix. With `h,w≥8`, `4w≥3h+8`, and its northwest tile at row
and column at least four on a board with `k≥59`, `no_wide_front`
rules it out. The proof uses the physical south boundary. It does
not assume straightness of the tiles below the suffix, nor require
the rectangle to have height at most 43.

* `RootedSouthContact.board_word` proves catalogue membership from
  the score at every plaquette in this rectangle. The relevant
  margin for the six-site halo is four tiles, not a 43-row upper
  bound. The halo uses the same rerooted parent field throughout.
* `RootCoverField` adds a flag to each tile indicating a certified
  vertical path to its north foot. A flag only propagates when the
  intervening forced edges are present. Two flagged neighbors
  cannot be bridged; on the bottom row a flagged middle mark
  would connect the north foot to a distinct marked south foot.
* `RootCoverWave.no_field` is an induction on **physical** rows and
  columns. The finite invariant is indexed by distances to the south
  and east (capped at six), and `4*column-3*row` (clipped to `[-1,6]`).
  It stores possible outgoing south and east pairs. All allowed
  words preserve the invariant from their north and west neighbors;
  entering from either open edge has a separate check. At the
  southeast corner the width inequality forces the last phase, with
  no possible south pair. The certificate is 39,592 bytes, 159
  interned sets. Regenerate from the repository root with
  `python3 -B -m analysis.research_program.root_cover_wave --export`.
* For a candidate bad window on a separated route, `y=4+4j`,
  `x=f+16i+3j`. Its rectangle satisfies the same inequality: the
  terms in `j` cancel. Thus `empty_route_cover` covers all `BadAt`
  sites by `∅`; `roomy_impossible` applies `south_of_sparse_failures`
  and the verified cap exclusion. In particular every short fan at
  `u≥19` is excluded for the normalized scored witness. There is also
  a cut at the long collision row `y=Y+2`: even the rooted teeth
  strictly east of `q` would give a contradiction unless
  `k+3*(Y+2)<4*(q+1)+8`.

### Side 161, isolate index five

For `(u,q)=(3,5)` the generic row-four suffix starts at tile column
18. `ShortFiveNorth.lean` keeps the actual isolate and its neighbors
in a 48-by-48 crop starting at tile column 3. It checks just eight
outputs per view: columns 16 and 17 on rows 1 through 4. If all are
73, the existing plateau from column 18 completes these four rows.
`front_of_plateau` attaches them to the north feet of the same seed.
The resulting suffix has width 37 and height 49, exactly the
dimensions already checked by the east/south transfer for `(3,3)`.
The finite check is on the north crop; no extra southern transfer
certificate is needed.

For `(3,7)`, `ShortSevenNorth.seven_checked` moves the crop start to
tile column 4 and checks columns 16–19 on rows 1–4 in all eight
views. The generic plateau begins at column 20. `seven_front` in
`ShortCropFront.lean` combines the two pieces, giving the same rooted
width 37 and the same rectangle exclusion.

### A uniform rectangle allowing a first mask of 9

`North.translated_mixed` places the left edge at `q+5` for `q≥6`
and `q+17≤k`. Only the row-four tile at that edge can be 9 rather
than 73; rows one through three certify its north foot in either
case. `Mixed.exclude_suffix` uses both rim constraints and allows
either initial mask without asserting that a 9 propagates its root
to the next row. Its sufficient bound is `3*h≤4*w`, for `h,w≥8`.
The induction uses a single 45,899-byte table independent of the
dimensions (`root_cover_wave --export-mixed`); `native_decide`
checks local closure and the empty southeast phases.

For the translated row-four suffix the width condition becomes
`4*(q+5)≤k+12`. The assembly filters on this inequality for `k≥53`,
leaving 152 short pairs. The same rectangle lemma at a long fan's
collision strengthens its necessary bound to `k+3*(Y+2)<4*(q+1)`.

### Deeper north suffixes from translated witnesses

For tile count `k=11+14u ≥ 53` and `q+17 ≤ k`, use the following
placements. `d` is the distance from the west crop edge to the isolate;
the physical suffix begins at `(y,f)`.

| `d` | `y` | `f` | Left margin | Sufficient width: `4f ≤ k+3y` |
|---:|---:|---:|---:|---:|
| 9 | 5 | `q+3` | `q≥12` | `4(q+3)≤k+15` |
| 12 | 5 | `q+1` | `q≥15` | `4(q+1)≤k+15` |
| 12 | 6 | `q+2` | `q≥15` | `4(q+2)≤k+18` |

`DeepNorthCheck` inspects a representative crop in all eight views.
Only one mask-73 witness per row at or west of `f` is needed; the
witness column may vary. `translated_label` transports that readout
to the actual seed. `DeepNorthSuffix` grows each row east by
`east_step`, attaches the first three rows to their actual north
feet, and extends those lines vertically before applying
`Mixed.exclude_suffix`. The third profile verifies a deeper front
but its arithmetic cut is contained in the second.

### Grouping by the first possible suffix depth

At `f=q+1`, `neededDepth u q` is the smallest `y≥4` with
`4*(q+1)≤k+3*y` (`neededDepth_le`). This tests the slope only: an
actual north-rooted suffix and both eight-tile margins are still
required. `depthGroup y` gives the exact members at each depth among
the 121 pairs left by the previous three profiles.

| Depth | 6 | 7 | 8 | 9–12 | 13–20 | 21–32 | 33–53 |
|---|---:|---:|---:|---:|---:|---:|---:|
| Pairs | 3 | 6 | 3 | 16 | 29 | 33 | 31 |

The depth-six group is `(6,27), (10,41), (14,55)`. The old row-six
suffix began at `q+2`. `DepthSixCheck` uses a 72-site crop with the
isolate at relative tile column 18. In each view it retains a forced
73 at or before column 19 on every row from 2 to 6. The physical
transport in `DepthSixTransfer` preserves the mask and the actual
owner at the exceptional site. The east-ray and north-foot proofs
then give the required `q+1` suffix without a replay for each pair.
After this group, 118 short pairs remain.

At depth seven the six pairs are `(3,17), (4,21), (7,31), (8,35),
(11,45), (12,49)`. Use the same interior crop and its certified
rows 2–6, checking one more row. For `q=17`, shifting that crop
would place its origin off the board. Instead align a second crop
with the physical west wall and check rows 2–7 there.
`DepthSevenTransfer.exclude_seven` applies both placements at every
eligible size: with `k≥53`, `q=17` or `q≥21`, and `q+17≤k`,
the sufficient width is `4*(q+1)≤k+21`. Both use the same rooted
suffix argument, at row 7 and column `q+1`.

For row eight, keep the certified witnesses on rows 2–7. Only the
new row needs a finite check. `DepthEightCheck` tests interior
placements 21 and 22 tiles west of the isolate, accepting a
placement if it forces a 73 at or west of `q+1`. `eight_suffix`
transfers the result in the seed's own view and retains a path
to a north foot at every column from `q+1` to the east boundary.
For `k≥53`, `q≥25`, and `q+17≤k`, the exclusion requires
`4*(q+1)≤k+24`. The depth-eight pairs `(5,25)`, `(9,39)`, and
`(13,53)` all meet it with one unit to spare.

### Buffered suffix induction (no depth sweep)

`Rooted.Buffered.propagate` uses a plain top run from column `a`
and north-rooted columns from `f` onward. Whenever
`a+3*(D+1)≤f`, it keeps every column from **the same `f`** rooted
and equal to 73 through all `D` lower rows (with the stated margins).
It does not require the columns west of `f` to be rooted.

The row invariant is the adjacent-pair alphabet
`(3,9), (3,73), (7,3), (7,7), (9,9), (9,73), (73,73)`. Four
overlapping physical plaquettes carry this alphabet down a row,
losing at most three columns on the **unrooted** left edge. A single
finite check verifies the transition rule against the existing word
bank, including its rim tags. If the pair at `f` and the one below
it both belong to the alphabet, a non-73 left tile would bridge the
two distinct north feet either here or in the lookahead row.
`no_crossbar` excludes both, and the alphabet forces 73 eastward.

For long fans, `y=Y+2`, `a=q-3Y+3`, `f=q+1`, `D=Y-2` with
`Y=(q-15)/6`. Thus a scored failure must satisfy `k+6Y<4(q+1)`.
For `q=6Y+19`, the checked collision plateau first carries the
front to `Y+6`, improving this to `k+6Y+12<4(q+1)`.
`no_fan_failure_of_buffer` states the two exclusions explicitly.
These are uniform cuts on the long branch, not a proof when both
inequalities leave the rectangle too narrow.

### East-rim rigidity without a western width budget

`LatchedBand.rigid` (namespace `Rooted.Buffered`) needs just the
seven allowed adjacent pairs in a suffix of length at least two and
one north foot at its easternmost tile. A 3 or 7 at the start of a
subsuffix forces a 3 or 7 in the same column one row down, and a
stable vertical pair transmits the band to the true east rim. The
east-rim rule preserves the last north line; iteration to the
south rim contradicts unique perimeter attachment. Two adjacent
9s force such an obstruction in the next row. Thus even with no
spare western columns the row must be `73,...,73`, with only its
very first tile allowed to be 9.

`CollisionBand.plateau_all` uses this rigidity at the collision for
all odd long fans. The crop need only force membership in
`{3,7,9,73}` at four columns, not a singleton mask. These columns
overlap the band carried from the preceding row and extend its
certified left edge to one tile west of the required plateau. The
plateau through `Y+6` is now a conclusion even for center lengths
13 and 15. No failed-plateau alternative remains in `LongFailure`.
The sharper propagation `mixed_end` pays only two columns on the
first descent and needs no lookahead on its terminal row. It reaches
`2Y+6`; all long failures require `k+6Y+18 < 4(q+1)`.

For a remaining blocked speed move starting with front column `f`,
`OffBandMove` requires an actual tile outside `{3,7,9,73}` at
positive relative row `j` and between the move's read column and
`f+3j` inclusive. If all tiles in that region have one of the four
masks, catalogue membership certifies the adjacent pairs; the
farther eastern suffix is already a band. Rigidity then gives only
9 or 73 throughout the read rows, contradicting blockage. This does
not exclude every off-band tile or the early schedule exceptions.

`SlowBand.advance` improves on the pair-only propagation when two
incoming teeth are sealed (dangling). Their physical owner arrows
cannot point north. A single 21-site chart combines those two arrow
constraints with the previous and current 73 rows. It certifies only
four-mask membership at the western join. East-rim rigidity turns
that membership into full plateau rows. The new front includes its
seals and its north lines, so the same proof iterates: four western
columns pay for **two** new rows instead of six. This step has no
`Straight` premise and no depth parameter in its finite check.

In the current assembly set `s=(3Y-2)/4` (natural division).
From row `Y+6` this reaches row `Y+6+2s` with the front starting
no farther east than `q+1`. The surviving long branch must satisfy
`k+3*(Y+6+2s)<4*(q+1)` and exhibit either an early schedule
exception or a physically off-band move. In particular, this
argument does not infer that arbitrarily narrow eastern margins
satisfy the rectangle's width hypothesis.

### What a first break into 129 must look like

`Break129.no_fast_tail` excludes `129,9,73,...,73` at any eligible
row with a north line at the easternmost tile. Overlapping price words
force `144,129` one row down, with the new 129 three columns east of
the old one. A following 73 would demand both 128 and 18 or 146 at the
same site one row later. Thus the following tile is 9; rigidity keeps
the rest plain. The eastern price tags leave insufficient room for
this to continue indefinitely. On the terminal southern row, even
without lookahead, either surviving east mask (9 or 73) connects
the north foot to the south rim, violating unique attachment.

Consequently `Break129.forced_corner` confines the surviving 73→129
case to the following two-column word (west column, break column):
`(16,73); (16,129); (292,128)`. The tile immediately east of 129 is
73. This uses a western catalogue column, so the corner conclusion
in `FirstBreak` assumes `5≤x`. The same test **unconditionally**
removes 73→144 and 9→146 from first breaks of fitted moves: their
forced 129 one or two columns farther east would have 144 where the
corner requires 16. The remaining pairs are 9→2, 73→16, and 73→129.
The open-crop example with eastern neighbor 9 does not extend to
the physical square under these hypotheses.

### The western trace and its speed limit

`CornerCone.west_trace` forces both lower rows of the 129 corner to
be 292 at every column from 4 through `x-2`, inclusive. On the row
above, those columns have only 258, 288 or 292. If the initial
front at row `y` already covers `x-1` and `x≥6`, `CornerCone.birth`
traces the adjacent 16 backwards until its creation: at some
earlier row `y+h`, column `x-1` changes from 73 to 16 while
`x-2` changes from 2 to 258. From then until the row above the
129, columns `x-1,x` stay `(16,73)`. `CornerHistory` retains this
on the actual blocked move. It does not presume that the initial
front extends to the left of its read column.

The corner also gives a uniform propagation bound. Below a plain
suffix starting at `a`, a 129 at `a+1` would require a 16 at `a` in
the upper row, which is already 73. At `a` itself a 129 forces 73
to its east. The resulting plain suffix loses at most one column
on one descent. On the diagonal where that column is lost, the
possible nonplain heads decrease in the order `16,129,9`:
a repeated advancing 9 would leave `2,9` or `3,9` at the start of
a lower suffix, forcing a latch. Hence `CornerDrift.lean` proves
**four rows cost at most three columns**. The proof uses one fixed
plaquette law and induction, irrespective of depth. In particular,
if a first break is 129 at column `x≥5` below row `y+j`, its upper
16 requires `x ≤ max(5,f) + 3⌊j/4⌋ + (j mod 4)` for an initial
front starting at `f`.

`long_failure_of_seed` now starts at `Y+6` with the plain suffix
at `q-3Y+2`. After `Y-1` four-row blocks and two single steps,
the north-rooted suffix starts at `q+1` on row `5Y+4`. Thus
the remaining long branch requires `k+15Y+12 < 4(q+1)`.

### Tracing 2→258, including a leading-edge read

`PriorCut` in `FanSpeedTail.lean` retains a row `s` on the same
physical square. For a read column `x` (possibly the very first
column of the new front), the cut has `73` at `x-1` and **not `2`**
at `x-2`. Column `x` stays `73` from `s` through the incoming row.
At the initial collision the extra bit of information comes from
the four-mask read just west of the plateau. For subsequent moves
the old front covers both columns since each move advances by at
least three; the move's proved rectangle covers `x` through the
new cut. Neither argument adds a straightness assumption.

`TwoAncestry.from_prior` traces a 129 first break at `x` back
through the 16 at `x-1` to an actual `2→258` at `x-2`. Immediately
before the 258, read the triple of columns `x-3,x-2,x-1`. Going
backwards, the middle mask can stay 2, with left mask 288 or 292
and right mask 72 or 73. This run cannot include the retained
cut. The row just before the run must have one of the two forms
`(128|192, 8|9, 72|73)` or `(288|292, 32|36, 128)`. In particular
the all-144 and all-146 predecessors allowed by the western
plaquettes alone fail the physical read on their east. These are
necessary conditions; not every combination is asserted feasible.
`OffBandMove` retains the source, run and later 16 strip with no
`f<x` qualification. Independently, `sealed_entry` shows how the
dangling tooth's seal rules out an inherited 16 or 18 directly
above the western 16 when the seal extends through that site.

`GridGraphs/Tests/OneGapTwoAncestry.lean` checks the limit of the
mask-only argument: an unbounded travelling field passes **every**
bulk `(6,6)` plaquette, with a plain incoming suffix, an actual
`(128,9,73)` source, `2→258`, and a leading-edge `73→129`. The field
moves three columns per four rows, and every tile is in `Port.shapes`.
It is neither a blocked move nor a scored square. Ruling out that
source on a physical failure requires more than incompatible bulk
mask words.

### First nonstraight tile: a physical exclusion and a finite residual

`DepartureOwners.lean` orders the actual read window by row then column.
Fixed 15-site owner charts transfer the arrows on the first tile outside
`Port.shapes` from the same physical `Flow` used on the ancestry. Strictly
after the read's first column, the only `(mask, center parent)` pairs are
`(6,north), (8,west), (32,east), (144,south)`; the northwest site of such a
departure cannot carry a north line. For a 129 break, `DepartureTail`
excludes any actual departure in the first three rows beginning at that
break, for both sources. The apparent `32,2,73,...` continuation forces a
3 or 7 latch down to the perimeter.

The second source is now exactly `(292,36,128)`: 192 cannot be the
predecessor of the right-hand 128 since it would have had to persist back to
the retained 73. The other predecessors (128 and 129) rule out 32 at the
source center. On the first family the northwest and center arrows of the
middle tile point north and west; on the second they point west and east.
At the first row of the repeated 2 the northwest arrow points east for the
first source and west for the second.

`DepartureRim.lean` uses the *actual* easternmost north line. When the
preceding straight interval reaches a 73, an offending 6 or 144 would
transmit a forbidden pattern east until it hit the plain suffix. Induction
in the column proves the conflict at arbitrary distance. In this situation
the only candidate, even on the western edge of the read, is 8 below 128.
It requires a 48 or a 56 immediately west on both rows, with four consecutive
physical parent edges going west from its center. But the 128 with that
western neighbor already needs a nonstraight tile **in the read column**
one row earlier. At the top of the window it contradicts the plain front.
Thus it cannot be the first departure. In `straight_of_room` the
three-columns-per-four-rows cone provides both the 73 and the north foot;
the window can be widened for this argument and then restricted.

`Speed.roomy_uniform` gives a structural long-fan route for `k≥235`, using
the 27-row/13-column dangling move and the 4-row/3-column rooted finish.
Every window on the route has the width required by `straight_of_room`.
`roomy_south_end` applies the actual moves to the scored witness; the
resulting cap contradicts `no_south_of_room`. Below the uniform cutoff,
`RoomyIndices` checks **arithmetic schedules only**; 71 long pairs survive
this and the earlier rectangle cut. Adding the 104 short pairs gives 175
distinct possible physical indices, all at `3≤u≤13`. This is not a list
of realized scores.

`ShortBufferedFront` removes 26 more pairs. One fixed translated crop
puts a 73 at `(4,q−10)` in every orientation. Grow it east along row
four; the physical north lines already extend there from column `q+1`
onward. Three four-row advances consume nine columns of this buffer,
and two single-row advances consume the last two. This supplies a
rooted front on row 18 at `q+1`. For `(u,q)=(13,55)`, its dimensions
are `175×137`: `3·175 ≤ 4·137`, so `Mixed.exclude_suffix` applies.

The first-departure test uses the tooth on the preceding row, saving
one row in the cone budget. This removes three more long pairs. In
`Speed.route_179_175`, four long moves take `(147,100)` to `(39,152)`.
The medium move needs width up to `152+3·6+1+8=179`, exactly the available
width. It reaches the checked cap `(19,162)`.

At side 497, the row-five translated tooth at `q−13` gives fourteen
columns before `q+1`, enough for four four-row blocks and two single
rows. The resulting row-23 front for `q=55` meets the rectangle bound.
For `q=161,163`, `Speed.route_165` takes two dangling moves of 48 rows
and 22 columns followed by the medium move. `ExtendedDanglingMove`
checks the transfer on a fixed 23-by-55 straight window; the physical
straightness of each such read follows from its cone budget. The two
terminal states are `(19,146)` and `(19,148)`.

At side 455 the row-six tooth at `q−16` pays for five four-row
advances and two single rows. With `q=55`, the resulting row-28 front
leaves a `123×95` rectangle, with `3·123 ≤ 4·95`.
`BridgeCap.exclude_bridge` handles the two long indices by the same
34-, 48-, and 20-row transfers. The plain part of the last row starts
one column before the front with seals. The southern test only reads
the plain tiles and the last north line; it needs no seal at the extra
column. At `q=145` it reads 19 columns at height 22; at `q=149` it
reads 18 at height 21. In both cases the leftmost read is that extra
column.

`NestedDeparture` reduces the horizontal budget for a 48-row transfer.
Before the first bad row, every earlier row in the read is straight.
If enough such rows exist, a shorter certified transfer puts a new
plain row and an eastern root inside the read; start the cone there.
This bounds the lateral offset by 27 instead of 40. `NestedCap` allows
arbitrarily many repetitions. `GuardedSchedules` proves the physical
contradiction for any successful mixture of seven transfer sizes, using
the last plain column at the cap. It covers the four long indices at
side 413; the short index uses the row-seven tooth and a row-29 front.

At that stage 57 short and 42 long indices remained. For 26 of the
42 long indices even relaxing **all** intermediate width/placement
tests could not make these seven transfers work from the old handoff
to the old cap. For `t` moves with size indices summing to `A`, the exact
displacements are `7A−t` rows and `3A+t` columns (`Guarded.capacity_of_fits`,
`pending_capacity_checked`). A different move order alone cannot fix
that deficit.

The local check in `TrimmedCap.lean` replays the same physical height-14 cap with just
the last ten top tiles plain. The western three top tiles have no
plain-mask requirement. For *any* height `h≥14`, let `d=h−14`.
The last `3⌊d/4⌋+(d mod 4)+10` plain tiles and **one** eastern root
suffice: descend `⌊d/4⌋` four-row blocks and the remaining single rows
to the one checked cap. There is no upper height cutoff.

`CollisionReach` checks only the two masks at the western edge of the
plateau; `CornerCone.step_head` supplies the plain suffix farther east.
For collision lengths 15, 17, 19 this transports the front through
rows `Y+8`, `Y+7`, `Y+10`, respectively. The guarded schedule may
start on any certified row from `Y+2` to that endpoint. With both
improvements 16 long indices remain; only seven fail the necessary
capacity test for every available start. The trimmed cap also takes
the row-seven tooth at `q−19` directly, leaving 52 short indices.

`nested_window` separates the geometry from the choice of a shorter
window: a `RestartCover` may restart the cone only on a chart lying
strictly **above** the first bad row. `compact_bridge` and
`compact_extended` require only 35 and 49 plaquette rows instead of
40 and 54 for their respective 34- and 48-row advances. The intermediate
41-row advance also uses the new nested bound. For the latter two moves,
the tooth can be retained at offset 24 with seven columns of eastern
clearance, for a total of 31. At size five the total is 27.

On the nine formerly capacity-feasible long indices, removing just the
old cone-width test from the arithmetic search would allow all nine
routes; removing just the dangling-tip check would allow only `(5,65)`
and `(5,67)`. The new transfer keeps the actual tip check. Those two
indices can use the 41-row move wholly on the dangling side. At
`(6,93)` and `(7,107)` the last 48-row move uses exactly 31 columns
of available eastern room. `Tests/OneGapCompactSchedules.lean` checks
these counterfactual route counts separately from the physical proof.
`pending_capacity_checked` now leaves seven
long indices, **all seven** failing the relaxed capacity test. Together
with the 52 short indices this leaves 59 candidates on the same five sides.

`EastBoundary.rows` constructs the eastern word directly from the short
seed in any view. Write `b=q+2−3*y`. For `q+11≤k`, `y≥2`, `6*y+3≤q`,
and `3*y+4≤i<k`, the tile in column `i` is 146 up to column `b−4`,
then 18, 66, 72, and finally 73 from `b` eastward. Two fixed local
seed rules start rows 2 and 3. On each later row, two preceding rows
force the tooth at `b`; propagate 73 east and then induct westward,
using the already determined output to the right. `EastBoundaryChart`
checks only finite relative offsets in boxes of height 16 and width
at most 58 site origins. The inductive rules do not grow with `q` or `y`.

`EastBoundary.exclude_rows` couples this front to the actual eastern
north line and the trimmed cap. `capRoom` selects `y=⌊(q−3)/6⌋`.
This eliminates 13 short pairs at once, including both remaining
side-329 indices. There `y=8`, `k=109`, `topWidth 101=76`, and the
available widths are 78 and 76. The residual is 39 short plus 7 long.

For side 287 the filter gave `49,53,55,91`. The first three open-fan
rows miss the trimmed width by `1,1,3` respectively. `EastBoundaryExit`
reads one row beyond the proved interface: a 16-by-43 patch of mask
origins forces either 9 or 73. The retained eastern root and
`Departure.plainBeyond` turn this into a whole plain suffix.
For `q=91` the seven-size arithmetic misses by one column. Size
eight (`far_test`, with `cover56` for physical admission) advances
55 rows for 25 columns. From `(73,58)` it reaches `(18,83)`;
the guard starts at 82 and `topWidth 18=13`, exactly fitting `k=95`.
The combined cuts leave 33 short and 6 long indices.

`CornerCone.low_head` gives an additional free row after the exit:
whether the leading tile is 9 or 73, its diagonal successor has rank
zero. Thus the suffix beginning just east of that tile stays plain on
the next row; its last north line extends on the same board. Using
`topWidth (k-y-2)` instead of `topWidth (k-y-1)` removes `(4,37)`
and `(5,47)`. At that stage the side-245 short indices were 49,
51, 53, 55. Both long indices, 77 and 79, failed even the relaxed
capacity test from the old starting column.

`WestFanBase` reads the first three previously missing western tiles
in rows 2 and 3 from a single patch at the actual northwest corner.
For `q≥35`, `EastBoundary.rows_from` therefore starts at `3*y+1`,
and applies while `6*y≤q`. In the wider exits, `ExitPair` rules out
the `2,8` pair and reads a low head farther west on the row below.
In the widest case `66,72` places that head under the 66. These
exclusions clear all five side-245 short indices.

`LiveCut.exclude` uses the **current** boundary at `y=(q-15)/6+2`.
Two previous row words give the 73 at `b=q+2-3*y`; east propagation
gives its guard and suffix. `dangling_in_collar` seals the tips
starting at `b+1` using just the two columns that can touch each
line above the cut; the old front retains its north feet. Guarded
transfers now fit from `(y,f)=(12,44)` and `(12,46)` respectively
for 77 and 79. The same argument clears `(4,59)` and `(4,63)`.
At side 203 the last open row for `q=23,25` is row 3.
`Short.North.line_from_three` uses the three plain tiles in the
easternmost column to establish its north line through the start of
row 4. This supplies exactly the root needed by `EastBoundary.exclude_exit`
at `y=3`. Both indices pass the exit width test, leaving 21 short
and 2 long indices overall. The long indices are `(4,61)` and `(4,65)`.

`ShortBirth.exclude` now clears `(4,47)` and `(4,49)` at row 7.
For `q=47`, column 28 begins the plain suffix, and columns 29 through
47 carry isolated dangling lines. `dangling_after_birth` only needs
the two neighboring columns in rows close enough to touch each line
after its birth. On rows 0 and 1 these reads are all within six tiles
of the seed; one translated chart supplies them. `rows_from` supplies
the later words, and `suffix_from_sites` supplies the actual north
roots farther east. The guarded transfer thus has its physical front
as well as its width test.

`NorthFirstStep.first_east` propagates the plain mask on row one
through the last aligned column, using the actual east-rim price tags.
Starting at the paid seed column, `ShortBirth.north_roots` consequently
needs only `q+11≤k`, the room required for the birth and row reads.
At side 203 (`k=67`) this supplies the roots for the row-eight seals
at `q=51,53,55`, with 16, 14 and 12 columns of room respectively.
`DeepCut.front` restarts the eastern induction from the known long-fan
rows and carries the front to `y=⌊q/6⌋`. On the final row it reads the
plain suffix directly for the line seals. For `q=61` this gives row 10,
with guard column 33, dangling columns 34–61, and the preserved north
feet in columns 62–66. The guarded transfer fits.

For `q=65`, `LastLong.front` reads the collision from the physical
words in rows 8 and 9. On row 11, columns 32–34 carry `2,(8 or 72),
(9 or 73)`. The eastern north line rules out `2,8` by `no28`;
a 72 admits only 72 or 73 to its east, forcing 73 at column 34.
Three local row-10 tiles and the existing row-10 plateau supply the
remaining collar reads. Thus the row-11 transfer from column 35 has
all its dangling seals and its actual eastern root. It excludes the
last long index and proves `maxPreserved 203 203 = 13927`.

At side 161, `trimmed_excludes_of_ge53` admits the height-14 cap
using the physical catalogue directly. The seam check forces the
eastern column to continue the north line or touch the east rim.
At the bottom either the east or the south contact contradicts that
line. The exit theorem therefore clears `23,25,29,31,35` at `k=53`.
The guarded search also works physically at `k=53`: `nested_window`
admits each transfer window at that size, and `trimmed_excludes_of_ge53`
supplies the terminal cap. For `q=39`, `ShortBirth.exclude` seals
columns 24–39 on row 6, with guard column 23 and separate eastern
north roots. The transfer fits from column 24.

For `q<35` the ordinary eastern interval (starting at `3*j+4`)
suffices for the birth collars at `27,33`. For `q≥35`, the full
eastern interval reaches row `⌊q/6⌋`; reading the plain suffix
directly on the last row supplies the seals at `37,43`. Starting the
induction at row 2 needs only `q+7≤k`. At `q=21`, the narrow exit
with one tile of overlap forces a low head at local column 8, enough
for the trimmed cap. For `q=41`, `WideExitCut.front` uses the same
exit chart: on row 7 a middle 8 at column 21 would require the
forbidden `2,8` pair. The remaining 72 forces column 22 to be
plain. The preceding row words seal columns 23–41 at the cut; the
true eastern columns retain their north roots. A guarded transfer
fits from column 23. For `q=45` the row-8 head at column 23 is 9
or 73. Both masks put all marks in the first column of the tile,
so the dangling collars still seal. The north root forces every
tile strictly east of the head to be plain. The first guarded move
starts at column 24 and supplies its own plain guard at arrival:
no assumption that column 23 is 73 is required.

For `q=47`, only six columns of eastern room are available. Seven
tiles of right halo suffice for every `EastBoundaryChart` transition,
and the two-row birth chart can end at the paid column itself.
Consequently `WideExitCut.front` now applies at `q+6≤k`. It gives
the row-8 front from column 26, with dangling lines through 47 and
north feet at 48–52. A guarded route reaches row 28 at column 36
and row 34 at column 40. Its guard at 39 leaves exactly the 14
columns needed for the remaining height 19.

At `q=49`, the seed certifies the row-9 collars from column 26 and the
three actual north feet at columns 50–52. Column 25 can be 129, but
`Break129.no_fast_tail` then excludes a 9 at 26; a 73 at 25 propagates
directly. The guarded transfer fits at `(9,26)`. At `q=51`, the
row-9 head at column 26 is 9 or 73, and column 52 carries the north
root. The plain suffix starts at 27. A medium restart supplies the
straightness needed by the long move, which reaches the height-17 cap
at row 36 with its plain guard at column 39. `NorthCut161` checks
these two strips in 183 and 177 passes respectively.

The final import `GridGraphs.Results.SquareFormula` proves
`maxPreserved n n = squareScore n` unconditionally for every positive
`n`. At side 161 the value is 8791.
