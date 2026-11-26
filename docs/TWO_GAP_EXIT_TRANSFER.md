# What transfers from the side-329 two-gap proof?

**Uniform restriction.** Put `n=329+42t`, `t≥0`. If the exceptional
upper target is attained with two gaps, normalize the frame to `0011`
with the short arc on the north. There is a **vertical** marked-center
bond in the deep aligned tile square. Hence there is no horizontal
marked-center bond there. The inward exit on the short arc has column
`d=107+3j`, `0≤j<39+14t`. In particular it is at least 107 steps
from **each** north corner. These conditions do not exclude all exits:
at 371 they still allow 53 columns, `107,110,...,263`.

## From a physical proof core to bounded tests

`drat-trim -c` retained 75,938 of the 20,419,034 input clauses in the
[329 certificate](EXCEPTIONAL_329.md), using 2,460,915 resolution
steps. Reconstructing the physical variable names gives 15,030 mark
IDs reaching depth 59, 12,898 face-owner IDs reaching depth 57, and
1,367 extension IDs reaching depth 58; only four of the auxiliary
gap-tooth color IDs were needed in this core. The shallowest three-row
cross section in the interior scan was centered at row 63, reaching
depth 5 from the lateral sides. The shallowest three-column section
was at column 15, reaching depth 20. Thus periodic stencil prices
alone do not make this particular core a translated corner proof.
The core need not be minimal.

Root at NW. The north arc is not the root arc. Its sole inward arrow
is at the foot `(0,d)` of the ordinary bridge tooth `(2,d)`; on the
north arc all the other arrows point towards this exit. The marked
ordinary north teeth other than the exit point outward to their feet.
The two open words can be changed independently without moving the
bridge, by the [ordinary-endpoint and exchange theorem](EXCEPTIONAL_287.md#all-size-reduction-the-two-gap-perimeter-can-be-prescribed).
Change to `0211`, still rooted at NW and still exiting through the
same north site. The [width-seven exit theorem](ODD_SINGLE_DEFECT.md#a-uniform-strip-test-for-the-two-gap-exit)
for that word now applies: `d=2 mod 3`. Its reachable-state replay
gives `repeat=(27,69,232), zero=False, top phases=[2], short-end codes=[]`.
A gap tooth cannot be the bridge endpoint, so initially `5≤d≤n−6`.

In each box restrict the actual NW-rooted forced forest, the sole
72-unit exit, arc ownership, turn sheets and the complementary face
matching. All marked north teeth in the crop have distinct component
labels: the only component with two teeth has one on each arc, and
the NW gap tooth belonging to the long arc is not a bridge endpoint.
In a corner box *not containing the short exit*, **all** visible
teeth, even those on the lateral side, may be given distinct labels:
the crop cannot contain both bridge endpoints. Propagate equality
only across edges forced by marks. No marks are imported from a donor.

### An exit forces a deep bond normal to the north side

Work by contradiction: forbid vertical bonds from every aligned
center at depth at least 14 to its north/south neighbor in the box.
This test does not require the stronger row/column mask implications.
Coordinates and hashes below refer to the representative 329. Every
range uses step 3.

| exit test | domain (width × height) | CNF SHA-256 | DRAT steps |
|---|---|---|---:|
| at distance 5–59 from NW | left 104 × 74 | `852deeb28da21efbe15c10b7e0aae8b650150c073cacf77cfbbc45b074d172b6` | 79399 |
| at distance 5–59 from NE | right 104 × 74 | `37807370cafb60105f03772ce2915ba00c23ea578f286f24e18f09d072798990` | 72954 |
| at least 62 from both | 87 × 65 centered at column 164 | `840bb93cadcd25e6b91cdd8b0c443903a354cba6465691ec79dec8e7eeaa6513` | 5836 |

Each is UNSAT. Thus a vertical bond is required in the indicated exit
window. The [no-cross theorem](BULK_AXIS.md) then forbids every deep
horizontal center bond on the board.

### Link the two ends by the actual tile-row condition

A global flag for each deep tile row is true if it contains a vertical
center bond. If true, *every* deep tile in that row belongs to the
certified `ROW` mask list. Identify just these flags between two
boxes; each box retains its own marks, matching and other auxiliaries.
This does not assume matching marks or guess an interpolation between
the boxes: the flags of the actual board supply one consistent
assignment. For an exit within 104 of a corner, use the 150 × 81
charged box at that end, and a clean 104 × 74 box at the other.
The two checked disjunctions eliminate 34 exit offsets each:

| charged end | CNF SHA-256 | DRAT steps |
|---|---|---:|
| NW | `27883342b748b942eb5a9d52ea0049a0f8fc3ead5b20d51e37978817c4fb0cf5` | 190145 |
| NE | `5108d1655fd5d626a9033a0837ab5884cc4b0a35de508d6c7979d199c46450a8` | 194344 |

### Why the checks apply to every enlargement

Translate an end box along with its own corner. Translate the middle
box by `d−164`, a multiple of three. All tests at a site use the true
boundary, distances to the ends clipped at a fixed threshold, and
residues mod 3. Keeping the first and last sixteen coordinates and
the residue suffices even for the depth-14 axis test. In the middle
case both end distances are at least 62, leaving at least 17 even
after the 43-site half-width and a two-site halo. The distant end of
each corner box remains beyond every threshold. Reflection preserves
the corresponding labels since `n mod 3` is fixed. Thus all local
stars, patches, incidence directions, face availability, and deep
center tests are unchanged. The same physical row numbers are used
by both ends. Row flags with no visible tile add no restriction.

The direction on a visible perimeter edge is fixed by the path to NW
or the path to the selected north exit; at the clean end it depends
only on which side of the window the exit lies. The one-exit selector
list therefore maps bijectively in each charged box, and no selector is
required in the clean box. A putative larger board would restrict to
one of the *same* unsatisfiable formulas, not merely one with the same
counts. The ledger independently compares clipped coordinates, frame
bits, root directions and covers for all eligible distances at 329,
371 and 413. `lean/GridGraphs/Geometry/TwoGapExitCover.lean` checks
the all-size arithmetic of clipping, translation, and the residual range;
the SAT certificates are checked separately by `drat-trim`.

## What still survives the transfer tests?

For a middle exit tie the two clean end boxes and the charged middle
box by row flags. Also test the middle marks rooted on the short arc
from either end: there are canonical gap-word choices allowing either
corner root, with no charge on the middle north interval. The three
rootings share physical marks, not hypothesized interior arrows.

Link each end to the middle by projected six-site-high horizontal
tracks. Each step uses a certified square of four tiles in the clean
side or bulk from the reference `0133` catalogue: away from the
corners and the exit the straight north frame and east-going arrows
agree, and on the other side of the exit the words are reversed and
reflected. Respect both row-activation flags and the surviving axis
in every intermediate tile. For west and east track lengths `L,R`
in tiles, the chosen interface positions give
`L=(d−89)/3`, `R=(n−d−90)/3`. Thus `L+R=50 mod 14`.
For each graph the verifier computes exact ordered endpoint relations;
the powers at lengths 26 and 40 agree, so composition proves period
14 thereafter.

**This projection still admits `d=185` at every `371+42t`.** At 371
both lengths are 32; hold `L=32` and take `R=32+14t`. With the
length selectors fixed the checker completed the SAT assignment and
checked all **7,694,134 clauses**. Keep those window assignments and
use the equal ordered endpoint relation on every lengthened right
track. This is a model of the projection only: different tracks are
not required to use the same marks or owners in their overlapping
interiors. It is not a tree and does not show upper attainment.

Separately, a width-eight annulus using matching, no isolates and
ordinary bridge labels admits a literal 42-site repeating block.
Replaying the saved assignment at 329 and 371 checked 1,609,156
and 1,819,604 clauses, respectively. At widths 16 and 18, forbidding
horizontal bonds and insisting on the same specific repeated block
gave checked UNSAT quotients; an equality forest need not satisfy
that imposed repetition. Neither outcome closes the middle-exit case.

## Reproduction

```
export PYTHONPATH=target/pb-python
target/drat-trim/drat-trim target/two_gap_329_0011_axis_ordinary.cnf target/two_gap_329_0011_axis_ordinary.drat -c target/two_gap_329_0011_axis_ordinary.core
python3 -B -m analysis.research_program.two_gap_329_core
python3 -B -m analysis.research_program.exit_pump 7 119 0211
python3 -B -m analysis.research_program.two_gap_exit_box 104 74 32 left 120 --axis=2 --exits=5:59:3 --bond-only
python3 -B -m analysis.research_program.two_gap_exit_box 104 74 296 right 120 --axis=2 --exits=269:323:3 --bond-only
python3 -B -m analysis.research_program.two_gap_exit_box 87 65 164 flat 90 --axis=2 --bond-only
python3 -B -m analysis.research_program.two_gap_shared_rows left 180 --axis=1
python3 -B -m analysis.research_program.two_gap_shared_rows right 180 --axis=1
python3 -B -m analysis.research_program.two_gap_transfer_ledger --drat
python3 -B -m analysis.research_program.two_gap_shared_rows flat 180 --axis=1 --tracks --lengths --fixed=32,32 --reroot
python3 -B -m analysis.research_program.two_gap_periodic_rim 8 119 36 30000
python3 -B -m analysis.research_program.two_gap_periodic_rim 8 119 36 0 --replay
```
