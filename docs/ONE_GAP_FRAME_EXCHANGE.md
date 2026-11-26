# A one-gap upper witness needs only one canonical perimeter

Let `n=35+42t >=119`. If a one-gap forest attains `U`, normalize the
gap to NW and transpose the entire square if necessary to put its
isolate at `(2,d)`. **The perimeter can now be prescribed to be `0111`,
without changing a single interior mark or moving the isolate.** This
removes the frame choice from an *existence* test. It does not assert
that some `d` is feasible.

Here is the gluing argument. All vertices of the old perimeter lie on
one forced path, and the ring at depth one contains no marks. Remove
all perimeter vertices. A depth-one site has at most one inward
neighbor at depth two and no edges to other depth-one sites. The four
corners of the inner square are isolated there. A depth-two mark has
at least one marked foot on the old perimeter. Two distinct such marks
cannot lie in one component of the cut forest: their two paths to the
old perimeter, together with its path between the feet, would close a
cycle. At a corner, the two possible feet for the *same* tooth are
both marked in word 1 or 3; this excludes the tooth there. At the gap
one of the feet is missing, and its intervening depth-one site needs
coverage. The only possible covering mark is the NW tooth `(2,2)`,
since the unique isolate is at depth two.

Consequently distinct depth-one sites lie in distinct components of
the cut forest, with the **sole exception** of `(1,2)` and `(2,1)`
at the gap tooth. Restore any one-gap perimeter with the gap still at
NW, even facing the other way. Each inner corner contacts at most one
marked perimeter neighbor; every other depth-one site has just one
possible exterior neighbor. At NW the restored frame selects precisely
one of the two feet. Thus each old component attaches at most once to
the new perimeter path. The union is a forest, and the perimeter has
exactly `4n-9` marks, the same as before. Completion gives at least
`U`, hence exactly `U`. This argument also explains why simply moving
the gap to another corner does **not** work.

## Tight growth into the adjacent solved progression

Put the canonical old square in the southeast of side `N=n+3`, i.e.
translate it by `(3,3)`. Keep every old mark. Add the sites

* `(0,j)` for `0 <= j < N`, `j != 3`;
* `(i,0)` for `2 <= i < N`;
* `(2,3)` and `(N-1,2)`.

These are `2n+5` new marks. To check acyclicity it suffices to contract
the whole old perimeter to a terminal, retain each forced edge from
an old boundary site to a new site, and test the small L graph (parallel
contacts count as a cycle). In the straight middle of each arm,
extending its length subdivides the outer marked bar and gives the new
bar vertices distinct pendant neighbors. The forced edges from the old
marked side to the innermost new line are pendant at the terminal;
they do not meet the bar's leaves, since the bar is three lines away.
The two ends and elbow are independent of the arm length. The replay
below checks the contracted forest and the homogeneous middle, not the
existence of an old witness.

Here `U(k+1)-U(k)=6k+9=2n+5`. Therefore the grown forest would be
**optimal on the next side**. This is a restrictive equality, not a
contradiction: the neighboring rational dual has `13/14` slack rather
than `1/14`. At 245 the canonical growth spends all `936/1008` of the
new budget in individual lower bounds on known or partially known
patches and stars. The old isolate, now at depth five, can have zero
star charge: its centered patch costs 72 units. It would be incorrect
to apply the previous side's single-defect theorem to the grown board.

```
python3 -B -m analysis.research_program.frame_exchange_replay
```

### The three-layer growth gain cannot be increased by changing the annulus

Keep the one-gap interior, discard the entire perimeter, translate
it into a square of side `n+3` (all sixteen translations by `0..3`
in each coordinate are allowed), and freely re-mark the entire
remaining annulus. Its maximum is at most `6n-4` marks for every
`n=35+42t` for which the one-gap crop conditions hold. Thus the
net gain over the removed `4n-9` is at most `2n+5`: the construction
above already achieves the maximum over all placements. A contradiction
from gaining `2n+6` this way is impossible. This is an upper on
the annular replacement, not an existence statement for the crop.

Delete pendant contacts with the hole. Each inner corner can join its
two incident outer sites by a path exactly when both are marked;
the joined pair of NW ports gives one further such path. All other
old depth-one sites are in distinct components. Thus the annulus
frontier needs only the ordinary grid edges forced by either endpoint
and five additional links forced by both endpoints. It rejects cycles
by union-find and maximizes the mark count for every frontier state.

There are ten placements up to transposition. At the reference side
77 the largest value is 458. In each of the four straight blocks,
compare states after 12 and 54 slices: every later maximum is bounded
by the earlier one plus the block's shift. The four shifts sum to at
most 252. The transition in the intervening 42 slices can be repeated:
the active columns and their keep/forget indices depend only on the
fixed strip thickness and traversal order there. Neither the corners
nor the five extra links move relative to their block ends. The
checker compares the full relative transition sequence after inserting
all four runs with the separately generated side-119 sequence. Max-plus
monotonicity propagates the bounds through all subsequent blocks.
Hence each further side increment of 42 adds at most `252=6*42` to
the upper. The smaller reference 35 is also checked directly.

```
rustc -O analysis/research_program/annular_frontier.rs -o target/annular_frontier
python3 -B -m analysis.research_program.annular_growth_pump
```
