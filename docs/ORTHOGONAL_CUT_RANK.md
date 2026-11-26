# Combining the two cut directions at side 103

Update: the [integral floor test](INTEGRAL_RANK_FLOOR.md) excludes the
entire exhibited direction histogram by charging actual coarse turns.

## Exact joint price

Start with a marked forest. Delete row `y` and repair its single seam;
independently delete column `x` and repair its single seam, using the
[supported-path repair](SINGLE_CROSS_MINOR.md) on the original forest in
both cases. Let `d_y,d_x` count erased and demoted marks and `s` their
overlap as sets of **original sites**. Apply both sets of demotions
before deleting either line. Each individual cut is still feasible.

On the smaller square take the inherited edges and all supported
bridges. Call this forest `B`. The supported bridges expand to
internally disjoint forced paths. Let `R,C` be the other compulsory
row and column bridges. Both `B+R` and `B+C` are forests: for the
first expand just the supported column bridges into the single-row
repair, and for the second interchange the axes. These expansions
avoid the central deleted vertex. The exact remaining cycle rank is

```
μ = |R| + |C| - rank(R+C after contracting B).
```

In particular it is the dimension of the intersection of the two
graphic edge spans on the **same** contracted forest. Keep all of
either direction and complete to a maximal forest with the other.
Each rejected edge has a unique marked owner in its direction, so
erasing `μ` such marks suffices. Both choices of direction are
physical. With `g` new compatible marks found after repair, one obtains
loss `d_y+d_x-s+μ-g`. No separate charge for all near off-skeleton
marks is needed.

There is a second way to count `μ`. In the four quadrants before
gluing, keep every actual component touching bridges of **both** seam
types, including isolates. Let their number be `t`; let `a,b,h`
be the numbers of classes of those components after row gluing,
column gluing, and both gluings respectively. Contract each of the
two one-direction forests: each shared component contributes one
bipartite incidence edge. Thus `μ=t-a-b+h`, the same join-loss
identity as for a single lifted cut. If `t_Q` are the four separate
quadrant counts, collapsing all row-side classes in each half and
likewise all column-side classes can only increase this cycle rank:

```
μ ≤ sum_Q max(0,t_Q-1) + [all four t_Q positive].
```

Thus, for example, at most one shared class per quadrant costs at
most one mark beyond the union of the one-dimensional losses.

## Why a constant interaction charge cannot be assumed

For **every** `k≥1` take side `6k+7` and `k` concentric marked
perimeters spaced three apart. Omit one neighbor per corner so
off-rim bonds are leaves. In addition, omit a consecutive pair on
the left side crossing the central row and a consecutive pair on the
top side crossing the central column. These are disjoint from the
corner omissions, even at the innermost side 13. The two pairs are
the only missing perimeter bonds. Either central cut alone heals
just one; after both cuts each perimeter has a cycle. Spacing still
separates different perimeters, so the rank is exactly `k`. At 103
this gives `0,0` paid single-axis repairs and common rank **16**.
It is a cut obstruction, not a 3647 forest; refill can still pay.

## A partition-independent projection

In `p_y` count marks on the line and unsupported bonds for which
the blank surviving endpoint was **not** an original isolate. Define
`p_x` by transposition. After erasing the owners of these risky bonds,
any remaining unsupported bond attaches a previously isolated site.
It acts as a leaf unless the other seam also attaches there. Such a
double hit is possible only at the four corners of the central face.
If two corners are double-hit they are opposite and have the same
pair of marked owners. One further demotion suffices for all double
hits. If `(y,x)` is marked a double hit is impossible (its diagonal
neighbors cannot be marked), and the erased intersection mark was
counted twice. Hence the attainable loss is at most
`p_y+p_x+1-2[(y,x) marked]`. This does not assume the marks on
either seam repeat. The implementation also checks the repaired trees.

## Testing the first surviving component stratum

There is a new necessary inequality for every no-pitch 3647 candidate.
Let `E₀` count junctions with **none** of their own midpoint slots
marked. An unmarked such junction is physically isolated. A marked
one without any realized incident coarse edge also cannot reach
another junction: its immediate midpoints are blank, its diagonal
neighbors must be blank, and a marked far midpoint would realize
the edge. These junctions cost separate full-forest classes `A`.
For each remaining empty-stub junction choose its axis along a
realized edge: the unfilled slot on that edge costs one first
skeleton slack. The choices can all be made together. Some junction
is not an isolated empty-stub junction: without any marked midpoints
the score is at most `m²+2k²` (at most two marks per open coarse face).
The [no-pitch identity](SKELETON_CROSS_RANK.md) now gives

```
F - j ≥ 43 + E₀.
```

We tested the first possible stratum `F=43`, where `C=A=1, j=0`,
and all residual slacks vanish. To measure these ranks on the sector
chart, root the full component of NW at NW, every other component
containing junctions at one of its junctions, and all others
arbitrarily. The junction sinks count `A`. In an old junction
component exactly one arrow leaves the old skeleton bonds unless
that component already contains its full root. These departures
count `j`. Membership and departures are star events: a vertex is a
junction or is incident to an edge forced by a skeleton mark. The
same count works after pruning all off-skeleton leaves. To count a
realized coarse edge, at each of its midpoints let `f` be its mark,
`u` the near junction's mark, `v` the other midpoint's mark. The two
contributions `v*(f+2*(1-f)*u)` sum to twice the edge indicator.
Consequently all three counts are measurable without guessing a
terminal partition. Physical union-find replay checks the identity
independently of this chart.

Additional necessary restrictions at the floor used in the test:

* Every coarse tree edge points along its whole three-bond path
  toward NW. Exactly one endpoint sends an arrow along it; an
  unfilled predicted slot cannot lie on a realized edge. Both
  missing slots on the same predicted edge cannot pay for its one
  failure.
* On a junction line either there is no H and just one vacant
  junction, or each internal gap between H runs is a single vacant
  V with both incoming midpoint hits. Any other vacant V must have
  at least one actual hit. This is a finite word constraint on the
  triples (left stub, junction, right stub), from the two zero
  slacks. A V assignment means both horizontal owned slots are
  empty since empty-stub junctions are forbidden. No-pitch lines
  off the junction rows also cannot have all teeth marked: the
  extra off-phase mark would join two old junction classes. The
  transposed restrictions use the same marks.
* In each 4-by-4 coarse face, wire its four junctions **after**
  inserting the skeleton bonds. The remaining marks must not produce
  a cycle. For equal perimeter marks one may reject a face if a
  strictly larger feasible refill induces a refinement of its wired
  port partition. This is safe against every exterior consistent
  with the common skeleton tree.
* The chart includes the row and column no-cheap-cut conditions,
  including the isolate discount above. In the latter projection the
  count of risky bridges is bounded by both the number of possible
  unsupported bonds and the number of eligible nonisolated blank
  heads in the matching sector bucket. The chart is D4-averaged;
  summing over all row-column pairs in a band of size `s` gives
  `2s * (marks + risky heads) ≥ 78s² + 2*(marks in band square)`.

**Exact outcome:** even these constraints admit score 3647
*fractionally*, with `F=43,C=A=1,j=0`. All 9,102 equations and
inequalities of the projected model (including the target count),
the nonnegativity conditions, and forbidden sinks are checked over
the rationals. Moreover the *same* rational weights on **20 actual
NW-rooted coarse spanning trees** reproduce all 57 outgoing-direction
histograms and all 17 realized-edge histograms in the test. Every
tree is reconstructed and checked to reach NW from each of 1,225
junctions. The fit uses 3,223 nonzero chart variables. The saved
vectors are proof artifacts of the failure of this relaxation; none
is a physical side-103 mark mask. In particular the certificate
does **not** evaluate `μ` on a single integral 103-square.

```
python3 -B -m analysis.research_program.orthogonal_cut_overlap
python3 -B -m analysis.research_program.skeleton_exit_chart --physical
python3 -B -m analysis.research_program.skeleton_exit_chart 4 4 103 --lines --faces --isolate-cut --replay
rustc -O analysis/research_program/skeleton_arborescence.rs -o target/skeleton_arborescence
python3 -B -m analysis.research_program.skeleton_rooted_mixture
```

The missing step is to control the common rank and refills on the
**particular** row-column pair chosen in the same physical forest.
Marginal tree realizability and separately priced directions do not
give that coupling.
