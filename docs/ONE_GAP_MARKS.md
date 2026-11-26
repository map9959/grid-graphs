# One-gap star charges without guessed primal arrows

Consider a side-203 upper witness, with the one-gap perimeter normalized
at NW. Its only isolate is the depth-two charged star. The following
reduction removes **all primal directions** from the local charge tests.
The remaining global condition really is needed: two full-board
counterexamples to the local relaxation are given below.

## Which local directions matter?

* On the perimeter the parent is prescribed by the path to NW.
  The depth-one ring is empty of marks. At a depth-one unmarked site
  with two marked neighbors, its arrow points to the marked perimeter
  neighbor. A leaf always points toward its only marked neighbor.
* Every mark at depth two has a marked perimeter foot two steps away.
  Away from the corners this follows from the frame. At `(2,2)` and
  its images check the four corner words: at least one of the two feet
  is marked. **Exactly one** can be marked in a forest, since otherwise
  there would be a second connection between perimeter vertices.
  The mark's arrow goes toward that foot. Two neighboring depth-two
  teeth cannot be joined by a marked edge; neither can be the other's
  parent. Nor can an empty depth-two site join two teeth: its normal
  neighbor at depth one is empty, and two tangential teeth both already
  point out toward their feet. Thus every empty depth-two site is a
  leaf, except for the charged isolate. These tests give actual local
  directions for the outer three layers without any guessed arrows.
* At depths **three and greater**, the zero-charge table for an eligible
  outgoing arrow `d` has a simpler form. An unmarked site may point to
  any marked neighbor. A marked site may point to any marked neighbor;
  to point to an empty neighbor it must use a preferred direction.
  Preference at `p` in direction `d` is the zero-charge bit for a
  marked center with four empty neighbors and outgoing `d`. This rule
  is checked on **all** diagonal-free star masks, not just the singleton
  mask from which preferences are read.
* An arrow from a mark to an empty leaf is impossible. Hence a bulk
  mark points to an empty neighbor only across a join `#.#`: the next
  arrow continues straight to its other marked end. For **both ends at
  depth at least three**, the two opposite preferences are identical.
  The exhaustive type check at 203 compares 162 pairs of endpoint
  types/directions. For a join to a depth-two tooth only the direction
  **toward** the tooth is possible; check the preference of the other
  end. This converts join eligibility into forbidden three-site masks.

Retain all zero-charge `3 x 3` patches, the actual frame, the depth-two
shell tests, and exactly one uncovered site with charge 72. At every
other site impose coverage. No diagonal contacts are allowed. Forbid
the ineligible `#.#` hops just described. A useful additional necessary
clause requires every bulk mark to have a potential successor: another
mark one step away, or two steps in a preferred direction. At 203 the
mark formulation checks 81 bulk star types and forbids 26,398 physical
horizontal/vertical hops. The type comparisons are direct rational
stencil lookups in units of `1/1008`.

## A signed identity, valid even on cyclic patterns

Let `M` be the number of marks, `E` the number of forced edges, and `r`
the number of runs. For the locally admissible patterns just described:

```
7(M-13928) = 4(E-41207),     5(M-13928) + 4(r-230) = 0.
```

To prove it, orient every forced edge once, **allowing a bulk marked
site to have any number `h` of outgoing edges**. Fix the outer layers
as above. Direct leaf edges toward the mark, and each join toward
the tooth if present, otherwise arbitrarily between its two allowed
ends. Direct adjacent marked edges toward a tooth if present,
arbitrarily if both marks are in the bulk. The only sites at which the
intended outdegree may fail are now bulk marks. Each individually
chosen direction there has zero charge when used alone.

At a noncorner with a fixed mark mask the dual slack is affine in
the indicators “edge `d` outgoing”: only the corresponding edge
marginal changes when that arrow is reversed. In particular extend
`s(empty)` to a set of outgoing edges by adding
`s(d)-s(empty)` for each one. The raw marked sink charge is **576** on
every eligible bulk mask (`depth_two_marks.bulk` checks this using the
raw sink table, not an admissible new root). Thus the extended charge
of a bulk mark is `576(1-h)`. The physical edge-marginal prices still
cancel in the sum, since every forced edge has exactly one direction;
patch overlaps and star/patch incidences still cancel as before. The
corner term is unchanged. The summed charge is both
`72+1008(13928-M)` and `72+576(41207-E)`: there is one NW root, one
isolate, and every other nonbulk-mark site has one outgoing edge.
This proves the first identity. The second follows by subtracting the
target ledger from `E=3M+r-B`, with fixed frame boundary incidences `B`.
Negative aggregate charges in this extension are **not** valid charges
of a rooted tree; they account for marks used as multiple sources.

Equivalently, if `b` is the actual cycle rank and `c` the number of
nontrivial forced components, then `7(M-13928)=4(b-(c-1))`.
In particular a 13928-mark local solution must have as many independent
cycles as detached components. It is a witness only when both counts
are zero.

In particular **a forest satisfying these local rules is upper-optimal
if and only if it has at most 230 runs**. Indeed acyclicity and the
isolate imply `E<=41207`; now both identities force equality at 230
runs, and then there is exactly one nontrivial component. If instead
such a forest misses, its *selected* score misses by a multiple of four,
with seven extra components for every four missing marks. This statement
is conditional on the local rules; it does not lower the unrestricted
upper or exclude the existing 13927 rail.

This also rules out **completing a strictly subtarget local pattern to
score 13928 merely by adding marks**. If `M=13928-4a` with `a>0`,
it has `230+5a` runs. In any diagonal-free superset each new mark has
at most two opposite marked neighbors, so adding it removes at most
one run. Adding `4a` marks leaves at least `230+a` runs, whereas the
upper target requires 230. For the 13908-mark example below, therefore,
changing the spanning-tree completion alone cannot close the gap.

The identity has an all-size version on `n=119+42s`: replace 13928,
41207 and 230 by `U`, `n²-2` and `8n/7-2`, respectively. To see why
no new bulk type or preference pair enters, record on each axis
the distance to an end when it is at most eight, and otherwise the
coordinate modulo three. This determines depth-three membership and
all clipped depth-six stencil coordinates at offsets up to two,
including their reflected coordinates because `n mod 3` is fixed.
All axis classes, and hence their Cartesian products, already occur
at 119. The foot argument uses only the corner words and the two
frame rings. `one_gap_charge_identity --types` independently enumerates
the mark masks, charge table and preference comparisons, and checks
equality of the **actual** 119 and 203 tables as a replay.

## A smaller exact score counter

The `201 x 201` interior splits into `67 x 67` disjoint `3 x 3` tiles
with origins `(1+3i,1+3j)`. On the one-gap local rules **every tile has
one, two or three marks** (the four corner tiles have at most two).
For each tile, `aligned_tile_bound` enumerates the 512 masks, requiring
zero patch charge, no marks on ring one, coverage of its center unless
it can be the isolate, and no forbidden `#.#` in its rows or columns.
For example a nondegenerate bulk tile cannot have four marks: its
potential two-hop joins across its middle row or column index cannot
point in either direction. The finite mask test also checks the less
regular near-frame tiles. No branch length or interface geometry is
assumed.

There are 803 marks on the perimeter (boundary incidences less the
four double-counted corners). Thus reaching 13928 requires exactly
`3*4489-(13928-803)=342` missing marks relative to three per tile.
An equivalent score counter is
`#(tiles with <=2 marks) + #(tiles with 1 mark) = 342`.
It uses two binary indicators per tile rather than a board-wide count
of the 41,209 mark bits. This is a necessary equality, not an
impossibility certificate.

```
python3 -B -m analysis.research_program.aligned_tile_bound
# 203 4489 disjoint tiles, at least one mark each, maxima {2: 4, 3: 4485} target deficit 342
```

## Physical replays

**Bulk phase propagation (all exceptional sides `n>=119`).** Consider
aligned tiles whose surrounding two-site halo is at depth at least six.
In either direction a pair of side-adjacent tiles admits just 182 ordered
mask pairs in the local zero-charge relaxation on their common halo.
No forest or turn-sheet constraints are needed for this test. Every
three-mark tile is a complete row or column. Adjacent three-mark tiles
have the same such row or column; changing phase along a tile path
costs at least one unit of deficit.

More strongly, if the *left* column of a tile is marked, the tile to
its **right** has exactly the same mask, regardless of the neighbor's
assumed mark count. Thus this phase extends all the way to the right
bulk edge. The right-column, top-row and bottom-row phases extend
left, down and up respectively. Oppositely oriented perpendicular
stripes cannot demand different masks at the same intersection. The
middle-row and middle-column masks do not have this propagation rule.

Proof: enumerate the two-tile projections in a `7 x 10` or `10 x 7`
window, imposing the complete zero-charge stars and patches and local
edge directions. Block only the 18 observed mark bits after each
solution. `drat-trim` verifies the exhausted formulas, so the tests
for a unique successor or predecessor are exhaustive. Translation by
three preserves each bulk axis type (`defect_window.table`); reflection
uses `n-1-x`, with `n mod 3` fixed. Every such halo on every tail side
therefore has the representative window's tables. Iteration proves
the ray statement. This is a necessary condition, not a construction.

```
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.saturated_tile_phase --project
```

## Physical replays of full patterns

| Local pattern | Star | Marks | Runs | Forced edges | Cycle rank | Nontrivial components |
|---|---|---:|---:|---:|---:|---:|
| unconstrained connectivity | `(2,5)` | 14000 | 140 | 41333 | 126 | 1 |
| straight attachments constrained | `(197,2)` | 13908 | 255 | 41172 | 0 | 36 |

The latter test forbids any straight forced row segment joining two
perimeter feet directly or via two perpendicular straight legs (and
likewise after transposition). The premise is that the perimeter is
already a path. This eliminated every cycle in the displayed model,
but not the detached rods. Spanning-tree completion independently gives
`(13908,41172,37,41208,13908)`; the best existing lower bound is higher.

```
export PYTHONPATH=target/pb-python
python3 -B -m analysis.research_program.depth_two_marks 203 120 0
python3 -B -m analysis.research_program.depth_two_marks 203 150 2
python3 -B -m analysis.research_program.one_gap_charge_identity target/depth_two_marks_203_{0,2}.marks
python3 -B -m analysis.research_program.one_gap_charge_identity --types
python3 -B -m analysis.research_program.one_gap_charge_identity --examples
```

Specific SAT models can depend on solver version and clause order.
The last command checks the two archived mark patterns directly, including local
slacks and the signed identity. For the exact full-square test,
variant `1` requires a rooted complementary face tree on every free
edge except the isolate's edge toward its side. Variant `6` instead
uses one claimed join per nonroot run and complementary face ownership.
The latter is a Temperley matching: expand each run toward its claimed
join, attach the isolate by its prescribed edge, and root the dual at
the exterior. A directed primal cycle would enclose a trapped dual
cycle, which encloses a smaller primal cycle; neither root is strictly
inside. This finite descent excludes cycles. Any SAT result of an exact
variant must independently pass forced-edge and spanning-tree replay.

As an arithmetic control, imposing the new forbidden hops, tooth
parents and the phase-five isolate in the period-six GF(2) marginal
test still leaves all six eligible site buckets in every one-gap
frame. `python3 -B -m analysis.research_program.one_gap_hop_parity`
replays that finite quotient. Survival of a bucket is not an integral
mark pattern.
