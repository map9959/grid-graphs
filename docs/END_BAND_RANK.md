# End-row replacement priced against the actual exterior components

The end rows of a proposed frame need not already be pitch. There
is an arbitrary-width price for imposing pitch on **both ends at
once**, including the possibility that the two repairs compete for
the same interior component. The result is a test, not a universal
no-loss straightening lemma.

Use side `n=3k+1 ≥ 103` and cut depths `1..9`. For full-width cuts
use all pitch centers `0,3,…,n-1` and the two-profile comb bound.
Alternatively first perform the [sparse side-hole repair](SPARSE_COMPONENT_EXCHANGE.md);
let `S` be its gain (or use its certified lower bound). The two side
bars at columns `3,n-4` are then solid in the frame. On each end only
the internal centers `6,9,…,n-7` need attention: the outer teeth are
on the bars. The columns immediately inside the bars are empty along
all three band rows by diagonal exclusion.

For each chosen center take its three sites along the end row
(truncate at the physical board edge) and the same columns on the
two neighboring rows. One may use every tile or just the defective
tiles whose middle word is not pitch. An untouched good tile's
boundary column facing a repaired tile is empty in all three rows:
its middle bit is zero, and its normal neighbors are diagonal to the
good tooth. Hence the new tile has no lateral contact there.

Remove these tiles from the forest. Write `m` for their old marks,
`t` for the number of removed tiles, and compute the **single**
partition of the remaining physical sites, isolates included. Include
both ends in this computation. Reinsert one pitch center per tile.
The only other sites that can be marked are its two normal neighbors,
one toward each backing row two steps from the end row.

* If the backing site on the center column is marked, its edge into
  the tile is compulsory, even if the normal neighbor remains blank.
  Join the tile's private tooth node to that backing component.
  If the compulsory graph is cyclic, the prescribed cut cannot be
  imposed with the exterior fixed. In the repair version, take a
  spanning forest of those edges and delete the backing mark of
  each rejected edge, at cost `z`. Recompute the exterior partition:
  deletions can split classes but never merge them. The surviving
  compulsory spokes still form a forest.
* Adding a normal mark is forbidden if either adjacent tangential
  site in its backing row is marked (a diagonal pair). Otherwise
  its lateral leaves are unattached. If the outward edge was
  compulsory already or lies outside the grid, the mark is free;
  let `f` count these choices. In the remaining case the mark adds
  exactly **one** new contact, to an unmarked backing vertex. Include
  the vertex even if it is an isolate. Other unused off-center sites
  adjacent to backing marks are just leaves.
* After contracting the compulsory graph let `r` be the graphic rank
  of the optional contact edges: the number of successful unions when
  all are tried. Add precisely a maximal independent set of them.
  This realizes `t+f+r` marks. Conversely every aligned filling with
  this exterior can use at most that many: every paid normal mark uses
  one of those edges, and their union cannot contain a cycle. Thus the
  price is exact **for the final fixed exterior**; the preliminary
  choice of which backing marks to delete need not optimize the repair.

Applying the aligned theorem to the physical result gives

```
original score ≤ comb(n) + m + z - t - f - r - S .
```

For the full-width test one can take `S=0` and use the
[whole-row theorem](UNBOUNDED_RAIL_SEAM.md). No initial end bits or
side bars are then assumed. For the shorter cut use the joint frame
theorem, and the gain of its side repair if one was needed.

**A structural sufficient condition.** If both backing triples are
blank at each repaired tooth, there are no compulsory spokes. With
both backing vertices on the board, one optional join per tooth is
always possible. The extra joins are exactly the rank `r_pair` of
linking the two backing components of each tooth, using all teeth
jointly. (An absent boundary vertex acts as a private free endpoint.)
Thus `m ≤ 2t+r_pair+S` suffices for the comb upper. This allows an
arbitrary number of displaced end teeth. The test can distinguish
two instances with identical marks in the cut bands but different
connections through the interior.

### Limits of the replacement, at arbitrary width

Place the comb of side `n-30` in the center. Add five concentric
perimeter paths of sides `n,n-6,…,n-24` with the five standard
omissions on each path (see `PAPER_CONSTANT_GAP_LOWER.md`).
Distinct supports are separated by two blank layers. The paths add
`20n-285` marks; the resulting feasible score is exactly **comb minus
18**, independently of `n`. This is a control for the method, not a
counterexample to the comb upper bound.

On the long central portion of each side the first 13 rows are
parallel full bars at depths divisible by three, empty otherwise.
For *every* allowed cut, each interior pitch triple there initially
has three marks (one full tangential row). If the cut depth is not
divisible by three, one backing row is full; normal marks toward it
are forbidden. Each tooth has at most two marks including the center.
No compulsory edge there needs pruning: the tooth has at most one.
If the depth is divisible by three, both backing rows are blank,
but each is attached to a continuous bar one row farther away.
Hence the optional pairs in this central stretch all join the same
two classes, contributing rank at most one in total. Again the new
count is at most two marks per tooth plus one for the whole stretch.
End effects have bounded size. Thus this fixed-exterior alignment
can lose `n/3-O(1)` marks **per end**, in both orientations. Using
only the bad tiles does not fix the example: the original middle
words there are either completely full or completely empty.

Nor can a three-column side repair on the long straight part pay
that linear loss: its old wing already has one mark per row up to
`O(1)` ends, and with the solid bar the depth-three wing maximum is
at most one per row plus a constant. In an induction, these concentric
collars would instead be candidates for stripping: removing all
five costs **18 less** than the comb increment over those 30 sides.
A remaining issue is to prove a reduction when the exterior both
resists the end exchange and has no such removable collar.

### Checks

At 103, in a forest with off-phase marks on all nine northern candidate
lines and a displaced southern tooth, the side repair gained one.
For just the four bad triples the inventory `(m,t,f,r,z)` was
`(6,4,4,2,0)`; the end repair gained four. Physical tree completion
checked the result. On the five-path control, direct enumeration of
the 81 full-width cut pairs in **each orientation** gave best gains
`-50` and `-51`. Independent small-board enumeration checked 2,048
normal-row masks, including infeasible compulsory partitions.

```
python3 -B -m analysis.research_program.end_band_rank
python3 -B -m analysis.research_program.end_band_crosscheck
python3 -B -m analysis.research_program.end_band_obstruction
(cd lean && lake env lean GridGraphs/Geometry/EndBandRank.lean)
```
