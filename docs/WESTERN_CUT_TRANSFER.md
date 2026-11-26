# Western continuation is not the same as rooting at a cut

For the [eastern diagram](JOINED_ARM_BUDGET.md), **no fully rooted
four-column cap extends even one more column west**. This accounts for
*every* choice of marks in the four columns and every cost, not just
the minimum-cost example. If a component is allowed to stay unrooted
at column four, there are six-column fillings in which it has reached
a tooth, at the exact whole-square deficit. But again, none of the fully
rooted six-column caps extends to a seventh. These exclusions are
conditional on the incoming diagram. Below are also consequences for
opposing straight arms without a prescribed eastern diagram.

### Simultaneous transfer

Use tile columns in transposed coordinates (tile masks and physical
catalogues transposed together). Generate complete plaquettes outward
from the common eastern cut. On the **same** columns of marks keep two
frontier partitions: one for the first four new columns, one for all
five, or analogously six and seven. Each inserts all physical forced
edges, including cross-cut edges in the larger partition. Teeth are
tied to the perimeter root. A repeated connection is rejected; a
marked component that disappears must have reached the root, or an
open cut if that particular partition allows escapes. The older east
is represented by its exact partition and one mandatory attachment,
as in the previous transfer. Rooting the inner partition is a
testable condition, **not** imposed when measuring unrestricted drift.
A bitset records *all* total deficits, counted once on the larger band.
The transfer makes no SAT call.

For every tested starting `s` (the odd integers from 13 to 27), the
four-column spectrum agrees with the independently implemented rooted
band checker. With the fifth column present the spectrum is empty if the
first four must already be rooted. With six free columns and rooting
required only at their outer edge, the minimum is `s+23`. Backtracked
models passed a separate graph traversal on the unsliced eastern region:
each component containing a mark is a tree with exactly one tooth.
For the eight classes of `t` (where `k=39+14t`) the six-column costs
are `46,44,42,40,38,36,50,48`. The remaining western bands can pay
the balance of `198+72t` in their previous projection. An increment of
eight in `t` adds 504 deficit in the diagonal and 72 in seven new
western bands. The six-column cap's long homogeneous southern tail
has zero incremental cost: its 448 tiles and final 192 propagate
across every new column by the certified catalogue, so adding or
removing middle copies subdivides rooted paths and adds leaves.
No eastern cap in this test is a spanning-tree construction.

### Obstruction even when western rooting is delayed

Let `i` be the tile-column index of the initial interface, from the
west. For the diagonal it is `k-H`; its north arm has `s=k-4H/3`
tiles before the two transition tiles. After **seven** freely filled
columns west, the straight southern suffix starts no later than tile
row `s-7`. To test this, mark a violation if any tile between `s-7`
and the final clipped tile (exclusive of the latter) differs from
448 at the new cut; no violating terminal state exists. Neither the
inner nor the outer cut has to be fully rooted for this test.

In the distance-five chart the existing plateau bound, applied in the
transposed direction, gives `(i-7)-5 <= 3*((s-7)-1)`. The checker
compares the actual catalogue words before using the transpose. Thus
**`i <= 3s-12`** is necessary. For the unadjusted eastern diagonal
this rules out a full continuation at every `t>=9`, and also at `t=4,5`.
Indeed the eight starting `i` are `27,29,31,33,35,37,51,53`;
`t -> t+8` adds 28 to `i` and leaves `s` unchanged. This excludes
that interface even if all unfilled western marks and the order of
root attachment are free. It does not require more finite board proofs.
The position arithmetic and the `t>=9` implication are also checked in
[`WesternCutBound.lean`](../lean/GridGraphs/Geometry/WesternCutBound.lean).

### A cost bound without a prescribed eastern diagram

In canonical one-gap frame `0133`, take a bulk column at index
`13 <= i <= k-7`, so its seven western neighbors traverse bulk
transverse catalogue types. Suppose the transposed word begins
`6,7,...,7` with at least 13 tiles in this northern arm, and ends
`448,...,448,192` with at least 12 tiles in the southern arm.
Then **the column has deficit at least six**. No location of the
north isolate is prescribed. This is a conditional cost per column,
not a proof that every column contains both arms.

The equality budget is `198+72t`. Since other tile deficits are
nonnegative, at most `33+12t` columns can qualify. Among the `k-19`
columns indexed `13,...,k-7`, **at least `max(0,2t-13)` must lack
one of the two specified long arms**. This consequence applies to any
one-gap equality witness, not just the diagonal family.

* The two clipped end tiles already cost two. Enumerate bulk
  mask-pair walks from 7 to 448 with at most three more units of
  deficit. Collapse equal consecutive full masks but keep deficient
  self-loops and their cost. There are just 14 intervening words.
  The only interior full phase in them is 56.
* For each possibility the seven-column transfer now uses **only**
  the rooted contacts implied by the straight north arm. Everything
  else at the old cut is open; no unique exit or prior component
  partition is assumed. Take the union of all six additional certified
  north-star phases at each affected position, even permitting
  inconsistent choices between windows. There is no terminal state,
  on either axis, for any of the 14 words.
* These are unbounded-length tests. After the north fringe, close
  the reachable state set under arbitrarily many extra 7 columns.
  For an intervening 56 allow a single copy, or two with a second
  independent closure under further copies. The forced homogeneous
  448 tail compresses as above. Thus the exclusions do not depend
  on the particular lengths at which a word was discovered.

There is a companion spatial bound. If exactly two tiles separate the
maximal arms, five ordered mask pairs are locally possible. Only
`(16,16)` survives seven further columns; even that pair forces the
new southern suffix to start at or before `s-7`, where `s` is the
northern arm length. The checker covers `s=13,14,15` and every `s>=16`
by closure. With the full union of star phases the suffix still cannot
shrink westward. Its start can stay at row 1 for at most two columns
and at any later interior row for at most three. The row-1 test keeps
two tiles, west/north tooth and straight-arm root contacts; the other
tests keep three. Hence `(i-7)-5 <= 3*(s-8)+2`, or **`i <= 3s-10`**,
even for an arbitrary north isolate and unknown data east of the cut.

```
export PYTHONPATH=target/pb-python
python3 -B -m analysis.research_program.western_cut_transfer
python3 -B -m analysis.research_program.opposing_arm_cost
```
