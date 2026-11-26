# A smaller-square deficit from the marks that lock its perimeter

At 103 the [locked-fringe tree](CROP_END_COUPLING.md) loses **806** designated
marks on the crop to 91, against a comb increment of **789**. Keeping
the second row fixed allowed at most five net marks to be recovered.
Instead, release the blockers themselves. The unrestricted upper at
91 is 2858. The following are **conditional** improvements to it:

| Information used | Guaranteed improvement in the crop | Crop upper | Upper transferred to 103 |
|---|---:|---:|---:|
| Removed collar, four double-post windows and their seam words only | 23 | 2835 | **3641** |
| Actual backing at the windows | 32 | 2826 | **3632** |
| Also the holes three rows inward and their backing | 64 | 2794 | **3600** |

The first row holds for **every feasible completion** of the observed
collar and local words, without fixing any of the backing teeth, their
connections, or the rest of the smaller square. The last two rows use
more of the actual tree. These are bounds on the original designated
marks in the crop: if they can be increased by `G`, their count was
at most `P(m,m)-G`. This is valid on the full-degree sites of any
original spanning tree by restricting its forced forest.

## Physical exchange at any length

Use disjoint straight windows with their one-site pads disjoint, away
from corners. Use coordinates `(d,x)` with `d=0` on the crop rim. In
`l≤x≤r` erase rows 0 and 1, initially putting a solid bar in row 0.
Let `H` be the old vacancies on that bar and `B` the old row-one marks.
The nominal gain is `H-B`. All the stars of retained marks outside
the windows remain in place.

Contract the fixed exterior components. Represent each proposed bar
by **one distinct node**. Its two end edges go to the exterior seam
sites. A seam whose exterior endpoint is marked has weight two,
otherwise one. Each newly attached row-one leaf which already touches
the exterior gives a weight-one contact with its actual component.
This includes lateral contacts at the ends and marks in backing row
two; isolated contacts cause no cycles. Keep a maximum-weight forest
of these edges **across all windows together**.

* For a rejected leaf contact, omit the bar mark over the leaf.
* For a rejected seam with blank exterior endpoint, omit the end
  mark. If the exterior endpoint is marked, omit the first **two**
  marks: the first vertex still attaches to the exterior but the
  edge to the second vertex is now absent.

These physical omissions cost at most the rejected weights; overlap
may make them cheaper. The surviving bar pieces only split the kept
contact graph. A dangling endpoint from a cut seam cannot close a
cycle. Thus a real forest exists with gain at least

```
H - B - ν(all contacts) - ν(weight-two contacts),
```

where `ν` is edges minus graphic rank. This is Kruskal's rule with
weights one and two. No new mark is placed outside the windows.
The same construction works for several tangential bars at spacing
three in a window: their forced stars are disjoint, and the end,
normal-leaf and backing contacts are priced jointly.

## Pricing an unknown core from the discarded collar

The exterior in the preceding calculation is the untouched part of
the **smaller square**. The *discarded collar of the original square*
has different information: it says which exterior wirings are
impossible. Here is a general way to use that information.

Index the active interface edges by distinct ports. Let `π` be the
partition of their inside ends through the old windows and discarded
collar; let `η` be the partition of their outside ends through the
untouched crop exterior. A new crossing not supported by an old edge
gets a private old label. Old supported edges are actual, distinct
edges of the original forest. Thus gluing `π` to `η` is acyclic.
Let `τ` group the ports by proposed bar. Define `μ` to be the number
of independent merges of old labels demanded by `τ`. Then for
**every compatible `η`**,

```
ν(glue(τ,η)) ≤ μ = |π| - |π∨τ|.
```

Proof: over the field with two elements let `I(p)` be the span of
the differences of port vectors within each class of partition `p`.
It has dimension `#ports-|p|`. The nullity of the bipartite gluing
is `dim(I(τ) ∩ I(η))`, by the component count. Old acyclicity means
`I(π) ∩ I(η)=0`, so that intersection injects into
`(I(π)+I(τ))/I(π)`. The latter dimension is `μ`.

Apply this once to all contacts and once just to expensive ends:
`G ≥ H-B-μ_all-μ_ends`. Unknown active ports can be **overincluded**
in the merge count; adding a label to a bar cannot undo merges.
For arbitrary old words the checker takes the actual induced graph
of the collar plus the two editable rows, tests both seam words, and
includes a backing contact wherever neither neighboring row-one bit
forbids a backing mark by diagonal exclusion. A lateral leaf crossing
and a backing crossing cannot both be forced by exterior marks at one
end leaf: those two marks would be diagonal. None of these tests
needs the row-two word.

At the partition-only level the two nullity bounds can be tight
simultaneously. Join old labels greedily by pairs of expensive ports
in the same new group, then extend by all such pairs, always joining
different old components. Use the selected pairings to generate the
exterior partition. They stay independent over the old wiring and
all become redundant within new groups. This sharpness concerns the
contact debt, not optimality among all possible physical rewrites.

## Why this pays for the locked fringe

A **double post** is a rim mark with a marked inward neighbor at the
same tangential position. A window with `b` such posts at pitch three
and one blank column at each end has length `3b`. Diagonal exclusion
makes its two old words exactly the `2b` post marks. A backing tooth
can occur only under a post. Every post has a forced path to the
site immediately *outside* the crop, whether or not that outside site
was marked. Label posts by the components of these launch sites in
the discarded collar. A supported seam attaches through the first or
last post. Lateral leaf contacts use those labels too. Thus the
nominal gain is `b`, and labels for all possible contacts are known
before reading the backing.

For the six-layer cut the four label lists, up to renaming, are

```
00000001    00000002    00000003    00044445
```

All four seams pairs have marked exterior endpoints. There are
**five**, not 32, independent old-label merges. Just **four** of
those merges are needed by ends alone. Hence `G≥32-5-4=23`.
A different physical completion of the same local data tests both
prices: each seam pair returns via a deeper bar and one additional
tooth returns there too. The implemented exchange rejected four
expensive seams and one normal contact, gaining exactly 23.

This is an all-length reduction. In the fixed locked-fringe pattern
at `n=3k+1≥103`, enlarging the side only lengthens straight portions
of the old collar paths between the corner gaps and the windows.
This subdivides path edges and adds leaves without changing any
launch label. The removed count is `8n-18`; the comb increment over
side `n-12` is `8n-36+e`, `e∈{1,2}`. Subtracting 23 **beats the
comb increment by `5+e` marks**. A first counterexample cannot be
sustained by this outer pattern. If applying the known numeric
upper rather than induction, the remaining smaller-square upper gap
must still be compared with that saving.

### What the actual deeper holes buy

After the two-row repair on the test forest, 32 isolated holes remain
at crop depth three. For each one the two tangential edges already
exist. At depth two its neighbor is now an isolate: depth one is
blank and the adjacent depth-two sites are blank. At depth four its
blank neighbor is either isolated or attached to a sole donor at
depth five. This argument requires the local blank guards, not a
periodic deep core. For `q` holes and `J` such donors, insert all the
free holes and then accept the independent inward joins, of rank
`ρ`. The additional gain is `q-J+ρ`. In the replay `q=32`, `J=0`.
The repaired 91-square completed to an 8,280-edge tree with **2846**
full sites, versus 2782 original designated sites.

The same estimate scales with the number of locks. Keep the three
outer teeth per side and use any central odd train of `s≥7` inner
teeth fitting clear of the corners. Per side this adds `3-8+4+s=s-1`
marks to the six removed layers relative to two unmodified paths.
Hence `R=8n-46+4s`. Each crop window has `s+1` double posts and
`s+1` inward holes. With no backing contacts in the first exchange
and clean lateral guards its joint seam cost is at most eight
(at most one rejected seam per bar). Thus the saving against the
comb increment is **at least `10+e+4s-J+ρ`**. In particular an
extensive train can pay the unrestricted smaller-square linear gap
if enough of its inward contacts are independent or absent. The
side-193 replay used `s=25`, gained 104 twice, and beat the comb
upper by 117 on that measured class.

The dependency term is necessary. Four backed double posts returning
to a single tree gave *three* rejected contacts and only one extra
mark from the straightening. There is no deduction here that arbitrary
residue-one maximizers contain the priced windows.

## Verification

```
python3 -B -m analysis.research_program.blocked_rim_exchange
python3 -B -m analysis.research_program.collar_port_rank
(cd lean && lake env lean GridGraphs/Geometry/BlockedRimExchange.lean)
```

The port checker exhausts all 203 old partitions of a six-port test
and all compatible exterior partitions (11,735 comparisons), and
cross-checks arbitrary old two-row words against physical refills.
Lean checks the subspace dimension inequality and crop arithmetic;
the forest surgeries are proved above and replayed in Python.
