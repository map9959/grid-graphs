# Net cost of an arbitrary six-layer collar

For `n=3k+1≥103`, the **ten outer layers contain at most `16n-170`
marks**, with no restriction on the collar or core. This gives a
pattern-free crop comparison. It does not close the unrestricted gap;
there is a physical obstruction even to optimal four-layer repair.

## Transfer inequality

Remove six layers to obtain side `m=n-12`. Write `R` for the removed
count, `T` for the old ten-layer count, `I` for the unchanged count
inside those ten layers. If `B` marks can be placed in the first four
crop layers against this same interior, a physical gain `G` satisfies
`R-G≤min(R,T-B)`. The new content is to bound *both* terms of `T-B`:

* `A` is the lesser of `16n-170` and four independent corner maxima
  with only the supplied first six layers prescribed. Thus `T≤A`,
  regardless of how the unknown deeper words or components join.
* Take the [attained four-layer pattern](COLLAR_PEEL.md) with `8m-40`
  marks. Let `z` be the cost of clipping its redundant edges, below.
  Then `B≥8m-40-z`. Neither `A` nor `z` needs an optimal repair oracle.

Consequently, with `d=16n-170-A`,

```
R-G ≤ 8n-34-d+z.
```

The measured `T` can replace `A`; other physical refills can raise `B`.
The combined upper is `min(U(m)+R, A+min(P(n-20), U(m)-B))`: `n-20`
is in the solved residue-two family. At 103, `U(91)=2858`; `d-z≥2`
suffices. Any 3647 witness must have **both** `T≥789+B` for every
realized refill and `T≥1274` because `P(83)=2373`.

## The unrestricted ten-layer cap

Divide the annulus at side midpoints into four L-shaped pieces, each
a `10×10` corner and two arms. Ignore edges crossing the cuts for an
upper. The full straight length of a side is `L=n-20`.

1. A width-ten transfer retains ten mark bits and the connectivity
   partition of the ten frontier vertices. Try every next mask and
   reject a redundant forced edge. From length 13 to 14 the **entire**
   vector of maximum scores repeats plus four (24,263 states counting
   the initial state). A free arm can therefore be lengthened at a
   cost of exactly four per column against any fixed remainder.
2. With both arms of length 13 the corner maximum is 143, hence
   `4(h+v)+39` for any `h,v≥13`. With one arm absent it is
   `4(h+v)+42` (base 94 in either orientation). The corner verifier
   traverses one arm, the diagonals of the corner, then the other arm.
   It retains the marked bits and partition of all live vertices and
   includes the blank reentrant corner site. Four pieces give `16n-164`.
3. Forbid the transverse mask marked precisely at depths `0,3,6,9`.
   The width-ten vector then repeats from length 47 to 57 with increment
   38. Checking ten remainders gives a cap of `4L-14` for all `L≥83`.
   If a whole straight arm lacks the mask, detach it; the two adjacent
   one-armed corner bounds cost six, the arm saves fourteen. This gives
   **`16n-172`**.
4. Otherwise duplicate one pitch slice in the straight part of each
   side. The neighbor's marked bits are a subset of the pitch mask
   by diagonal exclusion. The four crossing edges are subdivided, and
   the new normal edges are leaves. Repeating extends the annulus to
   any side `s=n+t` with `T+16t` marks, keeping its corner interfaces.
   Pump the annulus alone; the original interior need not repeat.
   Choose `s=3q+2` with `q=12 mod 14` sufficiently large. Insert a
   physically optimal square of side `s-24` starting at depth 12.
   The two blank layers separate forced supports. The
   [exact residue-two scores](RESIDUE_TWO_CLASSIFICATION.md) give
   `P(s)-P(s-24)=16s-170`: neither endpoint is exceptional and the
   two seventh-floor terms differ by two. Thus `T≤16n-170`.

For the conditioned bound simply run the four free-end corner sweeps
with the observed outer six bits at each position, leaving every
other mark free.

## Certifying recovery

Erase the first four crop layers and contract the forced forest of
the unchanged core. Each remaining edge forced by a proposed template
has one or two template owners. Keep a spanning forest, considering
two-owner edges first. For every rejected edge withdraw all its
owners. The remaining stars are a subforest. For `β` rejected edges
of which `β₂` have two owners, `z≤β+β₂`; the implementation charges
only distinct withdrawn marks.

A second refill splits the adjustable band into elbows, leaving one
blank terminal slice at each end of each arm. Optimize each word with
all backing vertices wired to one root. A port edge is required if
either endpoint is marked, even behind a blank terminal slice.
Adjacent elbows have two blank slices separating their marked
supports. Each result stays acyclic under the stronger common wiring,
so the four can be used together in the real crop. This price only
uses the backing bits; the checker also completes the result to a
physical spanning tree.

For example, for the locked fringe at 103, `A=1447`. All **688**
four-layer template marks fit (`β=β₂=0`), giving upper **3617**
from the six-layer-conditioned count or **3598** with `T=1428`.

## Why the universal test is insufficient

The mixed test uses width-eight elbows on the left and width-ten
elbows on the right. At 103, backtracking produces corner scores
`341,299,303,344`. Start with two blank slices between neighboring
elbows, fill additional independent stars, use a partial backing bar
at depth ten on the left and insert the side-77 construction at depth
13. Complete the tree, then use **all** its full-degree sites.

This tree has 3535 full sites and 10,608 edges; `T=1298`. For an upper
on **every** four-layer refill, split the smaller perimeter into four
width-five elbows, retain the observed fifth layer, optimize all
other bits and subtract the fifth-layer count. Even ignoring cuts
and deeper constraints the editable layers can contain at most **502**
marks. Thus `R-G≥1298-502=796`, compared to a comb increment of 789
and an exclusion threshold of 788. Also `T+P(83)=3671`, so the
second solved-core comparison does not remove this obstruction.

This effect can be linear in side length. Place the vertical split at
`2n/3+O(1)` and the horizontal split near the middle. The total low
side length is `l=(7/3)n+O(1)`; the high length is `h=4n-l+O(1)`.
Free width-eight vectors repeat with increment 22 per seven columns;
width ten has increment four per column. Therefore the original band
can have at least `(22/7)l+4h-O(1)` marks, using the straight arms
and leaving fixed-size corner patches empty if needed. Put a
continuous depth-ten backing bar along each long low segment; depths
eight and nine are blank there. In the crop its adjacent row must
stay blank along the straight part. Every mark in the next row
attaches to that same backing component. The remaining width-three
strip with these wired spokes has cap `l+O(1)` (vector shift three
from lengths 7 to 10). The high segments have the free width-four cap
`2h+O(1)`. Even an optimal four-layer restoration thus has net loss
at least `(15/7)l+2h-O(1)=8n+l/7-O(1)`. Also the original ten-layer
count can reach `14n-O(1)`, above
`comb(n)-P(n-20)=(2831/210)n+O(1)`. These are obstructions to the
comparisons, not trees exceeding the comb.

Depth matters. A six-layer refill on the mixed tree attained effective
loss **764**, giving upper **3622**. The same six-layer rule costs
**817** on the ordinary comb diagnostic; it is not a universal
exclusion either. The score-3647 question remains open.

```
rustc -O analysis/research_program/collar_strip_gap.rs -o target/collar_strip_gap
rustc -O analysis/research_program/collar_bend.rs -o target/collar_bend
target/collar_strip_gap 10
target/collar_strip_gap 10 ban
target/collar_strip_gap 8
target/collar_strip_gap 3 wired
target/collar_bend bases
python3 -B -m analysis.research_program.arbitrary_collar_transfer
(cd lean && lake env lean GridGraphs/Geometry/ArbitraryCollarTransfer.lean)
```
