# Using the solved residues to price the retained core

For `n=3k+1≥103`, let `m=n-20=3p+2`. Write `T` for the old
ten-layer count and `I` for the count in the remaining `m`-square.
The [arbitrary-collar comparison](ARBITRARY_SIX_COLLAR.md) gave
`T≤16n-170`, but its four-layer repair could fail even if optimal.
Here are bounds on **the other term**, `I`. The window of allowed
scores for a given collar is not determined by `P(m,m)` alone.

## An all-length consequence with no assumption on the deeper core

Along each side omit the two `10×10` corners, leaving `m` tangential
positions. Partition these arbitrarily into low and high intervals
(`qL,qH` nonempty pieces in total over all sides). Let `S` be total
low length, `J` the total number of selected sites at depths **8 and
9** on those intervals. High intervals have no word constraints. For
every feasible score `M=T+I`,

```
(3+1/m) M ≤ n²+4n+23 +20 qH +102 qL/7 -4S/7 +3J +(16n-170)/m.
```

In particular if the number of pieces is `o(n)` and
`4S/7-3J ≥ (11/30+ε)n` for some fixed `ε>0`, this beats the comb
for all sufficiently large sides. If the two layers are completely
clear on the low intervals, a fraction strictly above `77/480`
of the total straight side length suffices (bounded away from that
threshold). Neither the low intervals' other eight rows nor the
high intervals have to repeat.

This is stronger for a long *partial* stretch than subtracting the
two solved-square scores alone: the mixed construction can have
`T=14n-O(1)`, more than `comb(n)-P(n-20)=(2831/210)n+O(1)`.
The extra debit comes from the fact that old collar connections rule
out identifications of the *same* ports inside the retained square.

**Proof.** In the core let `r,c` count straight marked runs and
forced components, isolates included, and `D` the marked boundary
degree deficiency (one per open-side mark, two per marked corner).
The exact edge ledger gives `3I=m²+D-r-c`. In a high piece of
length `L` let `z` be its marks, `A` the count on its inward edge,
`D_i` the core marks facing it, `O` the number of positions with
both bits set, and `c*` the number of piece components reaching
these `A+D_i-O` forced crossings. Contract the disjoint high-piece
forests and the core. The bipartite multigraph of crossings is a
forest; consequently `c ≥ 1+Σ(A+D_i-O-c*)`. This is joint across
pieces, even when different sides touch the same core component.

The piece ledger is `3z=10L+outer+A+ends-r_i-c_i`, where `ends`
counts the two short-face words. Every doubly occupied crossing
costs a **distinct** run inside the piece: both tangential neighbors
of the inward mark are prohibited by the facing mark's diagonals.
Thus `O≤r_i` and `c*≤c_i`. It follows that
`3z+D_i-(A+D_i-O-c*)≤11L+20`. On a low piece, the width-eight
free transfer gives `7 z₈≤22L+34`; hence `3z+D_i≤73L/7+3J_i+102/7`.
The transfer checks the additive remainder over the full transient
and one period, not just the asymptotic rate. Each remaining corner
contains at most 42 marks by the exact corner sweep with two zero
arms. Summing, using `4m` total length, and then `r≥I/m≥(M-16n+170)/m`,
gives the displayed inequality. The code optimizes high/low
assignment by a two-state path recurrence.

For example take one full low side, one high, and on each other
side a single low part of length `floor(2n/3)-10` and a high
remainder. For `J=0`, `S=(7n-124)/3`. This gives
`M ≤ n²/3+7n/9+54` for `n≥181`, strictly below the comb whose
linear coefficient in `n` is `11/10`. The integer comparison also
pays at 172, 175 and 178. Thus the comb upper holds in this mixed
class **for every `n=3k+1≥172`**. For `O(1)` deviations at the
transitions use the general inequality, with the same slope.

## Exact use of the core's boundary connectivity

The same comparison applies **directly** to a residue-one square.
For `n=3k+1` use the exact prices `E` of the best adjacent row/column
and `F` of the full outside ring calculated below. Every feasible
input then has score at most `min(P(3k+2)-E,P(3k+3)-F)`. Subtracting
the comb shows that either of the following gains suffices:

```
E ≥ 2k - floor((k-5)/7) - floor((3k-13)/10) - exceptional(3k+2)
F ≥ 4k + 4 - floor((3k-13)/10).
```

At 103 these are 56 and 132. The actual comb's best L and ring gains
are just three and five, respectively. Thus transferring *outward*
alone is not the missing unrestricted bound; the exposed ports after
cropping can have quite different prices.

Let `η` partition the perimeter vertices by their actual forced
components *inside the core*. To grow `m` to `m+1`, add an L along
two adjacent sides. To grow it to `m+2`, add its full perimeter
ring. On the new path/cycle each site meets at most one old vertex.
A tangential edge is forced if either endpoint is marked; a port edge
into `η` is forced if the new site **or its old backer** is marked.
Two occurrences of an old corner use the same label. Include even
isolated old ports. This small graph decides exactly which fillings
are feasible, with the entire original core kept.

Labels of disjoint trees cannot alternate around the perimeter
(two paths joining alternating terminals must intersect). Consequently
between successive occurrences of a label there are only complete
nested blocks. In a block store the initial and final bits and the
partition of three terminals: the common label, first site, last
site. Compose neighboring summaries by identifying the common root
and inserting the actual seam edge; a redundant seam rejects the
choice. Forget a completed label, keeping its two endpoint relations.
Close the final seam for the ring. The explicit stack processes any
nesting depth, with a bounded number of partition operations per
site. Backtracking the maximizing bits gives physical trees, not
just compatible port scores.

If `L*` is the best of the four L gains and `B*` the optimal ring
gain, then

```
I ≤ min(P(m), P(m+1)-L*, U(m+2)-B*).
```

The first two terms use the **exact** residue-two and residue-zero
formulas for arbitrary size. A further option: apply the ring solver
from the inner `(m-2)`-square to `m`, releasing the current rim. Its
improvement is a certified deficit below `P(m)`. This last test reads
one layer farther in.

The component ledger is another independent bound. `c≥|η|` and
`r≥ceil(I/m)`. Boundary marks require carriers in their respective
classes. Also an unmarked boundary vertex that shares its class
with another boundary vertex and has no marked rim neighbor needs a
marked inward donor. For all such required sites cut their row and
column lines at known vacancies, diagonally forbidden sites, and
incompatible labels. Each real carrier covers requirements in one
remaining horizontal or vertical segment. A matching in the bipartite
segment incidence graph lower bounds `r`. An interior forced isolate
surrounded by four forced vacancies counts in addition to `|η|`.
All these bounds use only the boundary word and its partition.

There is also a certificate without reading `η`. On the same ports
compute `π` using the old collar and all crossing edges but **no**
core edges. Gluing `η` to `π` is acyclic. Thus on any nonempty set
of ports `Z` the number of distinct `η` classes is at least
`|Z|-|π restricted to Z|+1`. Use all ports for `c` and the marked
ones for `r`. For extensions, first treat old port vertices as
separate, then require that the new outside graph connect only vertices
with the same `π` label. Its induced partition refines `π`, so the
refill works against *every* compatible interior. The solver carries
the `π`-color of each live component and rejects a conflicting union.

## A charge for physically broken rails

Take `b` aligned pairs of opposite marked teeth, isolated tangentially
in both end words, at columns spaced at least three, with all `2b`
core labels distinct. Their boundary-rooted carriers are straight
vertical segments (possibly singleton). For each tooth take the first
vacant site just inward of the end of its carrier, then step right
one column. The resulting `2b` witnesses are distinct interior sites:
opposite tips must be at least three apart or they are connected.
Keep the teeth away from the rightmost two columns.

Every witness is vacant by diagonal exclusion. If it is not an
isolate, its supporting mark is either two columns right of the
tip and one row inward, or one column right and two rows inward.
The other two neighbors are blank (at a singleton tip use the old
boundary word). No distinguished vertical carrier can support it.
A vertical helper can support at most two witnesses, one per end
at its unique nearby column. A horizontal helper must either use its
left endpoint, or in the second case reach the tip column and thereby
join the tip's component. Its left endpoint can serve at most two
witnesses and it can join only one of the distinct tip components.
Thus `2b≤3 extra_runs + extra_components`. Additional normal carriers
in distinct classes outside the witness columns need not be charged
as helpers.

In particular on a width `m=3p+2` pure pitch core, suppose the sides
are blank singleton ports, the end words have `p` pitch teeth covering
the other sites, and the pitch triples have distinct classes except
for `p-b` corresponding through pairs. Then `c_boundary=2m+p+b`,
and `p+b` distinguished carriers cannot serve as helpers. The ledger
gives `I≤pm-ceil(8b/9)`. This is a length-dependent charge per break;
there is no assumption that the interior resembles rails.

## Checks and limits

At 103 the old mixed tree's ten-layer count is 1298 and its minimum
four-layer net crop cost is at least 796 (threshold 788). Adding an
L to its side-83 core gains **110**, so `I≤2434-110=2324`.
The boundary ledger gives **2306** instead of 2373, hence parent
upper **3604**. Even without the inside labels the collar projection
gives 3605. Releasing the core rim gained 133 and produced an
83-tree with 2370 full sites and 6888 edges: core upper 2240 and
parent upper 3538. On the ordinary 103 comb the boundary ledger is
tight at **2241**, giving exactly 3646.

These are general inequalities and conditional exclusions. No result
here proves that *every* superior residue-one tree has sufficient
clear side length, sufficiently many distinct ports, or sufficiently
many broken rails.

```
python3 -B -m analysis.research_program.core_boundary_envelope
python3 -B -m analysis.research_program.core_envelope_check
python3 -B -m analysis.research_program.core_interface_length
python3 -B -m analysis.research_program.split_rail_boundary
target/collar_bend elbow 10 0 0
target/collar_strip_gap 8
(cd lean && lake env lean GridGraphs/Geometry/CoreBoundaryEnvelope.lean)
```
