# An unrestricted frame around Q_k has insufficient growth

**Computational lemma with uniform reduction.** For k>=4, embed Q_k from
`PAPER_NESTED_RENEWAL_OBSTRUCTION.md` in the center of side `3k+8`.
In any feasible forest preserving the prescribed F and U labels on this
whole crop, at most **13k+31** centers are in the surrounding three-layer
frame. In particular no coordinated rewrite to Q_k followed by any choice
of this frame attains the requested `14k+25` for k>=7. The deficit is
linear, even if the boundary rewrite and frame are not periodic. This
does not bound completions of a different core.

### Contracted crop ports

Use local crop side `n=3k+2`. Call the top rod at column `3j+1` A_j,
and the bottom rod at column `3i+3` B_i (indices as in the nested-renewal
note, including i=-1). Use names P_j for the component of A_j. For
1<=j<=k the singleton at `(3j-1,3j-1)` connects A_j to B_{j-2}:
it reaches the A_j center two columns to its right via the intervening U
vertex, and the B_{j-2} center two columns to its left the same way.
All these edges have at least one F endpoint. The bottom contacts are thus
not independent of the top. Only proved identifications are needed for
the upper bound: splitting a root, if anything, relaxes acyclicity.

Take paired top and bottom strips of width three above/below the first
`3(k-1)` crop columns. On each triple `c=3j+i`, 0<=j<=k-2, the top
ports belong to P_j (the rod and its two neighbors). Bottom ports belong
in order to `P_{j+1},P_{j+1},P_{j+2}`. The first two touch the bottom rod
at `3j`, the last touches the rod at `3j+3`. The top port itself is F
only for i=1; the bottom port only for i=0. These statements include
the leftmost triple. Even when a port is U, a frame center next to it
**forces** the contact edge.

For the straight left strip take crop rows 2..n-1 and for the right
strip 0..n-3. Every such port **is F** on the same rod for that side.
Both strips have length 3k. Treat them separately, dropping joins to
the other regions. Contraction of a forest, omission of edges and
splitting of roots preserve the necessary condition of acyclicity;
parallel edges must still count as a cycle. Centers in the regions are
disjoint, so their separate score upper bounds may be added.

### Finite state certificate

Keep the previous frame column mask and partition of its three or six
vertices together with the live crop roots. Introduce each next column's
mask; add within-column and between-column edges exactly when at least
one endpoint is F. Apply the port rule above and reject a repeated union.
After processing i=2 shift the live roots `(P_j,P_{j+1},P_{j+2})` to
`(P_{j+1},P_{j+2},fresh)`, retaining all inherited connections.
Forget vertices only after their last incidence. Start with distinct
roots, no selected previous sites and free ends (dummy pendant contacts
do not constrain the answer). Maximize the sum of mask sizes. The local
rules repeat every three columns. For each reachable terminal state
store its maximum score, not just a global maximum.

`analysis/research_program/crop_frame_rate.py` computes these vectors in
two ways: union-find with live-root shifts, and explicit multigraph DFS
checking `E=V-components` and then projecting the partition. All vectors
agree. For the pair the 9- and 12-column vectors have **exactly the same
471 entries, each score increasing by 7**; for a side all 8 entries
increase by 3. The three-column update commutes with adding a constant
to the entire score vector. Induction therefore gives the paired
maximum `7m+2` and single-side maximum `3m` for all lengths `3m`, m>=3.
This is an induction on exact vectors, not a fit to successive maxima.

### Caps and final bound

The uncounted frame consists of four 3x3 corners, a five-column tail
on each of top and bottom, and two-row tails on left and right. This
partitions all `12n+36` frame sites without overlaps. Ignoring exterior
joins, a 3x3 rectangle carries at most 4 centers. On the five-column
top tail the port grouping is `[a,a,a,b,b]`, with F at offsets 1 and 4.
On the bottom it is `[a,a,b,c,a]`, with F at offset 0; for example
the final U port is adjacent to the lower end of the rightmost A rod.
The two-row left tail has two U ports (allowed distinct); the right
tail has two ports on the same rod, the first F. The cap routine
exhausts the little partitions independently by explicit set unions.
The maxima used are respectively 4 per corner, 7 per top/bottom tail
and 3 per left/right tail. The same maxima are checked again with every
crop contact deleted, so the cap estimate does not depend on the tail
port classification. Therefore

    frame <= [7(k-1)+2] + 2*(3k) + 4*4 + 2*7 + 2*3
           = 13k+31.

Since `|Q_k|=3k²+5k+1`, the whole score is at most
`T(k+2)-(k-6)`. This excludes an eventual constant-gap lower family in
this specific frozen-core class; it is not merely a failure at one seed.
The old-to-Q rewrite itself is not a feasibility obstacle: remove old
centers outside Q first, then add missing Q centers, always passing
through subsets of a forest. The bottleneck is what can be attached
after that rewrite. In particular k=7 and k=8 would need 123 and 137
new centers respectively; this certificate allows at most 122 and 135.

Replay (small periodic interfaces only, no large-square optimization):

    python3 -B -m analysis.research_program.crop_frame_rate

The replay additionally verifies acyclicity and the claimed physical port
identifications on both historical Q_2 and Q_4. The asymptotic result
uses the rod formulas and the vector induction rather than those two
examples. This is not a Lean theorem.
