# Period (9,9) test: no centered target transition

**Scope.** Base-five split (4,4), one diagonal interface of arbitrary fixed
normal width, two saturated rail backgrounds, 18-periodic doubled domino
matching along the interface, and independently optimized boundary arms
of doubled depths 4 and 5. Corner neighborhoods renew with period three
in k. This does not classify arbitrary spanning trees.

## Arm cost from the vertex ledger

For the rooted square use `3 f = n²+4n-1-h-D-rho`, with `h` the missing
grid incidences at unpreserved boundary vertices, `D` the number of arrows
entering unpreserved vertices, and `rho` the preserved-root indicator.
The target is `(n²+3n-10)/3`. Increasing n by nine therefore allows only
**nine** more units of `h+D+rho`, while requiring `18k+48` more centers.
Corners and the root contribute a constant on each residue subsequence.
Each growing arm adds one longitudinal period; the interface adds one
period of D. The remaining uniform backgrounds have D=0.

The torus classification gives `2*3*2^6=384` layouts: two axes, three
phases, and three independent primal and three dual rail directions.
For a given layout at a physical side, read the outward domino ports
plus primal/dimer labels in a fixed collar. Enumerate column pieces in
the arm; adjoining pieces must match all ports. The local score of a
nonpreserved interior vertex of tree degree d is `d-1`, or `d` on the
physical side. A preserved vertex costs zero. Minimize this nonnegative
integer sum on a closed 18-column word. The state includes preceding
midpoint labels to score complete vertex stars. This is exact finite DP,
not a timeout-dependent optimizer. Assign the top and right arm to one
background, bottom and left to the other. Recompute the latter physical
boundary positions for each k mod 3. These are deliberately independent
minima, so omitting the end joins favors a construction.

Subtracting the four arm minima from nine leaves the following counts
on **each** of the three classes: 440 ordered pairs with budget zero,
216 with one, 48 with two, four with three. All other ordered pairs have
negative budget or a forbidden side profile. As a check, at longitudinal
period six this arm algorithm reproduces the previous centered budget
distribution exactly (72,32,4), without using its SAT arm calculation.

## Any-width test

All candidate starting and ending layouts have nine incoming sites in an
18-site normal slice. This number stays nine. Exhaust matching transitions
by sending each remaining site either straight or to the adjacent column
of the next slice, requiring distinct destinations. Two doubled steps
close a primal slice. Its D cost counts 1 for each degree-two site and 2
for each degree-three site. Each primal site sends one arrow, so degree
zero cannot occur. The state carries occupancy, previous midpoint labels,
and normal phase mod nine. Start and finish at phase zero, padding any
interface into its prescribed backgrounds with free homogeneous slices.

Meet the forward and reversed half-cylinders on a primal slice. Reversal
sends column c to -c, complements occupancy, and exchanges the preceding
and following midpoint labels. Disjoint complementary occupancies suffice
for joining the matchings; count the middle slice cost using both midpoint
masks. For budget b<=3 a feasible path has a median cost unit in some
slice (choose any slice when b=0). On either side of it there are at most
floor(b/2) paid units. Thus searches of radius at most one in **loss**, not
in length, suffice. Radius-one closures exhaust zero-cost loops too.

No background pair reached its target on any residue. Controls: 120
balanced identical-background joins of cost zero; directed nonidentical
joins from layouts 50,56,84,88,98,100 into 112 of cost two. Layout IDs
are the deterministic generator order. The 384 matchings were checked
for reciprocal partners and 27 preserved sites per 9-square torus.

    cargo build --release --offline --bin diagonal_nine
    cargo test --offline --bin diagonal_nine
    python3 -B -m analysis.research_program.period_nine
