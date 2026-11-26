# Crossed rail sectors, with independently oriented interfaces

This test replaces parallel interfaces by four sectors meeting in an X.
Top, right, bottom and left sectors each have their own saturated background
and pay only for the corresponding physical side. The four joins run on
half diagonals; two have slope +1 and two slope -1. A bounded center and
four bounded corner neighborhoods do not affect the growth rate. A target
family of primal tangential period p must therefore obey

    2*(top arm + right arm + bottom arm + left arm) + sum(four join losses) <= 2p.

Here a side increase of 2p adds two arm periods per side and one period
to each interface. As before, loss counts incoming arrows into unpreserved
sites and boundary deficiency. This test is necessary even for a bounded-gap
family: an excess in this loss is incurred again at each enlargement.

The slope-minus interfaces are reflected by `(r,c) -> (r,last-c)` in
doubled coordinates, keeping the actual far-side phase `last=8+6*t`
for a base-five square. In increasing reflected normal order the joins
are top-to-right and left-to-bottom; the unreflected joins are top-to-left
and right-to-bottom. Costs are directed. Fitting each join independently
can only underestimate the cost of assembling an actual X and its center.

## Period three

At centered split (4,4), each side admits 18 of the 24 backgrounds.
All 18^4 assignments were tested. A six-site doubled cylinder Dijkstra
search takes all physical occupancy sectors, not just the balanced one.
It exhausts states up to cost 6, with no normal-width cutoff. More
expensive or unreachable joins are provisionally priced at 7, which is a
lower bound. The minimum of these lower bounds over sector assignments
is 12 against the allowance 6. Thus even a best assignment falls at
least two centers short **per side-six growth**. The same test also
excludes splits (1,1), (2,5), (4,5), (5,5), (6,6).

## Period nine

Necessary conditions include matching site counts across the normal
cut, rail-end costs, and signed cut currents. For the latter let ff and
u denote signed forward currents on arrows F->F and all arrows into U,
respectively. If L and H are the rail labels (axis, transverse residue)
at the two ends, there are at least `|L symmetric-difference H|`
terminal units. In a finite strip, counting F->F incidences gives

    2 * #F->U from inside = terminal units + ff_low - ff_high.

Counting all arrows into U then gives the lower bound
`max(0,ceil((|L xor H|+ff_low-ff_high)/2)+u_low-u_high)` on interior
loss; U->U arrows out of the strip's vertices were discarded. This sign
and rounding convention was cross-checked against 1,152 directed
period-three transfer queries (two diagonal directions).

At period nine the flux relaxation gives a minimum of 12, below the
allowance 18, on each of the three residue classes. The same minimizing
example (top,right,bottom,left)=(0,129,254,127) has **zero** arm cost on
every side and a flux lower bound of 3 per join. The widened Rust
cylinder query `--sector` allows nonbalanced sectors and tests costs up
to 4 with forward radius 1 and reverse radius 2, joined across the
median-cost slice. All four required joins cost **at least 5**, so this
promising relaxed candidate costs at least 20 and fails. The returned
value above the threshold is not necessarily the exact minimum.

    cargo build --offline --release --bin diagonal_nine
    python3 -B -m analysis.research_program.crossed_rails
    python3 -B -c 'from analysis.research_program.crossed_rails import rotational; rotational(0)'

The optional quarter-turn test rotates the backgrounds about the actual
square center (not about lattice origin). While the physical arm widths
can differ, their four costs are included separately. The four cylinder
joins are then isometric, so each can cost at most floor((18-2*arm_sum)/4).
Of the 384 top layouts, 64 survive this and the normal occupation test.
There are 24 simultaneous-translation orbits of ordered join layouts;
the same orbit keys and thresholds occur in each of the three residue
classes. This symmetry argument concerns the backgrounds; it does not
impose rotational symmetry on a center tiling.

Completed transfer: **0 of 24 orbits survive**. Thus none of the 64
quarter-turn background tuples reaches the necessary gain, on any of
the three residue subsequences. Each tested directed seam has minimum
cost at least five; this information also applies when that seam occurs
in a nonsymmetric tuple. `python3 -B -m analysis.research_program.crossed_orbits`
propagates those 24 bounds through simultaneous translations and the
opposite diagonal reflection. This tightens 3,312 directed matrix
entries on each residue. The unrestricted crossed-background relaxation
still permits 781,910 assignments per residue, 186,834 at relaxed cost
12; none is a verified square construction.

## Shared-budget test of all remaining asymmetric assignments

The 781,910 candidates per residue have now been excluded. Collect every
directed entry used by any candidate with
`2*sum(arms)+sum(four directed joins)<=18`. There are 5,932 entries
before canonicalizing by simultaneous translation and diagonal reflection.
Keep existing lower bounds exceeding 4. The remaining entries require
only 552 directed orbit queries. The forward and reversed distance tables
can each be translated onto a representative rail layout independently:
if `low'` samples low at `(r+2a,c+2b)` and `high'` samples high at
`(r+2u,c+2v)`, use a lookup shift of `2*(b-v)` columns and
`a-b-u+v` normal phases from the low table to the high table. This is
only a change of coordinates at lookup, not a relaxation of the seam.

The exact threshold-four cylinder test returned 12 minima at zero,
none at one, 8 at two, 16 at three, 48 at four, and 468 strictly above
four. Replace entries by their exact minimum if <=4 and by at least 5
otherwise. **No assignment meets 18**, independently on each of the three
residue subsequences, without imposing compatibility at the center or
corners. No query was missing after reflecting with the actual far-edge
phase for each subsequence. As checks, threshold three alone left 265,822
assignments; its distance histogram agreed with and without independent
table translations. Another 22 direct/translated queries agreed across
all seven occupancy counts, including a nonidentical join of cost two.

    cargo build --offline --release --bin diagonal_nine
    python3 -B -m analysis.research_program.asymmetric_seams 0 4

This is a growth obstruction for the **centered base-five, period-nine,
four-sector X** with saturated backgrounds, not for all feasible trees.
