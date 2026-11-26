# Fully free three-column crop repairs

Use the moving-core net frame account. In each interior triple `j`, write
`r=row-3j, c=column-3j`. All **three** columns c=0,1,2 on the entire
inclusive interval `lo..hi` may be relabeled. There is no immutable center
or separator column between consecutive pockets. The unchanged top rod
(column 1) ends at lo-1 and the unchanged bottom rod (column 0) begins
at hi+1. The old core had `1-lo` top centers, `hi-1` bottom centers and
one satellite in the pocket: debit `hi-lo+1` per triple. Each top and
bottom frame strip has three independent free lanes. On the period-two
test the second pocket and both frame masks may differ from the first.

## Transfer across repeats

Retain a quotient of all forced primal edges modulo translation by the
whole repeat, labeling edges by the signed displacement of their endpoints
in repeat units. Within the core this translation increases row and
column together; on each straight frame strip it increases column only.
Contract each immutable rod's connected star support, including its U
neighbors. These supports are disjoint in this model. An interior center
in the right column can contact a rod in the **next** translated copy.
An ordinary nonrod vertex shared by two pockets has the same physical
identity in both. Enumerate unique edges before contracting so that
distinct edges which become parallel are not dropped. A variable edge is
present exactly when either incident endpoint is selected; a port touching
a fixed center is forced even if the frame endpoint is U.

A quotient component can lift to a forest precisely when it is a tree or
is unicyclic with nonzero winding. Indeed, one zero-winding cycle lifts
to a finite cycle, and for a component of rank at least two the map from
its free fundamental group to the integer winding group cannot be
injective. Conversely cutting the single nonzero-winding edge leaves
trees linked in infinite paths. This accounts for actual connections
across translated copies rather than checking just one open pocket.

The solver requires every occupied edge to consume an outgoing slot
at one of its endpoints, with at most one slot per vertex. This is the
pseudoforest condition. It also rules out short zero-winding cycles
upfront; opposite selected corners of a physical unit square are forbidden
directly since their stars cover the face cycle. Reconstruct each model by vertex DFS with winding potentials;
if a longer zero-winding cycle remains, forbid its actual edge set and
solve again. Count all selected core and frame sites with an exact unary
cardinality recurrence. The target is `8*period+debit` total sites,
since the two exterior side strips can contribute at most `6k+O(1)`
and the total net frame needs `14k+25`. Forest feasibility here concerns
the repeated core plus the top and bottom frames. It is a necessary test
before attaching the side strips and corners, not a full square seed.

## Period-two result

For `lo=-3,hi=5`, 54 free core sites and 36 free frame sites per repeat
give 90 Boolean center choices. The graph after contracting has 96
vertices and 188 physical edge orbits. Solver UNSAT for 34 centers (net
16); SAT for 33 (net 15). The latter model has 17 core sites instead
of the original 18, plus 8 sites on each of the top and bottom strips.
A separate primal replay restored the actual long rods and unfolded
one, two and five copies: forest in every case, with net scores 15,30,75.
This does **not** verify a target seed since the rate already fails.
The solver UNSAT result is scoped and has no independently checked proof
trace. A three-block test on these same windows also returned UNSAT at
24 net. These results do not exclude larger unknown macroperiods.

A taller control (`lo=-6,hi=8`, 15 rows, original two-block debit 30)
also attained net 15 with open primal replays of 15,30,75. Its first
net-16 search hit its 200-second limit; that run is inconclusive.

## Arbitrarily tall pockets at period two: exact transfer

The 600-second SAT retry also timed out. A direct matching-free **primal**
transfer now settles the taller question independently. Run

    python3 -B -m analysis.research_program.sheared_pocket -6 8

Contract the two frame strips separately. Their input vertices are the
two physical rod roots per repeat. Enumerate all width-six masks which
do not already force a physical face cycle. Add their actual edges,
including all rod contacts and any edges crossing to the translated
copy. A component carries an integer relative offset per attached site
and either no winding or one winding period. A second independent cycle
in a component, or one of winding zero, invalidates the forest lift.
When its remaining contacts are projected, preserve connection offsets
modulo its winding. Each frame has six distinct valid two-root summaries:
one can score eight, two can score seven and three can score six. Keep the
highest score for each summary, not six independently scored roots.

Process the interior on slices `d=row-column`, columns modulo six.
From a slice to the next, an occupied edge goes from c to c or c-1
(with the correct translation at the wrap). There are no within-slice
edges. The frontier carries the connectivity just described and the
two preceding F masks. Opposite selected corners of a unit face are
forbidden, both within the current mask and across two slices. All
remaining choices undergo the full acyclicity test. Start with the
top-frame partition on the two A rods: in the last homogeneous top
slice the preceding A-star also connects sites 1 to 0 and 4 to 3.
At the far end the future B-stars connect 0 to 1 and 3 to 4 before
applying the bottom-frame summary. Fixed parts of the long rods not on
the cut consist only of the continued rods with pendant leaves.

At local-height interval [-6,8], the exact best is 45 selected sites
minus debit 30, or **15 net**, not 16. More importantly, between free
slices 2 and 3, all 3,548 frontier keys agree and every score increases
by exactly two. This identical free-slice operator distributes over
adding a constant to all scores. Thus inserting any number of full
free slices adds exactly two per slice, before the unchanged exit
updates. Each added local row also increases the original-center debit
by exactly two. The net stays 15 for **every larger fixed height**.
The entry/exit schedules use only `d-lo` and `d-hi`, respectively
(physical local row at c is `d+(c mod 3)`), so a vertical shift of
the free interval does not change this calculation when `lo<=0,hi>=2`.
Any smaller window can be embedded in a larger one by restoring the
original rod centers in the newly free rows. With the earlier witnessed
net-15 model this is a sharp asymptotic obstruction to *all fixed-height*
three-column pockets of period two under these fixed rod/side assumptions.
No global nonexistence or higher-period obstruction follows.

## Period three: the deficit persists at arbitrary fixed height

`src/bin/sheared_pocket.rs` extends the shear transfer to nine columns.
Each frame has 17 distinct weighted partitions of its three rod contacts.
The interior state is the two last masks plus the lifted connectivity
of all nine frontier vertices. Negative winding offsets and nonzero
cycle periods survive projection onto the new frontier. The Rust
period-two run duplicates the Python state counts, per-slice maxima
and first whole-vector shift on the 15-row control.

For the 27-row pocket `[-12,14]` at period three, 104 sites were selected
at optimum, with original-center debit 81. The exact net is **23**, not
24. There were 294,322 distinct frontier keys on the stable free slices.
The scores on all keys from slice 1 to slice 2 increased by exactly
three, not merely at the maximizing entry. Thus every extra fully free
slice increases the final maximum by three, exactly its extra debit.
The entry and exit schedules are otherwise unchanged. By the same
embedding argument as at period two, all smaller fixed windows have net
at most 23 too. This is an upper bound on the repeatable interior even
with each of the three pockets and each of the nine frame columns
independently chosen.

A separately synthesized nine-row SAT witness attains 23: 26 core sites
instead of 27, plus 12 top and 12 bottom frame sites. Direct *uncontracted*
forest replay over one, two and five copies verifies net scores 23,46,115.
The lifted quotient test supplies repeatability, rather than inferring
it from those finite replays. These are open strips, not square seeds.
Since the rate is too low, no seed on any residue subsequence can renew
at target within this class. This result does not bound periods larger
than three or periods that grow with the square.

    cargo test --offline --bin sheared_pocket
    cargo build --offline --release --bin sheared_pocket
    target/release/sheared_pocket 3 -12 14
    python3 -B -m analysis.research_program.triple_pocket -3 5 3 23

    cargo build --offline --release --bin triple_pocket
    cargo test --offline --bin triple_pocket
    python3 -B -m analysis.research_program.triple_pocket -3 5 2 16
    python3 -B -m analysis.research_program.triple_pocket -3 5 2 15
    python3 -B -m analysis.research_program.triple_pocket -3 5 3 24

All synthesis variables describe one repeat; replay on longer strips
evaluates a fixed motif without optimizing large squares.
