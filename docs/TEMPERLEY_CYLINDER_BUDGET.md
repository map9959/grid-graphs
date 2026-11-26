# Arbitrary normal width at longitudinal period (6,6)

This is a computational obstruction for a class of diagonal-interface
constructions, not a nonexistence result for grid spanning trees.
Keep the base-five periodic arms and the two saturated triangular
backgrounds from the synthesis experiment. In between, allow **any**
domino matching invariant under doubled translation (12,12), equal to
the prescribed backgrounds sufficiently far to each side. The two
distances from the diagonal can be arbitrarily large. They are fixed for
a proposed repeatable interface. The argument bounds its asymptotic
increment, not its score on a small square in which the band hits a corner.

## Cut account and why widening cancels

For a full longitudinal period of primal vertices S in normal coordinates
`L <= r-c <= R`, define Phi as the signed inward flux of **all** primal
arrows across the two ends. Every site sends one arrow and each preserved
site receives three. With D counting arrows entering unpreserved vertices
of S, this gives the exact identity

    3 f(S) = |S| + Phi - D,             D >= 0.

On a normal slice there are six primal vertices. Either homogeneous rail
background preserves exactly two per slice, irrespective of rail phase or
orientation. D is zero in a homogeneous background. The reference cut
in the regional calculation is [-12,12], containing all sites whose score
may depend on the original three-tile band. Let B be the number of known
background centers in this reference cut, excluding those mutable sites.
Let H be the gain still required from the band after reserving the actual
background contribution and the four independent arm upper bounds.
Then the permitted loss is

    budget = |S| + Phi - 3 B - 3 H.

This budget uses no assumed matching of the three-tile band. To apply it to
a *wider* interface, enclose that interface by moving the ends of S into
the same background cut phases (whole multiples of six normal slices).
Phi is unchanged. Each added slice increases |S| by 6 and the reference
background count B by 2; hence the budget is unchanged. B is a subtraction
of the old background contribution, **not** a claim that the wider band
still contains those centers.

Equivalently, in the square score difference under side +6, each fixed
normal slice far from the end caps contributes one extra longitudinal
period. Replacing any finite-width diagonal strip changes the increment by
its score per period minus the reference score per period over the same
strip. For this comparison the finitely many end neighborhoods must repeat
on the chosen parity; a constant end score cancels. The calculation does
not cover a cap whose score grows with side, a second interface, or a strip
whose width itself grows on successive squares.

## Transfer, without any cutoff on normal distance

Use doubled normal slice `d=row-column`, with column modulo 12. Each
site's two forward neighbors have columns c or c-1. Enumerate all ways
to send the unoccupied sites forward, rejecting collisions. Take two
slice steps at a time. At each even slice the source mask from the last
odd slice and that from the next odd slice determine the four incident
edge labels at every primal site. A vertex of degree 1,2,3,4 receives
0,1,2,3 arrows respectively; its contribution to D is 0,1,2,0. Thus all
transition costs are nonnegative.

The key contains occupied sites, preceding vertical matches, preceding
midpoint labels, and normal phase modulo six primal slices. Relax a state
again only when its least known loss decreases. Exhaust the work queue
up to the source's largest relevant budget, not up to a depth bound.
This includes loops of arbitrary length. Testing the terminal state's
minimum against each individual pair's budget is necessary for an
interface. Forgetting length other than phase only enlarges the set, so
negative answers are valid exclusions. Terminal phase 1 corresponds to the
cut just after primal slice 12; the initial phase is 0 at -12. Test all
nonnegative budgets, including pairs excluded by the earlier rail-end
inequality, so that inequality is not required for the result.

## Results and replay

Centered split on both parities: of 1,296 layout pairs per parity, 72 had
budget zero, 32 budget one, 4 budget two, the rest negative. Twelve source
searches per parity, up to 20,490 reached states each: **zero target
transitions**. For split (1,1) the corresponding budget counts were
18,8,1; for (2,5) they were 38,16,2. Both parities again had no survivors.
The arm upper bounds are solver-assisted; a local timeout retains its old
upper bound, never an exclusion. The cylinder calculation itself uses no
SAT solver.

As a cross-check independent of the arm budgets, give all 1,296 centered
background pairs an allowance of two. The 36 identical pairs have minimum
loss zero. Exactly 54 directed nonidentical pairs have minimum loss two;
none have minimum one, and the other 1,206 are not reached at cost <=2.
Thus the transfer does find changes of background; the negative target
result comes from comparing their costs with the individual arm budgets.

    cargo build --release --offline --bin diagonal_budget
    cargo test --offline --bin diagonal_budget
    python3 -B -m analysis.research_program.cylinder_budget

The 240 positive controls include 96 unmodified periodic backgrounds, 48
changed exit profiles from a realizable elementary flip and 96 independently
scored one-loss paths. Pass `--all-splits` to run all 36 base-five splits
up to transposition, one parity at a time. The local unit
test checks every four-edge occupancy pattern in each primal column,
including the wrapped neighbor. No large generated datasets are needed.
