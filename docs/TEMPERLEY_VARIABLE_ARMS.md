# Independent boundary-arm depths at period nine

There is no target-gain X of the previously tested centered geometry even
if **each arm is retiled to its own arbitrarily large fixed depth**.
The four saturated period-nine sectors, single X junction and bounded
renewing corner/end neighborhoods are still hypotheses.

## What changed at finite depth

Give all four sides h free doubled rows, measured inward from that side.
This includes unequal choices up to h: reproduce a shallower arm and
copy its saturated background in the newly available rows. Such copying
does not add loss. Minimize each arm independently. The cuts on
neighboring arms need not line up, and the estimate does not assume their
corners fit. In each residue there are 384 layouts times four sides.

Going to h=8 reduced 256 of the old costs from 9 to 6. At h=14, relative
to the old 4/5 depths, 512 costs fell from 9 to 6 and 36 from 7 to 4.
528 combinations violate the checkerboard balance of external domino
ports. This condition is depth independent: giving the arm an extra row
adds nine sites of each color, and every internal matching uses one of
each. In the fixed background every transverse cut therefore carries
the same *signed* imbalance, with the global checkerboard convention.

For h=8 a matching DP across tangent columns gives exact costs. A second
implementation in `deep_arms.py` uses Boolean undirected domino choices,
one match per site and the actual background partners on the cut. For
each of the 11 balanced collar profiles it rejected the DP optimum minus
one and accepted the optimum. At h=14 each of the 11 lower bounds used
in the following calculation was feasible in a separate threshold query.

## Any-depth test

Run a different transfer from a homogeneous cut toward a free physical
boundary. At an even doubled row remember:

1. the 18 sites already matched on the preceding row;
2. the nine vertical primal edge labels on the incoming midpoints;
3. how many primal rows have been passed, modulo nine.

Enumerate every disjoint choice of horizontal dominoes on the current
cyclic row; all remaining unmatched sites must match to the next row.
Do this on the even and subsequent odd row. At each primal site on
the even row, the horizontal midpoint labels and the two vertical ones
now give its full degree d. Charge 0,1,2,0 at d=1,2,3,4 respectively,
the exact number of arrows entering unpreserved interior vertices.
Alternatively terminate on the even row if no domino points past it and
the physical-boundary phase is correct. Charge degree d for an unpreserved
boundary site (d-1 arrows plus one deficiency) and zero for a full site.
Every accepting path gives a cylindrical arm matching; the outgoing
direction pattern of horizontal dominoes is immaterial to later rows.

Start far enough inside the prescribed background at doubled row H,
a multiple of 18. Any finite arm can be padded up to such a cut at zero
cost. For the physical side through that primal cut inclusive, write f
for the preserved count, V for the number of sites, Phi for net inward
flux of all arrows at the cut. The exact loss is

    V + Phi + 9 - 3f .

Indeed the preserved boundary vertices receive two arrows instead of
three; their missing incidences cancel the same correction when adding
the deficiency of the unpreserved boundary vertices. V is a multiple
of nine; Phi is fixed by the background and cut phase. Therefore a
strict improvement on a candidate minimum v must cost **at most v-3**.
All transitions have nonnegative cost. Exhaust the reachable states at
this threshold, keeping the least loss per state. There is no depth cap;
longer paths which revisit a state at greater loss cannot help.

Grouping by the two actual start masks up to even tangential translation
and the proposed minimum gave 11 classes across all sides and residues.
One minimum was zero. None of the other ten admitted a path at threshold
v-3. Largest search: 205,506 reached states. As positive controls,
the normal transfer attained costs 0,3,4 on layouts 0,15,27.
Thus the depth-14 floors suffice for all finite depths (and they are
attainable there). Per residue the cost counts are
`0:256, 3:12, 4:108, 5:108, 6:524`, with 528 unbalanced.

## Shared loss

With the improved arms 982,418 assignments per residue pass the preliminary
relaxation. The directed seam tests at threshold four use 644 translation
orbits rather than the old 552. The resulting **lower** bound on
`2*sum(arm costs)+sum(join costs)` is 20, against an allowance of 18,
on all three k classes. Some seam costs are only lower-bounded; equality
at 20 is not asserted. Center or corner checks cannot rescue a failed
growth inequality, so there is no seed to lift in this class.

    cargo build --offline --release --bin arm_depth --bin diagonal_nine
    cargo test --offline --bin arm_depth
    python3 -B -m analysis.research_program.deep_arms
    python3 -B -m analysis.research_program.deep_arms --arbitrary
    python3 -B -m analysis.research_program.asymmetric_seams 0 4 1 14
