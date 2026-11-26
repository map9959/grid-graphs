# A repeating overlap dual rules out the residue-two target

**Computer-assisted theorem.** In the full-degree grid spanning-tree
problem, for `n=3k+2>=20`,

    P(n) <= floor(n²/3 + 20n/21 - 67/42)
         = T(k) + floor((23-2k)/14),    T(k)=3k²+7k.

In particular **no feasible tree attains T(k) for any k>=12**. The
first such side is 38: the target is 516 and the upper bound is 515.
This disproves the proposed eventual formula and excludes a uniform
family attaining it; it does not identify the exact replacement formula.
No construction shape, orientation of rails, period of the tree,
maximum status, or boundary coverage is assumed. This is an exact
finite rational certificate plus a counting argument, not a Lean theorem.

## Replay

**Exact finite result at side 23.** The physical witness in
`analysis/research_program/forest_23.txt` attains 196. Its 527 forced
edges form two components on 529 vertices; the independent verifier joins
them with one grid edge and checks all degrees. The separate unpooled
certificate gives `P(23,23) <= 19664286387/100000000 < 197`.
Thus `P(23,23)=196=T(7)` even though the target eventually fails.

    python3 -B -m analysis.research_program.verify_forest_23
    python3 -B -m analysis.research_program.patch_square --replay 23

**Exact extension at side 26.** `P(26,26)=248=T(8)`. Insert three rows
before old row 8 and three columns before old column 1 (zero based).
All 196 old marks survive in `forest_26.txt`; 49 new marks are in the
inserted strips and three are at formerly empty old sites `(1,0)`,
`(20,0)` and `(21,0)`. The 671 distinct forced edges form a forest on
676 sites. Its five components join to give a spanning tree with 248
full-degree vertices. The separate unpooled rational upper bound is
`24850000823/100000000 < 249`. This is a finite extension, not an
induction step asserting the same gain at later sizes.

    python3 -B -m analysis.research_program.extend_forest_23
    python3 -B -m analysis.research_program.patch_square --replay 26

**Side 29 is exact but the insertion chain did not continue.** The
unpooled dual certifies `P(29,29) <= 30635715579/100000000 < 307`.
For the particular saved side-26 grid, the SAT search tried all `27²`
placements of three consecutive new rows and three consecutive new
columns, requiring all 248 old marks to survive. No such placement
returned a score-306 solution. With those requirements removed it found
`forest_29.txt`. Independent replay verifies that all 837 forced edges
are acyclic, joins the four components, and counts 306 full-degree
vertices in the resulting 840-edge tree. Thus `P(29,29)=306=T(9)`.
The exact value relies only on the explicit witness and rational upper,
not on a certified negative result for the seam searches.

    python3 -B -m analysis.research_program.extend_forest_23 --29
    python3 -B -m analysis.research_program.patch_square --replay 29

**Side 32 is exact.** No score-370 witness was found among the 900
three-row/three-column insertion seam pairs preserving every mark of the
saved side-29 grid. The unrestricted search found `forest_32.txt`.
Its 1022 forced edges form two components on 1024 vertices; joining them
gives a spanning tree with exactly 370 full-degree vertices. The unpooled
rational certificate bounds every spanning tree by
`1851071499/5000000 < 371`. Therefore `P(32,32)=370=T(10)`, independent
of the negative seam-search result.

    python3 -B -m analysis.research_program.extend_forest_23 --32
    python3 -B -m analysis.research_program.patch_square --replay 32

**Side 35.** The unpooled rational upper is `8801428903/20000000 < 441`.
Duplicating rows 11–13 and columns 2–4 of the side-32 witness (zero based,
each block inserted immediately before its original) adds 69 marks.
The resulting 439 marked sites force 1221 acyclic edges; joining the
four components produces a 1224-edge tree with 439 full-degree sites.
The physical SAT search returned no witness at 440, first under all
1089 mark-preserving seam pairs and then without seam assumptions.
The upper LP alone does not exclude 440.

    python3 -B -m analysis.research_program.extend_forest_23 --35
    python3 -B -m analysis.research_program.patch_square --replay 35

**The side-35 negative result has now been proof-checked.** The physical
score-440 CNF with 36 independently regenerated, symmetry-expanded cycle
cuts is UNSAT. The dual charges in `side28_sat.cnf` give a necessary
budget: for every oriented forest, average over the eight square images;
each local atom occurrence contributes minus its negative dual residual
divided by its orbit size. The sum cannot exceed the residual-corrected
upper minus the target. Rounding charges down at scale 168 weakens that
constraint. Orient toward corner 0 in its component so the averaged corner
sink condition holds. Each extra cut forbids marking a vertex cover of a
specific physical grid cycle. Thus every actual score-440 forest would
satisfy the CNF. The checked contradiction and 439 witness give
`P(35,35)=439`, the first strict miss of the old target on the `k>=5` branch.

For replay use `python-sat==1.9.dev24` and `pindakaas==0.6.1` as in
`target/pb-python`, CaDiCaL revision `6b3d70b` and drat-trim `2e3b2dc`.
The large proof can be regenerated locally from the small saved cuts:

```
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.side35_unsat
sha256sum target/forest35.cnf
# 316a5d8a092279581188b8fe172464b74fcf081c54c4f9a8e2df627b25c70d81
target/cadical/build/cadical target/forest35.cnf target/forest35.drat
target/drat-trim/drat-trim target/forest35.cnf target/forest35.drat
```

Observed `s UNSATISFIABLE`, then `s VERIFIED` (196683 variables, 916073
clauses, 54230940 resolution steps). This finite proof is separate from
the repeating certificate starting its strict exclusion at side 38.

**The side-38 upper is attained.** After testing the 1296 seam pairs from
the old witness, unrestricted SAT found `forest_38.txt`. Direct replay
gives 515 selected sites, 1442 acyclic forced edges, two components and
1443 completed tree edges. The unpooled rational upper is
`51592859113/100000000 < 516`. Hence `P(38,38)=515`.

Duplicating rows 14–16 and columns 4–6 (zero based) yields a 596-site
forest at 41, the highest marked-site count among all 1296 choices of
literal three-row/three-column duplication. The same insertion produces
verified scores 683, 776, 875, 980 at 44, 47, 50, 53. These are finite
lower witnesses, not a proof that the tail upper bound is sharp.

```
python3 -B -m analysis.research_program.extend_forest_23 --38
python3 -B -m analysis.research_program.patch_square --replay 38
python3 -B -m analysis.research_program.repeat_forest_38
```

    python3 -B -m analysis.research_program.square_dual_physical
    python3 -B -m analysis.research_program.repeating_patch_dual 2 --three --replay

The first command requires only Python's standard library and the
517-term `analysis/research_program/square_dual_stencil.json`. It works
directly on physical square sites without building the LP which found
the certificate. It regenerates the 100 admissible 3-square masks by DFS.
The second command uses the independently stored algebraic dual in
`repeating_patch_dual_2_p3.json` and checks every one of 3,549
coefficient inequalities in exact rational arithmetic. No solver,
large tree search, or floating-point comparison is used by either replay.

## What can be charged on an unrestricted square?

For each site, record its selected bit, its neighbors' bits, and at most
one outgoing forced edge. An edge is forced if at least one endpoint is
selected. Two perpendicular neighbors cannot both be selected: they
would cover the four edges of their unit face. For a real feasible set,
orient each component of its forced forest toward a sink, choosing a
specified corner in its component. Average over the eight square
symmetries. This preserves its score; each physical corner then has
sink probability at least 1/4. It is not necessary that the original
tree be symmetric.

For every 3×3 patch keep the distribution on its nine selected bits.
Its *internal* forced graph must be a forest. The following linear
relations are necessary, with the signs in the saved stencil:

* Site and patch probabilities each sum to one. At a corner,
  four times sink probability is at least one.
* Neighboring star distributions agree on both endpoint labels **and**
  the arrow on their shared edge (or UU, unforced).
* At each of nine relative positions in a patch, the projection of the
  star onto its in-patch labels agrees with the projection of the mask.
* Adjacent patches have identical distributions on their six shared labels.

Only restrictions are used: we never infer a global forest from local
forests. Thus a dual bound for this relaxation is an unrestricted upper
bound. A fractional optimum, or a bound for translation-invariant trees
alone, would not establish the theorem.

## The local inequalities and their extension to every k

Stencil keys `s`, `sp`, `pp` multiply the three kinds of agreement
equalities, `star norm` and `patch norm` multiply normalization, and
`corner` multiplies the corner-sink inequality. The sole nonzero
corner multiplier is -9/14, the correct sign for an upper bound. There
are respectively 67, 242, 170, 23, 14 and 1 nonzero entries.

For a coordinate i on an axis of length S, use type

    i                              if i<d,
    2d+3+i-S                       if i>=S-d,
    d + ((i-d) mod 3)              otherwise.

Use S=n for sites and S=n-2 for patch origins. For agreement terms d=2.
For star/patch normalization take d=6/5. The coefficients are applied
to the relations at the individual physical sites of the indicated
types. They do **not** assert that the star or patch probabilities at
those sites are equal.

For each possible local variable the sum of its dual charges, averaged
over its eight symmetry images, must dominate its objective coefficient
(the site's F bit for stars, zero for patches). `square_dual_physical.py`
adds these charges directly, with west/north edges and the reverse side
of a patch overlap contributing negative sign. It sums over distinct
orbit elements instead of averaging over all eight: each orbit element
has the same stabilizer multiplicity, so this has the same sign. All
residuals are nonnegative integers after clearing denominators.

Here is why the finite check covers all sizes rather than only the
squares printed by the verifier. For a star, every incident agreement
key is determined by its fine (d=6) position type: adjacent star
coordinates differ by at most one; covering patch origins differ by
0, -1 or -2 on each axis, with board length n-2. At a near or far
coordinate its distance from that end is explicit. At a fine bulk
coordinate all valid incident positions are still outside the two
coarse boundary layers, and their phases are fixed by the offsets
modulo three. For a patch the same argument uses fine d=5: its star
coordinates have offsets 0..2, and its other patch origins differ by
at most one. Missing boundary incidences and all normalizations are
therefore fixed by the fine type. Reflection maps a near type to its
far partner, and for a bulk type the reflected residue is determined
by `S mod 3`; transposition just exchanges axes. Consequently the
**eight-image average** for any local atom depends only on its fine
type, its labels and `n mod 3`, even at a position on a symmetry axis.
Every pair of fine coordinates and allowed local atom is represented
at n=20. All larger residue-two squares satisfy these same local
inequalities. There is no extrapolation of finite optimum values.

## Exact boundary correction

All matching relations have right side zero. The objective of this
dual is therefore just the sum of the normalization charges at all
sites/patch origins and the corner charge. Write `n=20+3j`. Each fine
boundary-axis index occurs once; a bulk residue occurs `a+j` times,
where a is its number of occurrences at n=20. Multiply the two axis
counts for each normalization entry. The verifier sums these exact
products symbolically, yielding

    U = 2111/14 + (300/7) j + 3 j²
      = n²/3 + 20n/21 - 67/42.

In particular `U-T=(73-2n)/42=(23-2k)/14`. This is negative already
at k=12 and decreases thereafter.

## Checks and limitations

The direct site/patch replay gives, for example:

| n | physical orbit variables | least scaled slack | U | T |
|--:|--:|--:|--:|--:|
|20|6398|0|2111/14|150|
|23|8873|0|2753/14|196|
|38|24938|0|7223/14|516|
|41|29627|0|8369/14|598|

At 41 the target is `3*13²+7*13=598`. The n=17 finite dual still
replays and is separate from this tail result. Exploratory period-one
charges gave only `n²/3+4n/3-14/3` with the same agreement depth;
the period-three stencil is essential to the improvement shown here.
An exploratory numerical full-size LP on side 23 terminated without
a verified result. It was not used in deriving this theorem.
