# An actual 3×3 forest constraint cuts off the fractional square

The rational star certificate in `UNRESTRICTED_SQUARE_CURRENT.md` has
no extension to joint distributions on overlapping 3×3 forced forests.
In fact, even a single patch at zero-based corner (2,2) is incompatible.
This rules out a proposed fractional obstruction, not a primal tree.

Number the sites `0,1,2 / 3,4,5 / 6,7,8` in row order. A mask is legal
if the graph of all internal grid edges incident to its F sites is a
forest. Exactly 100 of 512 masks are legal. Edges extending outside the
patch are ignored, a necessary restriction on every feasible square.

Let `P_i(s)` denote the marginal probability of the event specifying
site i's own F/U bit and then its in-patch neighbors in the order east,
south, west, north (skip missing neighbors). Bits use F=1. The following
inequality holds pointwise on every legal mask and hence in expectation:

    P_5(1101) <= P_1(0101) + P_3(0000) + P_4(01010) + P_7(0110).

On the left the entire right-hand column 2,5,8 is F and the central
site 4 is U. Then 1 and 7 must also be U (opposite-corner face cycle).
The right-hand rail already joins 1,4,7. Any two centers in the left
column would force a second path between contacts of that component:
for adjacent centers use their common edge; at separation two use their
intervening site. Thus the only choices for the left column are empty,
top singleton, middle singleton, bottom singleton. The actual masks,
encoded by sum of `2^i` over F sites, are respectively 292,293,300,356.
Each satisfies one of the four events on the right. Exact probabilities
from the old certificate are `1/12 <= 0+0+0+0`, a contradiction.
The test also located support failures on 28 patches of its 14-square
realization. Global single-edge rank inequalities did not detect this
conditional joint obstruction.

## Upper-bound experiment without a template assumption

Use a separate distribution on local oriented star states at **every**
physical vertex. Enforce equality of the shared edge-state distributions
exactly. No fixed-depth ansatz is used when the CLI argument is `all`.
Without loss for this objective, average the square's eight symmetries:
an actual tree can be oriented toward each of the four corners in the
corresponding rotated copy, hence the averaged distribution has sink
probability at least 1/4 at each corner. Identifying only symmetry images
is valid for an upper bound on *all* primal configurations. Extra
uniform interior-type identifications (`depth` supplied as an integer)
are **not** valid for that purpose.

At side 17 the unrestricted star-only relaxation has a checked primal
score `3315473/29550 > 112` and a verified dual upper `<112.201`.
Adding every translated and rotated/reflected copy of the displayed cut
gives the dual upper `11152225169988875357 / 10^17 < 111.523`.
Consequently the integer upper from this method drops **112 -> 111**.
The target at this side is 110; this alone does not settle it. These
are comparisons of relaxations, not improvements over the repository's
recorded exhaustive finite score.

For the full patch test introduce local distributions on all 100 masks;
match each of their nine projected star-label marginals and require
equal six-bit distributions on the 2×3 and 3×2 intersections of adjacent
patches. Every sampled patch enforces actual induced-edge acyclicity.
Orientation marginals are retained at the star level; if feasible, the
result is a *relaxation* of full oriented patch laws, not a gluing theorem.

At n=17 this full overlap model has 4,655 variables and 4,138 distinct
rows. It gives a verified primal of `1553/14` and a verified dual upper
of `55465222943562449/500000000000000 < 111`. Thus **P(17)=110** by
the already verified 110-center witness. This is a different finite
upper certificate, not a uniform theorem. The witness itself uses 45
distinct legal patch masks in its 225 patches. In particular the LP
does not erroneously rule out a target-scoring tree.

Duals are checked with rational arithmetic: clamp nonnegative inequality
multipliers, form every reduced-cost residual, and add its positive part
to the dual objective since each original variable is a probability in
[0,1]. This produces a safe bound without trusting floating-point
optimality. Primal checks recover rational values by elimination on the
positive support and verify nonnegativity and every constraint exactly.

    python3 -B -m analysis.research_program.patch_square
    python3 -B -m analysis.research_program.patch_square --replay
    python3 -B -m analysis.research_program.patch_square 17 all plain
    python3 -B -m analysis.research_program.patch_square 17 all cut --dual
    python3 -B -m analysis.research_program.patch_square 17 all patch --shadow

The `--replay` command loads the sparse rational dual multipliers in
`patch_square_17_dual.json`, checks the model digest and verifies the
upper bound with no external LP solver.
