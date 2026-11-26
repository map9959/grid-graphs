# One bulk axis on the exceptional tail

If `n=35+42t >=119` and a forest attains the integer upper target,
then throughout the square of aligned tile centers at depth at least
14, **all marked center-to-marked-neighbor adjacencies have one common
axis**. There may also be no such adjacencies. This holds in *both*
perimeter-gap cases. It does not assume that all the runs in the forest
are parallel.

An aligned tile center is `(2+3i,2+3j)`. Its nine mark bits, in
row-major order starting with the low bit, define its mask. A vertical
center adjacency means that the center and either its north or south
neighbor are marked. Such a center in tile row `i` restricts the
mask of **every tile of that row in the deep square** to

```
9 18 36 66 72 73 129 132 144 146 258 288 292
```

A horizontal center adjacency analogously restricts its whole tile
column to

```
3 6 7 12 24 33 48 56 96 192 264 384 448
```

These lists are disjoint. If both adjacencies existed, their tile row
and tile column would intersect in a tile required to be on both lists.
This also applies when the centers are far apart.

## Local proof and extension to arbitrary distance

Take two adjacent aligned tiles and all vertices within a six-site
rectangular halo: `15 x 18`, or its transpose. Check the exact
zero-charge rule at every complete star and patch, and consistent
ownership of forced edges. The actual charged star is at depth zero
or two by the [run ledger](RUN_LEDGER.md), outside every such window.
Do not require acyclicity. At side 119 use tile origin `(40,40)`.
Enumerating all assignments *projected to the 18 tile bits* leaves
148 ordered pairs in each direction. A DRAT proof excludes all other
pairs after blocking these 148. For any deep-square adjacency, even
the outermost halo vertex is at depth at least seven. All its complete
stencils therefore have the same bulk types as at the representative:
translations are multiples of three and reflection depends only on
`n mod 3`. No boundary frame assumption is used in the projection.

For a vertical center adjacency the only possible seed masks are
`18,144,146`. Take the union of the forward closure and the backward
closure of these seeds in the **horizontal** ordered-pair relation.
These are separate closures: a tile lies on one side or the other of
the seed. Their union is exactly the first displayed list. Transpose
for the other list. Every actual line follows the relation at every
step. This proves the dichotomy, without needing a common lift of
arbitrary paths in the projected relation.

```
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.saturated_tile_phase --cross
```

The same replay gives an arbitrary-length deficit test. Weight a step
ending in mask `m` by `3-popcount(m)`. From four steps onward the
pairwise **minimum** cost in the projected relation is affine in the
length: among the 586 reachable end pairs, 578 have slope zero and
8 have slope one. The checker verifies the affine induction directly:
every incoming affine candidate has adequate initial value and slope,
and one candidate attains both. A projected minimum is a lower bound
on the corresponding deficit in any physical strip.

## No interior islands of deficit

Call a deep tile deficient if it has fewer than three marks. **Every
deficient tile is joined to the edge of the deep tile square by a chain
of deficient tiles, allowing side or corner contact.** This applies to
both gap cases and does not assume a rail construction.

First, a finite side-connected island of tiles differing from a uniform
full phase cannot be surrounded by that phase. For one of the four
outer stripes this follows by tracing across each row or column from
the forcing side: the stripe propagates unchanged. For the vertical
middle stripe, mask 146, every horizontal segment of the island is
flanked by 146. The masks on any `146 → ... → 146` track belong to the
strongly connected component `{18,144,146}` in the six-halo relation.
They are all subsets of the *same middle column*. This also holds for
the neighboring tiles outside the island, which are 146. If a mark on
the middle column is missing, consider the site immediately to its
left. That site and its four neighbors are unmarked: the possible
middle-column mark on its right is missing, and all other sites are
off the middle column of their tile. This check uses at most the four
side neighbors of the tile. An uncovered site is impossible in the deep
square. Transposition proves the assertion for mask 56, whose vertical
track component is `{24,48,56}`.

Now suppose a king-connected component of deficient tiles misses the
boundary of the deep square. In tile-center coordinates take the union
of the closed squares of radius `3/4` in the maximum norm about its
centers. Their interiors are connected, including at diagonal steps.
Trace the outer boundary of the union, rounding each coordinate to its
nearest integer. This gives a closed walk of **side-adjacent full
tiles**: the trace crosses one half-integer at a time (its segments
lie on quarter-integer lines); its rounded centers are outside the
component but at most one king step from it. All are still in the deep
square and they all have the same phase, by the adjacent-full-pair
rule. A side path from a deficient center to the outside must meet
this walk: at a crossing of the trace its nearest center is a path
vertex. Thus the deficient center lies in a bounded side component
of non-phase tiles surrounded by that phase, which was just ruled out.

The deficit budget on the whole aligned interior is
`D=5k-g+floor((k-5)/7)` for `g` gaps: subtract the `U-(4n-8-g)`
interior marks from `3k²`. Hence all deep defects form boundary-rooted
clusters with **at most `D` cells in total**, not arbitrary sparse
points scattered over the square. For instance a defect at tile
distance `h` from the boundary consumes at least `h+1` such cells.

This also gives a compact description of a candidate's bulk. Record
the deficient tiles and their masks, the boundary phases, and in each
tile row the left and right extreme-phase prefixes/suffixes (likewise
in each column for the top and bottom phases). Every remaining full
tile must have the *single* allowed middle orientation. The sum of
the successive absolute changes of the four recorded run lengths is at
most `4D`: each unit change crosses an edge between an extreme full
tile and a deficient neighbor, since adjacent full tiles agree. No
edge is counted twice. These constraints locate where a search for a
period-42 shortening actually has to handle nonuniform marks.

## Side 245: all two-gap cases excluded

The full-board two-gap test retains the matching on complementary face
edges, the rooted orientation and unique charged boundary exit, and a
disjunction of all 15 frame classes modulo square symmetry. Add one
flag for each tile row or column with a center adjacency and enforce
the two inherited word lists plus the common axis. No end mask or
connector route is prescribed. CaDiCaL returned UNSAT; `drat-trim`
verified the proof. The CNF has 838,523 variables and 10,379,179 clauses,
SHA-256 `e90425d26efe7913bbf115ccf2e127a677c8a0595fa6e486f46f7692e6b3f44d`.

```
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.two_gap_board 245 300 all --axis
```

This last exclusion is finite. The common-axis theorem is uniform.
The [remaining one-gap interface tests](SOUTHWEST_PORTS_245.md)
apply to different branches and do not by themselves exhaust them.
The [subsequent rooted-tile proof](TILE_CASES_245.md) exhausts them.

The compact DRAT stream is 1,486,443 bytes (SHA-256
`18b63a5a1768cb5f64a3714a4fefa01d71522ef69280dec50473e3cdcd39dcaf`).
Rechecking it took 1,234,659 resolution steps. The abstract implication
from track closures to the rectangular crossing contradiction is also
checked in `lean/GridGraphs/Geometry/BulkAxis.lean`; the local projection
uses SAT/DRAT, not Lean.

## Boundary fluxes beyond the axis test

On a square of four adjacent tiles the six-site-halo projection has
490 mark quadruples. A horizontal two-tile word has the same indicator
above and below each such square if it is `(24,73)` or `(292,48)`.
Vertically the corresponding words are `(18,7)` and `(448,144)`.
Consequently one occurrence repeats along the entire perpendicular
track. Neither end of any of these four tracks can meet a clean flat
side: the eight endpoint formulas are independently DRAT-checked. The
physical endpoint windows at opposite ends are disjoint. Since at most
one contains the charged star, the four words are impossible *anywhere*
in the deep square, for every exceptional upper witness.

```
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.tile_circulation 0 --cert
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.tile_flux_ports 6
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.tile_flux_closure --cert
```

Using the entire ordered-pair relations, rotate the charged side to
north and require reachability from all three clean sides. This removes
32 of the 490 quadruples, retaining 458 before fixing the axis. With
either axis fixed, 391 of 413 survive. These are necessary languages,
not proof that arbitrary labelings with these quadruples glue to trees.
