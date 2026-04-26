# Diagonal Proof Program for `P(n,n)`

This note records the proof path suggested by the exact diagonal data through
`n = 15` and the Lean-formalized forced-edge lemma. The goal is to stop
chasing larger square computations and reduce Conjecture C to a clean finite
grid covering/decycling theorem.

## Progress ledger

### Formalized in Lean

* `GridGraphs.Forced`: full-degree vertices force all incident grid edges;
  therefore every actual full set has an acyclic forced-edge graph.
* `GridGraphs.Diagonal`: the complement `U` of a full set is an induced-edge
  decycling set; every grid unit cell in an acyclic forced-edge graph has a
  boundary `U-U` edge.

### Verified computationally

* Exact diagonal values through `n = 15`:
  `1, 2, 4, 8, 11, 16, 22, 27, 34, 42, 49, 58, 68, 77, 88`.
* `fullub-witness 13 13`, `14 14`, and `15 15` certify the last three values
  by matching forced-edge upper bounds with completed spanning-tree witnesses.
* The local cell-hitting relaxation is too weak after `n = 4`.
* The `n ≡ 1 (mod 3)` construction pattern is explicit and dual-connected for
  `n = 4, 7, 10, 13, 16`.
* `analysis/check_diagonal_patterns.py` verifies the `n ≡ 1 (mod 3)` pattern
  through `n = 40`, including forced-edge acyclicity, greedy tree completion,
  and exact full-degree counts.

### Rejected

* Simple count-matching residue-0 and residue-2 extensions of the residue-1
  strip pattern. They have the right `|U|` but disconnected dual graphs.

### Main open proof tasks

1. Prove the planar-dual equivalence between primal forced-edge acyclicity and
   dual connectivity of `U-U` edges.
2. Find clean parametric `U` constructions for `n ≡ 0, 2 (mod 3)`.
3. Prove the induced-edge decycling lower bound for all `U` with connected dual
   face graph.

### Cached witness data

The expensive `fullub-pattern` outputs for n = 12, 13, 14, 15 are cached in:

```text
data/diagonal_u_12.txt
data/diagonal_u_13.txt
data/diagonal_u_14.txt
data/diagonal_u_15.txt
```

Use these files for pattern analysis instead of rerunning `fullub-pattern`.
For example:

```bash
python3 analysis/u_pattern_stats.py < data/diagonal_u_14.txt
python3 analysis/dual_decycling.py < data/diagonal_u_14.txt
```

## Target theorem

For `n >= 4`, conjecturally

```text
P(n,n) = floor(n^2 / 3) + n + C(n mod 3),
```

where

```text
C(1) = -1,
C(0) = C(2) = -2.
```

Equivalently, if `U` denotes the non-full-degree vertices in an optimal tree,
then the conjectured minimum size of `U` is:

```text
n = 3k:     |U| = 6k^2 - 3k + 2
n = 3k + 1: |U| = 6k^2 + k + 1
n = 3k + 2: |U| = 6k^2 + 5k + 3
```

This is exact for `n = 4..15`.

## Proven reduction: forced edges

Let `G = G(n,n)` be the square grid graph. Let `T` be a spanning tree of
`G`, and let `F` be the set of full-degree vertices in `T`. Put `U = V \ F`.

If `v in F`, then every grid edge incident to `v` must lie in `T`.
Therefore every edge touching `F` is forced into `T`.

Define

```text
H(F) = (V, {uv in E(G) : u in F or v in F}).
```

Then

```text
H(F) subset T.
```

Since `T` is acyclic, `H(F)` is acyclic.

This is formalized in Lean as:

```text
GridGraphs/Forced.lean
forcedEdgeGraph_le_of_preserves
forcedEdgeGraph_isAcyclic_of_preserves
grid_forcedEdgeGraph_isAcyclic_of_preserves
```

So the true optimization satisfies

```text
P(n,n) <= max |F| such that H(F) is acyclic.
```

The Rust command `fullub n n` computes this right-hand side exactly for
`n <= 15`.

## Equivalent decycling formulation

Since `H(F)` contains exactly the grid edges **not** internal to `U`, the
forced graph is

```text
H(F) = G - E(G[U]).
```

Thus the upper-bound problem is equivalent to finding the smallest vertex
set `U` such that deleting the induced edge set `E(G[U])` makes the grid
acyclic:

```text
q(n) := min {|U| : G(n,n) - E(G(n,n)[U]) is a forest}.
```

Then

```text
P(n,n) <= n^2 - q(n).
```

The diagonal theorem would follow from the exact formula for `q(n)` above,
plus a matching spanning-tree construction.

## Local necessary condition: every cell needs a `U-U` edge

Every unit square is a 4-cycle. If none of its four boundary edges is a
`U-U` edge, then every boundary edge touches `F`, hence every boundary edge
is in `H(F)`, creating a forced cycle. Therefore:

```text
For every 2x2 cell, at least one boundary edge has both endpoints in U.
```

This cell-hitting condition is necessary but not sufficient: larger
rectangular cycles also have to be broken. The full condition is the forest
condition on `G - E(G[U])`.

The helper `analysis/cell_hitting.py` computes the local relaxation. It agrees
with the conjectured decycling number only at `n = 4`; after that it is much
too small:

```text
n,local_min,conjectured_q
4,8,8
5,10,14
6,18,20
7,21,27
8,32,37
9,36,47
10,50,58
11,55,72
12,72,86
13,78,101
14,98,119
15,105,137
```

Therefore the diagonal upper bound cannot be proved from unit-cell hitting
alone. The proof must use the full induced-edge decycling/forest condition.

## Proposed upper-bound theorem

The upper-bound side is now a standalone combinatorial theorem:

```text
Theorem (induced-edge decycling number of the square grid).
For n >= 4, every U subset V(G(n,n)) such that G(n,n) - E(G(n,n)[U])
is a forest satisfies

  |U| >= 6k^2 - 3k + 2      if n = 3k,
  |U| >= 6k^2 + k + 1       if n = 3k + 1,
  |U| >= 6k^2 + 5k + 3      if n = 3k + 2.
```

This theorem would imply the desired diagonal upper bound immediately by the
forced-edge lemma.

## Planar-dual formulation of the upper bound

The full forest condition has a useful planar-dual interpretation. Let

```text
S = E(G[U])
```

be the set of deleted `U-U` primal edges. A primal cycle survives in
`G - S` iff no edge of that cycle lies in `S`. In the planar dual, primal
cycles correspond to cuts separating a set of bounded faces from the exterior.
Thus:

```text
G - S is a forest
iff
the dual edges S* connect every bounded cell-face to the exterior face.
```

For the square grid this means the `U-U` edges must form a connected network
in the dual cell graph, connecting all `(n-1)^2` cells to the outside. Boundary
`U-U` edges connect adjacent boundary cells to the exterior face; interior
`U-U` edges connect the two cells on either side of that edge.

This is stronger than the local `2x2` cell-hitting condition. Cell hitting says
each face has at least one incident dual edge. The forest condition says those
incident dual edges must globally connect all faces to the exterior.

The next upper-bound proof should therefore be a minimum-vertex theorem for
sets `U` whose induced primal edges yield a connected dual face graph.

### Planar-dual equivalence proof sketch

Let `G` be the `n x n` grid graph embedded in the plane. Let `S` be any set of
primal edges, and let `S*` be the corresponding set of dual edges in the planar
dual whose vertices are the `(n-1)^2` bounded cell-faces plus the exterior
face.

Claim:

```text
G - S is a forest  iff  (V(G*) , S*) is connected.
```

Here `(V(G*) , S*)` means the spanning dual graph with all faces as vertices and
only the duals of edges in `S` as edges.

Proof direction `=>`:

Suppose `(V(G*) , S*)` is disconnected. Then there is a nonempty proper set of
faces `A` not containing the exterior face and with no `S*` edge crossing from
`A` to its complement. The boundary between `A` and its complement is a union
of closed primal edge-disjoint cycles. Since no crossing dual edge lies in
`S*`, none of those boundary primal edges lies in `S`. Hence at least one
primal cycle remains in `G - S`, contradicting that `G - S` is a forest.

Proof direction `<=`:

Suppose `G - S` contains a cycle `C`. By the Jordan curve theorem in the grid
embedding, `C` separates at least one bounded face from the exterior. Let `A`
be the set of bounded faces inside `C`. Every dual edge crossing from `A` to
the complement corresponds to a primal edge of `C`. Since `C` lies in `G - S`,
none of these crossing primal edges is in `S`; hence none of the crossing dual
edges is in `S*`. Therefore `A` is separated from the exterior in `(V(G*),S*)`,
so that dual graph is disconnected.

This is the standard planar cycle/cut duality specialized to the rectangular
grid. For a Lean proof, avoid invoking Jordan curve theorem generally: define
the grid dual explicitly and prove the equivalence by induction on finite
rectangular cell regions or by using mathlib planar graph infrastructure if it
is available. The informal proof is enough for the next combinatorial step.

For our problem, `S = E(G[U])`, so the upper-bound theorem becomes:

```text
If the dual graph formed by U-U edges connects all cell-faces to OUT,
then |U| is at least the conjectured q(n).
```

The helper `analysis/dual_decycling.py` checks this dual graph for witness
patterns. Current outputs:

```text
n=13
|U|=101 conjectured_q=101 match=True
dual_vertices=145 dual_edges=144
faces_connected_to_out=145/145 all_connected=True
row_U=1,12,12,1,12,12,1,12,12,1,12,13,0
strip3_U=0:25,1:25,2:25,3:26

n=14
|U|=119 conjectured_q=119 match=True
dual_vertices=170 dual_edges=170
faces_connected_to_out=170/170 all_connected=True
row_U=0,14,10,10,9,9,8,9,9,10,7,10,12,2
strip3_U=0:24,1:28,2:26,3:27,4:14

n=15
|U|=137 conjectured_q=137 match=True
dual_vertices=197 dual_edges=197
faces_connected_to_out=197/197 all_connected=True
row_U=1,14,12,5,12,9,10,9,10,10,10,10,9,13,3
strip3_U=0:27,1:26,2:29,3:30,4:25
```

The n = 13 witness is especially structured: each full 3-row strip has 25
non-full vertices, and the final residue strip has 26. The n = 14 and n = 15
witnesses are optimal but less canonical, likely because `fullub` tie-breaking
is not optimized for visual regularity. The construction proof should search
for a cleaner representative, not necessarily use these exact rows.

Additional cached pattern stats:

```text
n = 14 row counts:
1,13,10,10,9,9,8,9,9,9,9,9,12,2
strip totals: 24,28,26,27,14
mod3 counts:
  11,16,13
  11,16,15
   9,15,13

n = 15 row counts:
1,14,12,5,12,9,10,9,10,10,10,10,9,13,3
strip totals: 27,26,29,30,25
mod3 counts:
   7,19, 9
  18,25,15
  12,22,10
```

The row-word summaries from `analysis/u_pattern_stats.py` show repeated
`.UU` / `.UU.UU` motifs. For example, many n = 14 rows are built from runs
like

```text
.1 U2 .1 U2 .1 U3 .1 U2 .1
.1 U2 .1 U2 .1 U1 .1 U4 .1
```

and n = 15 contains a diagonal sequence of length-4 `U` runs moving rightward:

```text
.1 U2 .1 U4 .1 U2 .1 U2 .1
.1 U2 .1 U2 .1 U4 .1 U2 .1
.1 U2 .1 U2 .1 U2 .1 U4 .1
```

This suggests the residue-0 and residue-2 constructions may be built by routing
a width-2 `U` backbone through a periodic grid of holes, with occasional
length-4 runs to keep the dual network connected between strips.

### Tile-matrix view

The helper `analysis/tile_catalog.py` groups a cached witness into 3x3 tiles
and assigns labels to distinct tiles. This is the right abstraction level for
the remaining construction search: the residue classes appear to be finite
tile systems plus boundary tiles.

For `n = 13` (`n ≡ 1`), the tile matrix is almost a rectangle of one tile:

```text
D A A A B
D A A A B
D A A A B
E A A A B
C C C C F
```

where the repeated interior tile is

```text
A = ...
    UUU
    UUU
```

For `n = 14` (`n ≡ 2`), one optimal witness has tile matrix:

```text
B C C C F
A A G H D
A A B I D
A A B J D
K E E E L
```

The common tile

```text
A = .UU
    .UU
    .UU
```

acts as a vertical width-2 backbone. The exceptional tiles `G,H,I,J` route the
dual connection horizontally through the middle/right of the square.

For `n = 15` (`n ≡ 0`), one optimal witness has tile matrix:

```text
E E F F B
C G H H B
I A A A A
C C J K A
G D D D B
```

with repeated tiles

```text
A = UU.      C = .UU      D = .UU
    UU.          .UU          UUU
    UU.          .UU          ...
```

This strongly suggests a tile grammar: use vertical backbone tiles (`.UU` or
`UU.` columns), horizontal cap tiles (`.../UUU/...` variants), and a small set
of turn/bridge tiles to route a dual spanning tree through the face grid.

The remaining construction task is to find a periodic tile grammar that
generalizes the n = 14 and n = 15 matrices, preferably with a simple repeating
interior and finitely many residue-boundary patches.

The symmetry-reduced catalog from

```bash
python3 analysis/tile_symmetry.py data/diagonal_u_12.txt data/diagonal_u_14.txt data/diagonal_u_15.txt
```

is especially informative. Nearly all full 3x3 tiles in the residue-0/2
witnesses belong to two dihedral symmetry classes:

```text
C1: 5-U cap/turn class, canonical representative
...
UUU
.UU

C2: 6-U slab/backbone class, canonical representative
...
UUU
UUU
```

There is a smaller 6-U bridge/turn class

```text
C3:
..U
UUU
UU.
```

and only a few exceptional bridge tiles, notably `U.U/U.U/UUU` and
`U.U/U.U/U.U` in the n = 14 witness.

This suggests a much sharper construction hypothesis:

* The bulk of every optimal `U` pattern is a tiling by C1 and C2 tiles.
* C1 tiles reduce the count by one relative to a 6-U slab tile while preserving
  dual routing through a turn/cap.
* C3 and the rare exceptional tiles are used only to connect C1/C2 regions or
  handle residue boundaries.

If this is correct, residues 0 and 2 may be described by a finite-state path of
C1/C2/C3 tiles through the 3x3 tile grid, rather than by row-level formulas.

`analysis/tile_class_matrix.py` prints this symmetry-class view. For the cached
witnesses:

```text
n=12:
C1 C2 C2 C1
C1 C3 C2 C1
C1 C3 C1 C1
C1 C2 C1 C1

n=14:
C1 C1 C1 C1
C2 C2 C3 C4
C2 C2 C1 C5
C2 C2 C1 C6

n=15:
C1 C1 C2 C2 C1
C2 C1 C1 C1 C1
C4 C2 C2 C2 C2
C2 C2 C3 C3 C2
C1 C1 C1 C1 C1
```

Here `C1` is the 5-U cap/turn class and `C2` is the 6-U slab/backbone class.
Thus most of the count is controlled by how many C1 tiles are used. In an
`n = 3k` square, the tile grid is `k x k`, and the conjectured count

```text
6k^2 - 3k + 2
```

is exactly what one gets from all 6-U tiles after replacing `3k-2` of them by
5-U tiles (plus bridge tiles that also have 6 or 7 U's). For `k=4`, the n=12
class matrix has ten C1 tiles, two C3 tiles, and four C2 tiles:

```text
10*5 + 2*6 + 4*6 = 86 = 6*16 - 10.
```

This suggests the residue-0 upper/lower construction should be described by a
path or cutset of `3k-2` count-saving C1 tiles through a sea of C2 tiles, with
O(1) bridge corrections. The residue-2 case should have an analogous tile-grid
statement with different boundary tiles.

### Crop-and-reroute hypothesis

Another useful viewpoint: the residue-0 and residue-2 witnesses are close to
croppings of the clean residue-1 construction at the next larger `n ≡ 1`
size. Use

```bash
python3 analysis/crop_diff.py 14
python3 analysis/crop_diff.py 15
```

to compare cached witnesses against those croppings.

For `n = 14`, cropping the `n = 16` residue-1 construction gives 122 vertices
of `U`, while the optimum has 119. The actual witness performs a reroute with
`35` added vertices and `38` removed vertices. The additions occur almost
entirely in sparse rows `3, 6, 9, 12`; removals occur in the adjacent dense
rows at periodic columns such as `3, 6, 10, 13`.

For `n = 15`, cropping the `n = 16` residue-1 construction gives 146 vertices
of `U`, while the optimum has 137. The actual witness performs a larger
reroute with `32` additions and `41` removals. Again, additions concentrate in
sparse rows `3, 6, 9, 12`, while removals form periodic holes in neighboring
dense rows and the bottom boundary.

This suggests a constructive route for residues 0 and 2:

1. Start from the next larger residue-1 construction.
2. Crop to the target square.
3. Replace selected dense-row columns by sparse-row routing bridges.
4. Delete redundant boundary vertices.

The net effect must preserve dual connectivity while reducing `|U|` by exactly
the residue correction. The observed modifications are periodic enough that a
finite patch rule may exist.

### Rejected simple extensions

Two obvious count-matching extensions of the `n ≡ 1 (mod 3)` strip pattern were
tested for the other residues:

* `n = 3k`: repeat row counts `1, n-2, n-2`, with final block
  `1, n-2, n`.
* `n = 3k+2`: repeat row counts `1, n-2, n-2`, then add one all-`U` row and
  a sparse bottom row of `k+1` vertices.

Both match the conjectured cardinalities, but `analysis/dual_decycling.py`
shows that their dual graphs are disconnected for the tested sizes. They are
therefore invalid constructions. The rejected patterns are still available for
inspection via

```bash
python3 analysis/diagonal_patterns.py --experimental 12 | python3 analysis/dual_decycling.py
python3 analysis/diagonal_patterns.py --experimental 14 | python3 analysis/dual_decycling.py
```

This failure is useful: the remaining residue classes need either different
boundary routing or a different strip motif, not just trimming the residue-1
construction.

### First counting consequences

Dual connectivity immediately gives the weak edge lower bound

```text
|E(G[U])| >= (n - 1)^2,
```

because the dual face graph has `(n - 1)^2 + 1` vertices. This alone is far
too weak: a large induced subgraph of the square grid can have nearly `2|U|`
edges, so it only suggests `|U| ≳ n^2/2` while the conjectured value is about
`2n^2/3`.

The missing ingredient must use geometry of how `U-U` edges can connect the
dual faces. A plausible strip-counting theorem is:

```text
In every three consecutive rows, a dual-connected U pattern must spend roughly
2n vertices, with boundary/residue corrections.
```

This matches the leading term `|U| ~ 2n^2/3` and explains why a 3-strip proof
is the natural next target.

### Structural hypothesis for the upper bound

Think of `E(G[U])` as a dual-connected network. Each `U` vertex can support at
most four incident `U-U` primal edges, but the cheap edge count is too weak.
What appears to matter is **routing through consecutive rows**:

* A row with very few `U` vertices can act as a sparse connector, but then the
  neighboring rows must be dense enough to keep all adjacent faces connected in
  the dual.
* In a 3-row window, the witnesses spend roughly `2n` vertices, with boundary
  corrections. This matches the leading term of the conjectured `q(n)`.
* The residue-1 construction has the clean window pattern `(1, n-1, n-1)`,
  with a final `(1, n-1, n)` correction. Residues 0 and 2 require more subtle
  horizontal routing because the naive trimmed versions disconnect the dual.

A possible counting theorem to aim for is:

```text
For each block of three consecutive rows, except for boundary correction terms,
dual connectivity forces at least 2n - O(1) vertices of U in the block.
```

The hard part is making the `O(1)` corrections sharp enough to recover all
three residue formulas.

The residue formulas can be rewritten in a strip-counting form. Write
`n = 3k + r`:

```text
r = 0: |U| = 6k^2 - 3k + 2 = k(2n - 3) + 2
r = 1: |U| = 6k^2 + k + 1  = k(2n - 1) + 1
r = 2: |U| = 6k^2 + 5k + 3 = k(2n + 1) + 3
```

So the upper-bound proof should probably show that each complete 3-row strip
costs at least

```text
2n - 3,  2n - 1,  or  2n + 1
```

depending on how the strip interacts with the top/bottom residue boundary,
plus a global correction of `2`, `1`, or `3`. This is more precise than the
earlier heuristic `roughly 2n per strip`.

For the known witnesses, strip totals fluctuate around exactly these values:

```text
n=12 (r=0, 2n-3=21): strip totals 21,21,22,22 in cached witness
n=13 (r=1, 2n-1=25): strip totals 25,25,25,26 in clean construction
n=14 (r=2, 2n+1=29): strip totals 24,28,26,27,14 in one noncanonical witness
n=15 (r=0, 2n-3=27): strip totals 27,26,29,30,25 in cached witness
```

The residue-0 and residue-2 witnesses are not aligned to simple horizontal
strips, which explains the fluctuations. A successful proof may need sliding
3-row windows or diagonal strips rather than fixed bands starting at row 0.

The cached witnesses support this. `analysis/u_pattern_stats.py` now prints
sliding 3-row totals. Examples:

```text
n=12 sliding3 totals:
22,25,24,22,23,23,21,25,26,21

n=14 sliding3 totals:
24,33,29,28,26,26,26,27,27,27,30,23

n=15 sliding3 totals:
27,31,29,26,31,28,29,29,30,30,29,32,25
```

The minima are below the naive per-strip average in some places, but only when
neighboring windows compensate. This suggests a discharging proof over
overlapping 3-row windows: sparse windows must be adjacent to denser windows,
because otherwise the dual connection cannot pass through that region.

### Likely proof shape

Work with `U-U` edges as the deleted edges. The grid has cyclomatic number

```text
beta(G(n,n)) = |E| - |V| + 1 = (n - 1)^2.
```

So any successful `U` must delete at least `(n - 1)^2` edges, but this
edge-count lower bound is too weak by itself. The missing ingredient should
be a boundary/strip accounting argument showing that induced deleted edges
cannot be packed densely enough unless `|U|` has the claimed size.

Promising decomposition:

1. Partition the square into horizontal strips of height 3, plus a residue
   boundary strip of height 0, 1, or 2.
2. In each 3-row strip, count how many `U` vertices are needed to break all
   forced cycles crossing the strip and adjacent strip boundary.
3. Add correction terms for the top/bottom boundary and the rightmost residue
   columns.
4. Recover the three formulas for `n mod 3`.

The witnessed patterns below strongly suggest this 3-strip structure.

## Lower-bound construction program

For the lower bound we need, for every `n`, an explicit set `F` of the target
size and a spanning tree `T` in which every vertex of `F` is full-degree.

The `fullub-witness` command already proves this for `n = 13, 14, 15`:

```text
fullub-witness 13 13 -> fullub = 68, completed tree full count = 68
fullub-witness 14 14 -> fullub = 77, completed tree full count = 77
fullub-witness 15 15 -> fullub = 88, completed tree full count = 88
```

The completion step is simple:

1. Force all edges touching `F`.
2. Check the forced graph is a forest.
3. Greedily add remaining `U-U` grid edges connecting different components.
4. If this reaches `n^2 - 1` edges, the result is a spanning tree and all
   vertices of `F` are full-degree.

To prove the lower bound generally, we need a parametric `F_n` or `U_n`
pattern whose forced graph is visibly a forest and whose components can be
connected by `U-U` edges.

### Lemma C: forest completion by non-forced edges

This generic lemma is the bridge from a valid `U` pattern to a spanning-tree
construction.

**Lemma.** Let `G` be a connected graph, `F` a vertex set, and `U = V \ F`.
Let `H` be the forced-edge graph containing every `G`-edge incident to `F`.
Assume:

1. `H` is a forest.
2. Contracting each connected component of `H`, the graph whose edges are the
   remaining `U-U` edges is connected on the contracted components.

Then `H` can be extended to a spanning tree of `G` by adding only `U-U` edges.
Consequently every vertex in `F` is full-degree in the completed tree.

**Proof.** Contract the components of `H`. Since `H` is a forest, adding an
edge between two distinct components preserves acyclicity. By assumption, the
available `U-U` edges connect the contracted component graph, so choose any
spanning tree of that component graph and add the corresponding `U-U` edges to
`H`. The result is connected and acyclic, hence a spanning tree. No added edge
touches `F`, so every vertex of `F` remains incident to exactly all of its grid
edges and is full-degree.

In the planar-dual construction checks, dual connectivity of `E(G[U])` implies
`H` is a forest. The greedy completion check verifies condition 2 explicitly.
For a paper proof, it is cleaner to define connector `U-U` edges explicitly and
show they connect the forced-forest components.

Lean note: `GridGraphs.Diagonal.connected_graph_has_spanning_tree` now records
the mathlib fact that any finite connected graph has a spanning tree subgraph.
This is weaker than Lemma C because it does not guarantee the spanning tree
contains a specified forced forest. The formal forest-extension lemma remains
open.

### Proposition L1: residue 1 lower-bound construction (`n = 3k + 1`)

**Statement.** For every `k >= 1`, with `n = 3k + 1`, there is a spanning
tree of `G(n,n)` with

```text
floor(n^2/3) + n - 1
```

full-degree vertices. Equivalently, there is a non-full set `U` with

```text
|U| = 6k^2 + k + 1
```

such that the forced graph on `F = V \ U` is a forest and can be completed to a
spanning tree by adding only `U-U` edges.

This proves the lower-bound half of Conjecture C for `n ≡ 1 (mod 3)`, assuming
the standard forced-edge completion lemma.

#### Definition of `U_{3k+1}`

The `n = 13` witness reveals a clean infinite pattern, implemented in
`analysis/diagonal_patterns.py`.

For `n = 3k + 1`, define `U` as follows. The bottom row is all full, i.e. no
vertices in `U`. For each 3-row block `t = 0, ..., k-1` with first row
`r = 3t`:

```text
row r:     only column 1 is in U
row r + 1: columns 1..n-1 are in U
row r + 2: columns 1..n-1 are in U, except in the final block where all
           columns 0..n-1 are in U
```

For `k = 4` (`n = 13`) this is exactly:

```text
.U...........
.UUUUUUUUUUUU
.UUUUUUUUUUUU
.U...........
.UUUUUUUUUUUU
.UUUUUUUUUUUU
.U...........
.UUUUUUUUUUUU
.UUUUUUUUUUUU
.U...........
.UUUUUUUUUUUU
UUUUUUUUUUUUU
.............
```

Cardinality:

```text
(k - 1) * (1 + 2(n - 1)) + (1 + (n - 1) + n)
= (k - 1) * (2n - 1) + 2n
= 6k^2 + k + 1,
```

which is the conjectured `q(3k+1)`.

The script check

```bash
python3 analysis/diagonal_patterns.py 16 | python3 analysis/dual_decycling.py
```

returns

```text
|U|=156 conjectured_q=156 match=True
dual_vertices=226 dual_edges=225
faces_connected_to_out=226/226 all_connected=True
```

and similarly for `n = 4, 7, 10, 13`. Since the dual graph has
`dual_vertices - 1` edges and is connected, it is a dual tree. This gives a
particularly clean construction proof for the `n ≡ 1 (mod 3)` family once the
planar-dual equivalence is written down formally.

The stronger construction checker

```bash
python3 analysis/check_diagonal_patterns.py 40
```

verifies every `n ≡ 1 (mod 3)` case up to `n = 40` by explicitly completing the
forced forest to a spanning tree. Its output includes:

```text
n,nonfull,expected_nonfull,full,expected_full,edges,status
4,8,8,8,8,15,True
7,27,27,22,22,48,True
10,58,58,42,42,99,True
13,101,101,68,68,168,True
16,156,156,100,100,255,True
...
40,1028,1028,572,572,1599,True
```

This is strong evidence that the residue-1 lower-bound construction is ready
for an informal proof and then Lean formalization.

#### Proof of Proposition L1

Let `n = 3k + 1`, `k >= 1`, and use the `U` pattern above. We prove that it
gives a spanning tree with

```text
|F| = n^2 - |U| = floor(n^2/3) + n - 1.
```

This is the diagonal formula for `n ≡ 1 (mod 3)`.

##### Count

There are `k` three-row blocks and one final bottom row. In each non-final
block the row counts are

```text
1, n-1, n-1,
```

and in the final block they are

```text
1, n-1, n.
```

The bottom row has count `0`. Hence

```text
|U| = (k-1)(1 + 2(n-1)) + (1 + (n-1) + n)
    = (k-1)(2n-1) + 2n
    = 6k^2 + k + 1.
```

Since `n = 3k + 1`,

```text
floor(n^2/3) + n - 1
= floor((9k^2 + 6k + 1)/3) + 3k + 1 - 1
= 3k^2 + 2k + 3k
= 3k^2 + 5k.
```

Also

```text
n^2 - |U| = (9k^2 + 6k + 1) - (6k^2 + k + 1)
          = 3k^2 + 5k.
```

So the count matches the conjectured lower bound.

##### Dual connectivity

Let `S = E(G[U])`. We show the dual edges `S*` connect every cell-face to the
exterior face.

For a dense row `r` whose `U` vertices are columns `1..n-1`, the horizontal
`U-U` edges in that row connect, in the dual, all cells immediately above row
`r` to the cells immediately below row `r`, from columns `1..n-2`, and the
rightmost horizontal edge connects the adjacent boundary cell to the exterior.
Thus each dense row creates a horizontal dual corridor from the right boundary
into the interior.

For two consecutive dense rows, their vertical `U-U` edges in columns
`1..n-1` connect adjacent cells within the strip, so the two row-corridors are
joined into one connected dual slab.

The sparse row immediately above each dense pair has a single `U` at column 1.
Its vertical `U-U` edge to the dense row below supplies the left-side bridge
needed to connect the next slab to the previous one. In the final block, the
third row is all `U`, so the left boundary also connects to the exterior. This
anchors the entire chain of slabs to both sides of the square.

More constructively, every cell lies in one of these three situations:

1. It touches a dense row corridor and reaches the right exterior through that
   corridor.
2. It lies between the two dense rows of a block and reaches that corridor by a
   vertical `U-U` dual edge.
3. It lies above a sparse row and reaches the next block through the column-1
   sparse bridge.

Inducting over the 3-row blocks from top to bottom connects all cell-faces to
the exterior face.

The checker shows that the number of dual edges is exactly the number of dual
vertices minus one:

```text
dual_edges = (n-1)^2 = dual_vertices - 1.
```

So once connected, the dual graph is a tree.

##### From dual connectivity to a tree

Assuming the planar-dual equivalence from the upper-bound program, dual
connectivity of `S*` implies `G - S` is a forest. But `G - S` is exactly the
forced-edge graph for `F = V \ U`. Therefore the forced edges are acyclic.

Finally, greedily add `U-U` edges connecting different components. Since the
original grid is connected, this completes the forced forest to a spanning tree.
No added edge touches `F`, so every vertex of `F` remains full-degree. This
produces a spanning tree with exactly `n^2 - |U|` full-degree vertices.

This proves Proposition L1 modulo formalizing the grid dual-connectivity
equivalence or replacing it by a direct acyclicity proof for the forced graph.

#### Lean formalization checklist for Proposition L1

1. Define `U_residue_one k : Set (GridVertex (3*k+1) (3*k+1))`.
2. Prove the cardinality formula `|U_residue_one k| = 6*k^2 + k + 1`.
3. Define the corresponding set `F = Uᶜ`.
4. Prove the forced graph `forcedEdgeGraph (gridGraph n n) F` is acyclic.
   The easiest path may be through the grid-dual theorem; a direct proof by
   describing connected components of the forced graph is an alternative.
5. Define explicit connector edges inside `U` or prove the greedy completion
   lemma: every forest subgraph of a connected graph can be extended to a
   spanning tree by adding edges outside the forest.
6. Conclude the tree has `n^2 - |U| = floor(n^2/3) + n - 1` full-degree
   vertices, since all edges incident to `F` are forced into the tree.

## Witness patterns to decode

The `fullub-witness` full-vertex sets for `n = 14, 15` have a clear
period-3 flavor: most rows contain full vertices in columns congruent to a
fixed class modulo 3, with dense full top/bottom boundary rows and residue
patches near the right edge.

The next proof task is to rewrite these witnesses in terms of the non-full
set `U`, because `U` is what the upper-bound theorem counts. Use

```bash
cargo run --release -- fullub-pattern n n
```

to print both the full-degree pattern `F` and the non-full pattern `U`
without dumping the completed spanning-tree edge list.

Example `U` witnesses currently produced by the parallel tie-breaking:

```text
n = 13, |U| = 101
.U...........
.UUUUUUUUUUUU
.UUUUUUUUUUUU
.U...........
.UUUUUUUUUUUU
.UUUUUUUUUUUU
.U...........
.UUUUUUUUUUUU
.UUUUUUUUUUUU
.U...........
.UUUUUUUUUUUU
UUUUUUUUUUUUU
.............

n = 14, |U| = 119
..............
UUUUUUUUUUUUUU
.UUUUUUUUUU.UU
.U........UUU.
.UUUUUUUUUUUU.
.UU.UU.UU..U.
.U.UUUUUUUUUU.
.UUUU.....UUU.
.UU.UUUUUUU.U.
.UU.UUUUUUUUU.
.UU.U......UU.
.UU.UUUUUUUUU.
.UUUUUUUUUUUU.
.U..........U.
```

These witnesses are not yet in a canonical closed form; `fullub` may return
different optimal witnesses depending on tie-breaking. The proof should seek a
simple parametric `U_n`, not merely encode one accidental optimal output.

Expected form:

```text
U_n = periodic 3-strip pattern + boundary patches depending on n mod 3.
```

Once `U_n` is explicit, prove:

1. `|U_n|` equals the formula above.
2. `G - E(G[U_n])` is a forest.
3. `G - E(G[U_n])` can be completed to a spanning tree by adding `U-U`
   edges.

## Near-term tasks

1. Extract the `U` patterns from `fullub-witness 13 13`, `14 14`, and
   `15 15` into a compact row/column modular description.
2. Attack the induced-edge decycling upper bound by strip counting or a
   planar-dual connectivity argument; local cell hitting is insufficient.
3. Prove the 3-strip lower-bound construction informally in this file.
4. Only after the strip proof is stable, move it into Lean.

## 2026-04-26 progress: skeleton constructions for residues 0 and 2

This section is a handoff note from a session focused on synthesizing
parametric residue-0 and residue-2 patterns. The session produced **partial**
parametric constructions ("skeletons") that are forest-completable and
dual-connected by construction but overshoot the conjectured `q(n)` by a small
`O(k)` correction. The session also produced new tooling (`construction_lab.py`,
`tile_alphabet.py`, `search_residue.py`) that will accelerate the remaining
work.

### Key new structural observations

1. **Optimal dual edge counts differ by residue.** For optimal `U` witnesses:
   - Residue 1: `dual_edges = (n-1)^2` exactly. The dual face graph is a
     spanning tree of all faces + OUT.
   - Residues 0 and 2: `dual_edges = (n-1)^2 + 1`. The dual is connected with
     exactly **one** cycle. Verified at the cached witnesses `n = 12, 14, 15`.

   This means residue-0 and residue-2 optimal patterns must have *one
   unavoidable redundant U-U edge* relative to a tree. Any clean construction
   that aims for the exact optimum must arrange this single extra dual edge.

2. **The cached residue-0 / residue-2 witnesses are non-canonical.** Examining
   `data/diagonal_u_{12,14,15}.txt`:
   - n=12 row counts `1,11,10,4,10,8,5,10,6,9,11,1` and strip totals
     `21,21,22,22` are highly irregular.
   - n=14 has clean residue-1-style top/bottom anchor rows (`.UUUU...UU`)
     with irregular column-stripe-like middle.
   - n=15 transposes to a near-residue-1 top/bottom plus column-stripe
     middle.

   These are tie-breaking artifacts. A clean parametric construction is not
   yet derivable directly from any single cached witness.

3. **The "skeleton" parametric pattern has the right structural shape.**
   Defined in `analysis/diagonal_patterns.py` as `residue_zero_pattern` and
   `residue_two_pattern`:
   - Top sandwich: `.U....`, `.UUUUUUUU` (residue-1-style top anchor).
   - Middle: column stripes `.UU.UU.UU....`.
   - Bottom sandwich: dense + sparse (residue-1-style bottom anchor).
   - Inter-strip bridges: single U cells at row 2 between stripe blocks
     (and right-boundary OUT anchor for residue 2).

   The skeleton is **forest+dual valid by construction** for every relevant `n`
   (verified by `construction_lab.py` for n in `{5,8,11,14}` and `{6,9,12,15}`),
   but overshoots `q(n)` by:
   - **Residue 2 (`n = 3k+2`): excess `= k`.**
   - **Residue 0 (`n = 3k`): excess `= 2k - 3`** (for k >= 2).

   Concretely, for n=5 the skeleton matches `q(5) = 14` exactly. For larger n
   it does not.

### What blocked the construction

1. Greedy local removal from the skeleton fails: the only safely-removable
   single cells are along one boundary column (n-1), and the maximum
   simultaneous removal saturates well below the required `O(k)` deficit.
2. Random simulated annealing from `v7` (residue-1-style at n=3k) successfully
   produced valid `q(n)` patterns at n=6 and n=9 within seconds, but n=12
   exceeded a 5 minute budget. The SA outputs are also irregular and do not
   suggest a clean parametric form.
3. Multiple analytic attempts (cropped residue-1, transposed residue-1,
   alternating-side sparse rows, two-sided sparse rows, alternating bridges)
   all hit the same "dual disconnects when count saturates" wall.

### Hypothesis for the remaining gap

The structural piece missing for residues 0 and 2 is an **extension layer**: a
single periodic patch that absorbs the `O(k)` excess from the skeleton while
preserving forest+dual validity. The patch must consume one extra dual edge
per "redundancy unit" — directly matching the `dual_edges = (n-1)^2 + 1`
observation.

For residue 2 the excess is exactly `k`, hinting at *one removable cell per
F-column gap*. The bridges at row 2 are the obvious candidates, but the brute
naive removal disconnects the dual. The patch likely shifts the bridge into
a "double-jog" that economizes by 1 U per gap.

For residue 0 the excess `2k - 3` is more complicated. It is *almost* `2(k-1)`,
suggesting a per-strip saving of 2 with one corner-correction `+1`. The
inductive route from n=3k to n=3(k+1) (with cost increment `12k+3`) might be
the cleanest.

### Tooling produced this session

- `analysis/construction_lab.py` — single-file checker for any candidate
  pattern. Produces `(u_count, expected_u, dual_ok, forest_ok)` per call.
  This replaces ad-hoc snippets and is the canonical way to validate a
  candidate generator.
- `analysis/tile_alphabet.py` — named tile alphabet (S, C, C', B, B', K) with
  per-tile U-counts and N/S/E/W edge signatures, derived from
  `tile_symmetry.py` outputs on cached witnesses. Foundation for any
  tile-grammar synthesis approach.
- `analysis/search_residue.py` — random/constrained local search; useful for
  generating spot-check witnesses at small n and for verifying the structural
  hypothesis.
- `analysis/diagonal_patterns.py` (rewritten) — `residue_one_pattern`,
  `residue_two_pattern`, `residue_zero_pattern`, plus the skeleton variants.
  The status registries `STATUS_RESIDUE_*` flag which n are verified.

### Recommended next steps for the next agent

1. **Find the residue-2 extension patch first** (k = 1 already exact;
   k = 2 deficit 2; k = 3 deficit 3). Two route ideas:
   - Replace the row-2 bridge `(2, 3t)` for some t with a *staircase*
     bridge that consumes 1 fewer U per step. Try `(2, 3t), (3, 3t+1)` as a
     double-cell move replacing the single bridge plus one stripe cell.
   - Use the cached n=14 witness as a reference for the EXACT placement and
     reverse-engineer the patch rule.

2. **Once residue 2 is parametric, attack residue 0** using the same patch
   plus an additional adjustment (since the residue-0 pattern has different
   right-boundary handling). Note that residue 0's excess `2k-3` is almost
   exactly `2(k-1)`, suggesting a per-strip saving plus one boundary unit.

3. **Avoid SA at large n.** The pattern doesn't appear to factor through SA
   solutions cleanly. Stick to hand-design with `construction_lab.py` checks.

4. **Do not push n > 15 empirically.** Prior runs of `fullub-pattern` are
   cached in `data/diagonal_u_{12..15}.txt`; the construction problem is now
   purely combinatorial.

### Files to read for context

- `analysis/diagonal_patterns.py` — current skeleton constructions.
- `analysis/construction_lab.py` — primary verification tool.
- `analysis/check_diagonal_patterns.py` — currently only validates residue 1.
  Extend to dispatch on `n mod 3` once residues 0 and 2 are parametric.
- `data/diagonal_u_*.txt` — cached witnesses.
- This file (`analysis/proofs_diagonal.md`) — the complete proof program.
