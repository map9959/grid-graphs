# L2: Fixed-Rail Bottom Pocket

**Status: paper argument, not a Lean theorem.** The construction definitions
and lemma statements cited below were checked against the current source.
The arbitrary-repacking classification and sharp local upper bound in this
note are not formalized. No build, axiom audit, or optimization search was run
for this note.

## Exact Fixed Geometry

Use ambient zero-based `(row,column)` coordinates. Fix an integer `s >= 2`,
put `h = 3s` and `n = h+5`, and work on `{0,...,h+4}^2`. The deep square is
`D = [2,h+2]^2`. Thus the two rows below are the bottom two rows of **D**, not
the bottom two rows of the ambient board. In residue-two notation, `k=s+1`.
All intervals in this note are inclusive integer intervals.

Keep exactly the following preserved centers fixed:

```text
Fouter = ambient boundary minus
         {(0,1), (0,2), (1,h+4), (h+4,h+3), (h+3,0)};
z      = (2,2);
R_j    = {(3j+3,c) : j+4 <= c <= h+2},   0 <= j <= s-1;
L_j    = {(3j+5,c) : 2 <= c <= j+3},     0 <= j <= s-2.

F0 = Fouter union {z} union all R_j union all L_j.
Q  = {(r,c) : r in {h+1,h+2}, 2 <= c <= h+2}.
```

The free variable is an arbitrary subset `X` of `Q`, and the candidate is
`F0 union X`. In particular, first remove **all** of the construction's `B`
and `P` singleton centers. No fixed rail is shortened, translated, removed,
or supplemented outside `Q`. No boundary center or boundary hole changes.

Write `H(F)` for the graph on **all** ambient vertices containing every grid
edge with at least one endpoint in `F`. Feasibility means that `H(F)` is a
forest. A support is the set of vertices incident to an edge, not the set of
preserved centers, and is not automatically an induced grid subgraph.

## Verified Source References

Paths here are relative to `lean/GridGraphs/`. Namespace abbreviations in
the table are `BF = GridGraphs.BoundaryFiveFrame`,
`BC = GridGraphs.BoundaryFiveConstruction`, and
`RS = GridGraphs.ResidueTwoStaircase`.

| Source | Definitions or lemmas actually used |
| --- | --- |
| `Constructions/BoundaryFive/BoundaryFiveFrame.lean` | `BF.BoundaryHole`, `BF.Fouter`, `BF.Houter`, `BF.mem_support_iff`, `BF.support_eq`, `BF.spoke_iff`, `BF.nextRing_unique_neighbor`, `BF.support_isTree` |
| `Constructions/BoundaryFive/BoundaryFiveConstruction.lean` | `BC.Deep`, `BC.J`, `BC.Ffull`, `BC.forcedEdgeGraph_Ffull`, `BC.Fouter_card`, `BC.Ffull_card` |
| `Constructions/ResidueTwo/ResidueTwoStaircase.lean` | `RS.z`, `RS.R`, `RS.L`, `RS.B`, `RS.P`, `RS.baseline_card`, `RS.added_count`, `RS.A_card` |
| `Constructions/ResidueTwo/ResidueTwoStaircaseForest.lean` | `RS.Footprint`, `RS.interval_support`, `RS.piece_support_subset`, `RS.base_footprints_disjoint`, `RS.base_frame_inter`, `RS.base_family_isAcyclic`, `RS.P_footprint_inter`, `RS.P_frame_disjoint`, `RS.Ffull_isAcyclic`, `RS.Ffull_card`, `RS.stable_target_eq_staircase_add_gap` |

Important qualifications: `interval_support` and `piece_support_subset` are
one-way support inclusions. `base_frame_inter` asserts a **subsingleton**
intersection, not existence of an attachment. `base_family_isAcyclic` proves
acyclicity, not connectivity. `IsBase` in that file includes the predefined
`B` pieces as well as `z,R,L`; here we select only `z,R,L`. The `P` lemmas
apply to the predefined arithmetic progression, not every center allowed
below. The additional geometric arguments are given explicitly next.

## The Main Tree And Its Exact Support

Let `H0 = H(F0)` and `M = support(H0)`. Then `H0` restricted to `M` is one
tree, and every vertex outside `M` is an isolated vertex of `H0`.

To prove this, start with `BF.support_isTree` (its hypothesis `n >= 7` holds).
The frame support is exactly the outer boundary and next ring, except
`w=(1,2)`, by `BF.mem_support_iff`. For a nonempty horizontal interval of
centers `(r,a),...,(r,b)` here, its forced graph is the horizontal path on
row `r`, columns `a-1,...,b+1`, with a pendant vertex `(r-1,c)` and `(r+1,c)`
for each `a <= c <= b`. It is connected and has exactly the cross-shaped
support `RS.Footprint r a b`. The cited inclusion proves one direction;
the reverse follows because every listed off-row or endpoint vertex has an
edge to a center, and every center has a vertical incident edge. All these
coordinates are on the ambient board, including for the singleton `z`.

The supports of distinct `z,R,L` pieces are disjoint by
`RS.base_footprints_disjoint`. Their intersections with frame support are
exactly the following single vertices:

```text
piece       intersection with frame support
{z}         (2,1)
R_j         (3j+3,h+3)
L_j         (3j+5,1)
```

For uniqueness use `RS.base_frame_inter`. For existence, each displayed
vertex is a next-ring vertex other than `w` and is adjacent to the relevant
endpoint center. Hence it belongs both to the frame support and to the
piece support. In particular, the other outward neighbor `(1,2)` of `z`
is **not** a second frame attachment: it is `w`, initially isolated, and
becomes a leaf of the `z` star. Gluing these connected interval trees at
their single frame vertices proves connectivity and acyclicity on `M`.
Acyclicity is also an instance of `RS.base_family_isAcyclic` and the graph
union identity `BC.forcedEdgeGraph_Ffull`.

This gives a global exact description: `M` is the union of the frame support
and the exact footprints of `z,R,L`. For the pocket, its relevant slices are
as follows, **restricted to columns `1,...,h+3`**:

| Row | Columns in `M` |
| --- | --- |
| `h` | `[1,h+3]` |
| `h+1` | `{1} union [s+3,h+3]` |
| `h+2` | `{1,h+3}` |
| `h+3` | `[1,h+3]` |

Indeed the last left rail is `L_(s-2) = {(h-1,c): 2 <= c <= s+1}`;
its lower leaves occupy row `h`, columns `2,...,s+1`. The last right rail
is `R_(s-1) = {(h,c): s+3 <= c <= h+2}`; its left endpoint leaf is
`(h,s+2)` and its lower leaves occupy row `h+1`, columns `s+3,...,h+2`.
Earlier rails and `z` do not reach these rows. The remaining entries follow
from the exact frame support.

Do not infer that consecutive support vertices have a forced edge between
them: for example, `(h,s+1)--(h,s+2)` is **not** an edge of `H0`. Both
endpoints are unpreserved. Their connection in the main tree runs through
the rails and frame, not across that apparent seam.

## Allowable Individual Centers

Define upper-row and lower-row candidate centers by

```text
p_c = (h+1,c),    3 <= c <= s+1;
b_c = (h+2,c),    3 <= c <= s+2.
```

These, and only these, can occur in any feasible `X subset Q`.

For the positive direction, the slice table shows that each listed center
is initially isolated. Its four-neighbor star meets `M` exactly once:

```text
center       unique attachment to M       other vertices of its star
p_c          (h,c)                       (h+1,c), (h+1,c-1), (h+1,c+1), (h+2,c)
b_c          (h+3,c)                     (h+2,c), (h+2,c-1), (h+2,c+1), (h+1,c)
```

All four vertices in the last column are outside `M`. Thus each star alone
is a tree glued once to the main tree. The upper attachment `(h,c)` is an
**unpreserved lower leaf** of the last left rail: the preserved rail vertex
is `(h-1,c)`. Treating `(h,c)` as a preserved center would misstate the
geometry. The allowable upper range includes `c=s+1`, although the checked
`P` progression starts at `c=s`; individual legality is not the same as
compatibility with the checked `B` centers.

For exclusion of all remaining columns of `Q`:

1. `p_2` has two distinct neighbors `(h,2)` and `(h+1,1)` in `M`.
   `p_(s+2)` has two distinct neighbors `(h,s+2)` and `(h+1,s+3)` in `M`.
   Each center is outside `M`, so its two new edges close a cycle through
   the existing tree path between those neighbors.
2. For `s+3 <= c <= h+2`, `p_c` is already a lower leaf of the last right
   rail. Choose an adjacent rail column `d` in `[s+3,h+2]`, which exists
   since that rail has length `2s >= 4`. Preserving `p_c` forces the fourth
   edge of the unit square with vertices `(h,c),(h,d),p_d,p_c`; the other
   three edges were already forced by the rail. This is a cycle, even
   though the edge upward from `p_c` was present before insertion.
3. `b_2` has distinct neighbors `(h+2,1)` and `(h+3,2)` in `M`.
   Every `b_c` with `s+3 <= c <= h+2` has both `(h+1,c)` and `(h+3,c)`
   in `M`. These centers are outside `M`, so again two new edges close a
   cycle through the main tree.

Adding other centers cannot remove any such cycle. This exclusion does
not incorrectly apply an isolated-center insertion test to the `p_c`
vertices that are already in the rail support.

## Exact Spacing Criterion

For subsets `P subset [3,s+1]` and `B subset [3,s+2]`, put
`X = {p_c : c in P} union {b_c : c in B}`. Then, at paper level,

```text
H(F0 union X) is a forest
  iff
  |c-d| >= 3 for distinct c,d in P,
  |c-d| >= 3 for distinct c,d in B,
  |c-d| >= 2 for c in P and d in B.
```

**Necessity.** Every allowed star has its own attachment vertex in `M`,
and these attachment vertices are distinct, including across the two rows.
On one row, centers at column distance one are adjacent; their stars give
a path between their attachments with interior outside `M`. At distance
two, the stars share the intervening horizontal neighbor and give such a
path as well. Either path and the unique path in the main tree form a cycle.
Across the rows, equal-column centers are adjacent. At column distance one
their stars share the two other corners of the unit square. Again there
is a path outside `M` between their distinct attachments (and in the latter
case the unit square itself is forced). These are exactly the forbidden
spacing cases. This proves necessity for arbitrary sets, not merely for
an insertion order.

**Sufficiency.** The full support of an allowed star is the center and its
four grid neighbors. Under the stated inequalities, centers in the same
row have Manhattan distance at least three, and centers in different rows
also have Manhattan distance at least three. Their radius-one supports are
therefore pairwise disjoint. Each star meets `M` at precisely its one listed
attachment. Consequently all stars can be glued to the main tree, one at
a time, at a single vertex each. The resulting nonisolated graph is a tree;
all untouched vertices remain isolated. This accounts for all forced edges,
because `H(F0 union X)` is exactly `H0` union the stars of the selected
centers. No additional edge is forced merely because two support vertices
are grid-adjacent.

## Sharp Count

The spacing criterion implies that selected columns are distinct integers
in `[3,s+2]`, with successive differences at least two. This interval has
`s` columns. If there are `q >= 1` centers, then

```text
3 + 2(q-1) <= s+2,
q <= floor((s+1)/2) = ceil(s/2).
```

The empty case satisfies the same bound. Moreover, a gap of exactly two
between successive selected columns requires alternating rows; a same-row
gap must be at least three. The bound is attained by the actual source
progressions:

```text
B: b_(s+2-4t),    0 <= t < floor((s+3)/4);
P: p_(s-4t),      0 <= t < floor((s+1)/4).
```

Read right to left, these use columns `s+2,s,s-2,s-4,...`, alternating
bottom and upper rows and stopping at column at least three. Same-row gaps
are four, cross-row gaps are at least two, and the endpoint ranges above
hold even for `s=2`. Their count is
`floor((s+3)/4)+floor((s+1)/4)=floor((s+1)/2)`, the identity
`RS.added_count`. The checked construction's feasibility is independently
provided by `RS.Ffull_isAcyclic`.

Thus the maximum number of pocket centers for this exact fixed geometry is
**`ceil(s/2)`**. `RS.baseline_card` gives `3s^2` fixed deep centers and
`BC.Fouter_card` gives `12s+11` boundary centers. The sharp score within
this class is therefore

```text
3s^2 + 12s + 11 + floor((s+1)/2)
  = 3k^2 + 6k + 2 + floor(k/2),    k=s+1 >= 3.
```

The existing `RS.Ffull_card` proves that score for the displayed family;
it does not prove the new local upper bound over arbitrary repackings.

As a consistency check, each legal insertion merges the component of its
isolated center, three other isolated vertices, and the main component
into one: the full-vertex component count drops by **four**, not three.
Under the spacing criterion these vertices are not reused by other stars.
Each added center is an isolated induced preserved carrier, so the induced
carrier count rises by one. Boundary deficiency remains five. This is a
paper-level local accounting check, not a new uniform component formula.

## Scope And Remaining Gaps

This rules out gaining another center solely by repacking these two deep
rows while keeping `F0` exactly fixed. At side increased by six, the sharp
score for the same fixed-rail class increases by `12s+37 = 12k+25`, one
less than the target pump gain `12k+26`. In the stable range `k >= 5`, its
gap from `T(k)=3k^2+7k` is `floor((k-1)/2)-1`, as also expressed by
`RS.stable_target_eq_staircase_add_gap`.

This is **not** an impossibility theorem for L2, for other fixed supports,
for all boundary-five constructions, or for the conjectured optimum.
Moving or shortening rails, changing their frame attachments, editing
other rows, changing the boundary, or allowing a different component
partition can invalidate the premises. Rootless components are permitted
in the general problem; here every individually legal pocket star happens
to be rooted in `M`, as a conclusion of this specific geometry, not an
extra global feasibility requirement. No six-width closure invariant is
proved here.

Confidence is high in this local paper argument: all cited names and their
actual statement strengths were inspected, and the exact support and
attachment existence missing from the one-way source lemmas are proved
above. The remaining verification gap is formalization of the main-support
description and arbitrary-center necessity/sufficiency/count theorem.
Source inspection is not a fresh Lean check, and this note does not claim
one or promote the local argument to an unconditional global result.
