# Rectilinear cotree contour proof attempt

## Exact geometric model

Let `T` be a spanning tree of the `n x n` grid and put

```text
C = gridGraph n n \ T
U = supportFinset C
F = univ \ U.
```

In the plane dual, the edges crossing `C` form the cotree dual spanning tree.
Its finite vertices are the `(n-1)^2` cells and its outer vertex identifies all
perimeter ports.  For geometric arguments the outer vertex should be split back
into its individual perimeter ports; otherwise unrelated boundary contacts look
like incidences at one high-degree vertex.

At a primal vertex `v`, write `c(v) = C.degree v`, `t(v) = T.degree v`, and
`g(v) = (gridGraph n n).degree v`.  The proved local identity in
`ContourWaste.lean` is

```text
3 - c(v) = (4 - g(v)) + (t(v) - 1).
```

Thus `W` is not ordinary curvature at the vertices of the dual tree.  It counts
exterior grid sectors at supported primal vertices and all but one primal-tree
contour visit at each supported primal vertex.  `GeometricContourMarks.lean`
realizes the latter visits as `GridDirectionalDart`s.

The choice of the one unmarked visit at each vertex is arbitrary.  Consequently
a sweep or turning proof should not try to recognize the existing chosen
`baseSourceDart` geometrically.  A base-independent form is already supplied by
`PrimalContourLedger.lean`:

```text
W + 1 = B(U) + I_T(U) + kappa(F),
```

where

```text
B(U)     = boundaryDeficiencySum n n U
         = the number of incidences of U with the four sides,
I_T(U)   = (internalEdgeFinset T U).card,
kappa(F) = the number of connected components of gridGraph[F].
```

Corners occur twice in `B(U)`, exactly as two exterior sectors.  Every grid
edge incident with `F` is in `T`, so the components counted by `kappa(F)` are
also the preserved pieces of the primal tree.

## Precise rectilinear theorem

The desired universal bound is equivalent to the following static geometric
statement.

> **Rectilinear support sweep theorem.** For `n >= 3` and every spanning tree
> `T` of the `n x n` grid, with `U` and `F` as above,
>
> ```text
> n + 3 <= B(U) + I_T(U) + kappa(F).
> ```

Equivalently, there is an injection from `Fin (n+3)` into the disjoint union of

```text
four-side incidences of U
+ primal-tree edges internal to U
+ connected components of F.
```

The extra `3`, rather than `2`, is forced by the exact global `W+1` ledger.  A
proof of this statement and `cotree_incidenceWaste_add_one_eq_boundary_add_internal_add_components`
immediately gives `n+2 <= incidenceWaste C`.  Conversely, that waste bound
implies the displayed inequality, so this is an exact reformulation rather than
a stronger conjecture.

This is a better sweep target than an injection directly into
`GeometricCotreeContourMark`:

* it has no arbitrary local base dart;
* side contacts, transitions through `U`, and preserved carriers are separate;
* by `StraightForcedComponents.lean`, every nontrivial connected preserved
  piece is a horizontal or vertical interval;
* a horizontal or vertical sweep can therefore charge an interval once, charge
  a change between carriers to an internal `U-U` tree edge, and charge escape
  at the square boundary to a side incidence.

The missing local-to-global step is an injective lane rule proving that these
three alternatives cover `n+3` lanes.  In particular it must control reuse of a
vertical preserved interval by many horizontal cuts (and symmetrically for a
horizontal interval).  Merely knowing that preserved components are straight
does not yet provide that congestion bound; isolated preserved vertices may
also have several incident tree directions.

## Why the direct candidates do not close

### Horizontal and vertical cuts

Dual connectivity guarantees a cotree-dual edge across every nontrivial cut of
the cell columns or rows.  These crossing edges are distinct for distinct cut
positions, but crossing edges are not contour marks.  An interior supported
vertex with `C.degree v = 3` has local waste zero and can be an endpoint of
several such edges.  Following its unique primal-tree edge only moves the
charge: several lanes may subsequently meet the same preserved component.
The exact resource needed at that meeting is the single `kappa(F)` term, so an
additional no-reuse or interval-amortization lemma is essential.

### Extrema and turning number

After splitting the outer dual vertex into perimeter ports, a regular
neighborhood of the rectilinear dual tree has a closed orthogonal boundary.
Its signed turning number is the constant four.  This cannot itself yield a
quantity growing with `n`.  Absolute turns do grow for some trees, but they
occur at dual-face vertices, whereas `W` is evaluated around primal grid
vertices.  There is no local equality between a dual turn and
`3 - C.degree v`; straight dual passages and branching passages can both meet
zero-waste primal vertices.  A curvature proof would therefore still need the
same global assignment to side incidences, internal `U-U` tree edges, or
preserved components.

### One mark per diagonal or strip

Every unit cell has a cotree edge on its boundary, as proved by
`grid_tree_cotree_support_hits_cell_edge`.  Selecting one such edge in each
diagonal or strip does not select a mark: both endpoints can have zero local
waste.  Routing from these endpoints through `T` can coalesce, and counting the
first coalescence is invalid when it lies in a preserved component, since that
component contributes only one unit globally.  A valid diagonal theorem must
therefore be stated in terms of the three base-independent resources above and
must prove bounded congestion, not merely cell coverage.

## Most tractable next lemma

The useful intermediate statement is a one-dimensional interval-amortization
lemma.  In informal form:

> For one sweep direction, assign each lane either to its first side incidence,
> its first `T` edge with both endpoints in `U`, or the preserved component that
> carries it straight across the sweep.  Across all lanes, repeated assignment
> to one preserved component forces distinct intervening internal `U-U` tree
> edges or distinct endpoint side incidences.

To reach `n+3`, this must be combined with the opposite sweep and four extreme
side sectors.  The hard clause is the stated repeated-carrier implication.
It is local to a static tree and a family of ordered intervals; unlike
three-frame crop repair, it does not require constructing replacement vertices,
maintaining acyclicity during surgery, or re-proving dual connectivity after a
crop.  This makes it a more plausible theorem to formalize once its exact lane
ordering and endpoint conventions are fixed.

No complete injection was obtained in this attempt, so no new Lean theorem is
asserted.

## Forest-quotient interval amortization

The suggested contraction does give a precise one-carrier inequality, but it
also exposes an uncharged case.  Contract every component of `G_n[F]` in `T`
to one vertex and leave every vertex of `U` uncontracted.  Call the resulting
graph `Q`.  Its vertices have the two types

```text
F-components,                 individual U vertices,
```

and its edges have the two types

```text
F-U attachments,              T edges internal to U.
```

There are no edges between distinct `F` components.  Also, there cannot be two
parallel attachments from one `u in U` to one `F` component: the two
attachments together with the path inside that component would be a cycle in
`T`.

**Lemma (contracted tree).** `Q` is a tree.

**Proof.** Contracting connected subgraphs preserves connectedness.  A cycle
in `Q`, including a parallel-edge cycle, lifts by inserting paths inside the
contracted components to a cycle in `T`.  Thus `Q` is connected and acyclic.
QED

Fix an `F` component `C`.  An attachment branch of `C` is the component of
`Q-C` containing the `U` endpoint of an edge incident with `C`.  Different
attachments give different branches.  Indeed, a path in `Q-C` between two
such endpoints, together with their two attachment edges, would be a cycle in
`Q`.

Call an attachment branch *bare* when it consists of one interior `U` vertex.
Let `ell(C)` be the number of bare attachment branches.  Every non-bare branch
contains at least one of the following resources:

```text
a side incidence of a U vertex,
a T edge with both endpoints in U,
an F-component vertex different from C.
```

To see this, suppose that a branch contains none of them.  Its first vertex is
an interior `U` vertex.  With no internal `U-U` edge and no other
`F`-component vertex, it has no edge in `Q-C`, so the branch is precisely that
one vertex and is bare.  Choosing one resource in each non-bare branch is
injective because the branches are vertex- and edge-disjoint.  Consequently

```text
deg_Q(C) - ell(C) <= B(U) + I_T(U) + c_F - 1.          (A)
```

This is the unconditional forest-quotient amortization supplied by
acyclicity.

Now use the interval theorems.  If `C` is a nontrivial horizontal component,
its vertices form an interval in one row.  Every vertical grid neighbor of a
vertex of `C` lies in `U`: if it lay in `F`, its forced edge to `C` would put it
in the same component, contradicting straightness.  Since vertices of `F`
preserve all incident grid edges, each such vertical edge is an attachment in
`Q`.  Thus, writing `|C|` for the interval length and `r` for its row,

```text
tau(C) = |C| * (1_[r>0] + 1_[r<n-1]) <= deg_Q(C).
```

The vertical statement is symmetric:

```text
tau(C) = |C| * (1_[c>0] + 1_[c<n-1]) <= deg_Q(C).
```

Combining either formula with `(A)` gives the explicit one-component
interval-amortization inequality

```text
tau(C) - ell(C) <= B(U) + I_T(U) + c_F - 1.           (IA)
```

Singleton components have no intrinsic orientation and must be handled as
junctions, not declared horizontal or vertical arbitrarily.

### Why this does not prove the target

The term `ell(C)` cannot simply be deleted.  A bare branch is an interior
vertex `u in U` whose only edge in the contracted tree is its attachment to
`C`.  Equivalently, `u` is a leaf of `T`, all its other grid neighbors lie in
`U`, and all the corresponding grid edges are omitted from `T`.  It contributes
no side incidence, no internal `U-U` tree edge, and no additional `F`
component.  Consecutive transverse positions along a horizontal interval can
locally have this form without creating a primal cycle: the omitted edges
between and beyond those leaves belong to the cotree, not to the resource set
in `(IA)`.

There is a second obstruction to summing `(IA)`.  Although branches belonging
to one fixed carrier are disjoint, a resource selected from a branch of `C`
can lie in a branch of many other carriers.  A global sum therefore needs a
bounded-congestion rule in addition to the one-carrier injection.

Jordan separation does prove the distinct-branch assertion above, but it does
not charge a bare branch: a tree arc ending at an interior leaf is not a
crosscut and separates no region.  To finish the proposed strategy one would
need a new lemma that either

1. assigns every bare transverse leaf injectively, or with controlled total
   congestion, to a resource elsewhere in `Q`; or
2. couples horizontal and vertical carriers so that bare leaves in one sweep
   force distinct resources in the other sweep.

After summation such a lemma would have to leave at least `n+3` units.  By the
exact primal ledger this conclusion is equivalent to
`incidenceWaste (gridGraph n n \ T) >= n+2`, so asserting that total capacity
without the localization just described would be circular.  The existing
straightness and interval theorems prove `(IA)`, but not the required global
bound.

## Zero-waste continuation and the merger obstruction

The local continuation picture at a bare branch is exact.  Let `u` be an
interior vertex of `U` with `deg_T(u)=1`.  Since `U` is the support of the
cotree, all three other incident grid edges are cotree edges and

```text
deg_C(u)=3,                 3-deg_C(u)=0.
```

The four cells around `u` form a cyclic order.  Deleting the one dual edge
corresponding to the unique tree edge leaves the other three dual edges as a
length-three path.  Its endpoints are the two faces incident with the tree
edge.  Thus there is a canonical local bypass around `u`, and traversing it
uses no local contour mark.

This local bypass does not give nonmerging channels.  The obstruction already
occurs for two horizontally adjacent interior vertices `u` and `v`.  Delete
them from a sufficiently large square grid, choose a spanning tree of the
remaining connected grid, and add the north edge at each of `u` and `v`.
Then both are interior leaves of `T`, and their common horizontal edge is
omitted.  The two canonical three-edge dual bypasses both contain the dual of
that common edge.  More explicitly, if the four faces around `u` are

```text
NW(u), NE(u), SE(u), SW(u),
```

then the bypass at `u` is

```text
NW(u)--SW(u)--SE(u)--NE(u),
```

while the west edge of the bypass at `v` is the same dual edge as
`SE(u)--NE(u)`.  Their union branches but contains no dual cycle.  Hence
cotree-dual acyclicity does not prohibit this merger.

Rooted-shore port paths do not remove the obstruction.  In a rooted tree,
root-directed paths can share a terminal segment; their corresponding shores
are nested.  This is allowed, rather than forbidden, by
`targetShoreVertices_laminar`.  The port-path theorem identifies all shores on
such a shared path, and therefore also records the congestion instead of
bounding it.  This agrees with the general warning that one cotree-edge label
may occur on every fundamental shore along a long tree path.

There is also no unconditional termination proof for the unoriented local
rule.  Passing from `u` to `v` across their common omitted edge and applying
the same rule at `v` permits immediate return across that edge.  Orienting the
dual tree toward a root removes immediate backtracking and guarantees eventual
arrival at the root or a chosen stopping set, but at a rooted branch two
incoming channels may then share the parent edge.  Termination and injectivity
therefore trade places; dual-tree acyclicity alone does not provide both.

Consequently the proposed continuation rule cannot yield an injection of the
`n+3` canonical demands into terminal marks.  A valid continuation theorem
needs an additional capacity at mergers (charged to distinct internal `U-U`
tree edges, boundary sectors, or full components), or a demand-specific
noninterlacing invariant strong enough to show that the adjacent-leaf merger
is never simultaneously used.  Neither follows from cotree support,
port-path convexity, or rooted-shore laminarity.  No terminal-mark theorem is
asserted.
