# Planar Dual Upper Research

Date: 2026-09-07. Paper deductions and precise limitations, not a proof of
the global constant-gap bound. No Lean changes, optimization, or finite-search
evidence. This investigation reads the half-coefficient and positive-loss
notes but uses a different planar description.

## Model And Objective

For the subsequent upper-only continuation, see
[Isolate Routing](PAPER_ISOLATE_ROUTING_UPPER.md),
[Global Cap Payment](PAPER_GLOBAL_CAP_PAYMENT.md), and
[Global Metric Upper Attempt](PAPER_GLOBAL_METRIC_UPPER.md).
The reviewed isolate allocation removes the isolate-count error relative
to its conservative clean certificate. Clean short-strand payment remains
open. The cap note records new constant-gap classes and an explicitly
withdrawn overbroad transfer; none makes the global bound unconditional.

Let G be the n by n grid in its usual plane embedding, F the preserved
vertices, U its complement, and H the spanning subgraph of edges incident to
F. Feasibility means H is a forest. Use the actual counts f, r, b, c from
PAPER_HALF_COEFFICIENT_UPPER.md, including isolated vertices in c.

For n=3k+2 and T=3k^2+7k the exact ledger is

```
3f+r+b+c=n^2+4n,
r+b+c=3k+12-3(f-T).
```

Consequently r+b+c >= n-C would give f-T <= (C+10)/3. The task is to
obtain such a metric estimate, not to rename this equality.

The deductions below identify the precise dual graph and its bends, prove
that ordinary connectedness of U is almost automatic, and develop an actual
short-side corridor estimate. The desired metric bound is proved when the
once-pruned dual has no junctions of the specified type. The continuation
also pays arbitrarily many junctions in the isolate-free,
pendant-bend-strand class, which includes the square comb. The unrestricted
case remains open; the boundary-interval term is essential.

## The Exact Dual

Let D have one vertex for every bounded unit face of G and one vertex o for
the exterior face. Include the dual of precisely the UU edges. Keep parallel
edges incident to o: for example, two boundary edges of a corner cell can
have the same pair of dual endpoints.

Then

```
H is a forest  <=>  D is connected.
```

One proof in the forward direction extends H to a spanning tree S of G.
The duals of the edges outside S form a dual spanning tree, contained in D.
Conversely a cycle in H separates faces on its two sides, and no edge of D
can cross it. This contradicts connectivity. This is a statement about the
full plane dual, including o, not about the graph induced on U.

For feasible F,

```
|V(D)|=(n-1)^2+1,
|E(D)|=2n(n-1)-(n^2-c)=n^2-2n+c,
cycle_rank(D)=c-1.                                  (1)
```

Thus dual connectivity is exactly feasibility, and the cycles left in this
connected dual already account for c. Counting these cycles again as an
independent reserve would double-count.

## Leaves, Bends, And Boundary Ports

Two diagonally opposite F vertices in a unit cell force its four-cycle.
Thus a cell contains zero, one, or two F vertices, and in the last case
they are adjacent and belong to the same carrier. It follows that every
non-exterior vertex of D is exactly one of:

* Degree four, when the cell contains no F vertex.
* Degree two with a right-angle turn, when it contains one F vertex.
* Degree one, when it contains an FF edge.

In particular there are no straight degree-two vertices and no degree-three
vertices in this full dual. These assertions need not survive pruning or
passing to a spanning tree of D.

Write X, M, L for the numbers of these degree-four, degree-two, and degree-one
vertices, respectively. Let B count F vertices on the boundary cycle, C_o
count F corners, a count boundary FF edges, and w count F intervals on that
cycle. The boundary cycle is not entirely F, so

```
a=B-w.
```

Let t=deg_D(o), the number of boundary UU edges. Counting the two transitions
of each F interval gives

```
t=4n-4-B-w=b+C_o-w-4.                              (2)
```

Every interior FF edge belongs to two cells and every boundary FF edge to
one. Since the carriers have f-r induced edges,

```
L=2(f-r)-a.                                        (3)
```

The number of cell-corner incidences with F is 4f-2B-C_o. A one-F cell
contributes one and a two-F cell contributes two. Therefore

```
M+2L=4f-2B-C_o,
M=4r-2w-C_o.                                      (4)
```

An interior rod, regardless of length, contributes four bends. An interior
singleton also contributes four, not zero. These bends can be assigned to
their unique F corner, so (4) is a physical count, not an orientation
convention for singletons.

The degree sum together with (1) gives exactly

```
L=2X+t+2-2c.                                      (5)
```

This is the full Euler discharging equation for degrees 1, 2, 4 and the
exterior vertex. In particular degree-two bends have zero Euler charge.
Substitution of (2)--(4) and X+M+L=(n-1)^2 recovers the original ledger;
it gives no additional inequality.

For reference, the desired quantity in geometric dual variables is

```
r+b+c=M/4+3w/2+t+c+4-3C_o/4.                       (6)
```

So a potential dual argument must genuinely constrain bends, boundary
intervals, ports, and cycle rank by the square's side length. Merely asserting
the corresponding lower bound on the right of (6) is the original target
again. No unrestricted such metric lemma is proved here.

## Primal Complement Faces

There is a stronger structural fact about G[U]. The following statements
need only the local no-diagonal-F condition, not global feasibility.
That condition already makes the carriers straight filled intervals.

Let r_I count carriers avoiding the boundary and let s count full straight
rods from one side of the board to the opposite side that are NOT wholly
in the boundary. Equivalently, these are full horizontal rows with row
coordinate 1,...,n-2, or full vertical columns with column coordinate
1,...,n-2. Full top/bottom rows and full left/right columns are excluded.
Then

```
number of components of G[U]=1+s.                  (7)
```

Here is a planar proof with the face accounting made explicit. An interior
horizontal carrier of length ell occupies ell consecutive vertices on one
row. Deleting it and its incident edges merges its incident unit cells into
one rectangle of width ell+1 and height 2. Its entire rectangular perimeter
is in U: a putative F vertex on the top or bottom side is adjacent or
diagonally adjacent to the carrier; the two remaining side midpoints would
extend the carrier. The same argument holds vertically. A singleton gives
a 2 by 2 rectangle.

No unit cell is incident to two different carriers: adjacent F vertices
belong to one carrier and diagonal F vertices are forbidden. Consequently
the open regions merged by deleting different interior carriers are
disjoint. Boundary-carrier deletions merge their incident cells with the
exterior instead. These observations show that the bounded faces of G[U]
are precisely:

* The X original cells with no F corner, still unit-square faces.
* One rectangular face for each of the r_I interior carriers.

Sharing U vertices or perimeter edges does not merge these open faces.

For an algebraic check and a proof of the component count, let q be the
number of components of G[U], without assuming H is a forest. Direct
edge counting gives

```
|E(G[U])|=2n^2+2n-3f-r-b,
|E(G[U])|-|U|=n^2+2n-2f-r-b.
```

Counting cells incident to F using (3), (4), and B+C_o=4n-b gives

```
X=(n-1)^2-M-L
 =n^2+2n+1-2f-2r-b+w.
```

Euler for the possibly disconnected plane graph G[U] says

```
X+r_I=|E(G[U])|-|U|+q,
q=1+w-r+r_I.
```

Each boundary carrier meets the boundary cycle in one interval, except a
nonpure full side-to-side rod, which meets it in two. A pure boundary rod,
including an entire boundary side or a rod through a corner, still gives
one interval. Hence
w=(r-r_I)+s, proving (7).

As a countercheck, preserving only the full top row has s=0 and leaves U
connected. Counting that pure boundary row in s would incorrectly give
two components. The original wording of s did include it and was wrong;
the correction is to the definition and the boundary-intersection step,
not to Euler's formula q=1+w-r+r_I.

This proves more than the assertion that every U component reaches the
boundary. In particular, in the absence of nonpure spanning rods, U is
connected automatically. Ordinary complement connectivity cannot then supply
a new global restriction beyond the local exclusion already in use.

## Singleton Countercheck

Connected U does not imply connected D, even with straight carriers and
all the unit-cell exclusions above. On any board containing coordinates
0 through 6, put

```
F={(2,2),(4,2),(2,4),(4,4)}.
```

These are four singleton carriers with no diagonal F pair in a unit cell.
There is no spanning rod, so (7) proves G[U] connected. But H contains the
eight-edge perimeter cycle of [2,4] by [2,4]: each successive perimeter
edge has one of the four displayed F corners as an endpoint.

In D the four cells inside that rectangle form a separate four-cycle.
Their vertices are all right-angle degree-two vertices. Thus the exact
missing condition is dual connectivity, not primal complement connectivity.
The example is deliberately infeasible; it refutes replacing feasibility
by connected U plus the local carrier conditions, not the proposed upper
bound for feasible sets.

## Long Rod Countercheck

A metric charge must not assign positive cost per unit length to every
straight dual corridor. There is an explicit family with arbitrarily long
corridors and constant bends, ports, and cycle rank in a thin rectangle.

Take a W by 4 grid, W>=3, and preserve its complete top and bottom rows.
Each row and its adjacent row of holes is a forced tree; the two supports
are disjoint and cover the board. Therefore

```
f=2W, r=2, c=2, b=4, r+b+c=8.
```

The dual consists of a spine of W-1 degree-four vertices, two leaves at
every spine vertex, and an edge from each end of the spine to o. There
are no bends; there are two exterior ports and cycle rank one. All of
these claims follow directly by listing the three rows of cells: top and
bottom cells are leaves, and middle cells contain no F corner.

Thus the spine length is unbounded while every endpoint/topological cost
stays constant. Deleting its leaves makes the formerly degree-four spine
straight degree two; suppressing that spine loses the entire length W-1.
A proof using the pruned core cannot silently retain the original
no-straight-degree-two property.

More generally on a W by (3s+1) rectangle, preserve full rows
0,3,...,3s, where s>=1. The disjoint forced-tree bands cover every vertex,
and

```
r=c=s+1, b=4s, r+b+c=6s+2=2(3s+1),
M=0, t=2s, cycle_rank(D)=s.
```

This refutes a bound by the long side or diameter with coefficient bounded
away from zero uniformly over rectangles. It does not refute a square
bound or a bound by the short side. Inside a square, the same double-comb
strip shows why a local length charge needs a separate global argument
for the region outside that strip. This is an analytic family, not finite
evidence.

## Once-Pruned Core Geometry

The remainder allows a W_0 by H_0 board, W_0,H_0>=11. Put

```
A=max(W_0-1,H_0-1), B=min(W_0-1,H_0-1), m=min(W_0,H_0)=B+1.
```

The cell array is A by B after a possible rotation. Definitions of D, M,
t, and c are unchanged; beta=cycle_rank(D)=c-1 still holds on rectangles.

Delete all degree-one cell vertices of D once, but retain o even if it has
degree one. Call the result C. It is connected and has cycle rank beta.
It dominates all cells in the augmented graph with exterior vertex o.
Without o its cell subgraph need not be connected, and a leaf attached
directly to o need not have a neighbouring core cell. Thus this is not
automatically a connected dominating set of the ordinary cell grid.

Keep the distinction between a bend-origin vertex (one of the original M)
and a crossing-origin vertex (one of the original X).

**Local lemma.** The following hold in the actual core C.

1. A crossing-origin vertex has at most two deleted leaf neighbours, and
   if it has two they are opposite. It therefore has core degree 2, 3, or 4;
   degree 2 is straight.
2. A bend-origin vertex has core degree 1 or 2. It has at most one deleted
   leaf neighbour; when its core degree is 2 it is still a right-angle bend.
3. A straight degree-two crossing-origin vertex cannot be adjacent in C
   to a bend-origin vertex.

For (1), place the crossing cell at [0,1]^2. A leaf to its north requires
F at (0,2),(1,2), since the shared side is UU and the opposite side must
be FF. A leaf to its east similarly requires F at (2,0),(2,1). But then
(1,2),(2,1) are diagonally opposite in a unit cell. Rotation proves all
perpendicular cases. Assertion (2) follows from connectivity: a bend with
two leaf neighbours would be an entire three-vertex component disjoint
from o.

For (3), suppose the crossing's core direction is horizontal. Its north
and south neighbours were leaves, requiring F at
(0,2),(1,2),(0,-1),(1,-1). A bend cell immediately west would have its F
corner at (-1,0) or (-1,1). These are forbidden by the diagonal pairs with
(0,-1) or (0,2), respectively. The east side and vertical orientation are
the same argument. All coordinates used are present whenever the relevant
cell neighbours exist; o is not a bend cell.

Thus a straight surviving corridor cannot simply turn into a bend cell.
It must first encounter a crossing-origin vertex of core degree 3 or 4.
These are genuine, locally forced transition sites, not arbitrarily marked
cuts of a rod.

There is also an exact carrier interpretation. A horizontal straight
crossing cell has horizontal FF edges in the two leaves above and below
it. Those edges lie on carrier rows three apart. Continuing a straight
run continues the common FF-edge interval of that same pair of carriers.
Conversely, overlapping FF-edge intervals of two horizontal carriers on
rows three apart give such a run: their intervening cell has four U
corners, and the cells above and below are leaves. The vertical statement
is identical. Thus the long parts of the core are overlap corridors of
actual parallel rods, not arbitrary links of a generic dominating tree.

## Corridor Capacity Theorem

Let J_3 and J_4 count crossing-origin vertices of core degree 3 and 4.
Call them junctions. All remaining crossing-origin vertices have degree 2
and are straight. By the local lemma, their neighbours are crossing-origin
vertices or o, never bend-origin vertices.

Make a multigraph R on o and the J_3+J_4 junctions. An edge of R is a
maximal core path whose internal vertices are straight crossing-origin
vertices and whose endpoints are junctions or o. Include direct
junction-junction and junction-o edges as paths with no internal vertex.
The paths with internal vertices are literal straight intervals; they
cannot form an endpoint-free cycle on a finite row or column. Distinct
paths have disjoint internal vertices and edges. Loops at o and parallel
edges are retained. Isolated junctions are also retained in R.

Write g=|E(R)|, t_R=deg_R(o), and let a_M count core edges from a junction
to a bend-origin vertex. Degree counting at the junctions gives

```
2g=t_R+3J_3+4J_4-a_M.
```

R is obtained by deleting edges/vertices and suppressing paths in C, so
its cycle rank is at most beta. Since R has J_3+J_4+1 vertices and at
least one component, including any isolates,

```
g <= J_3+J_4+beta,
3g <= t_R+beta+4J_3+5J_4-a_M.                       (8)
```

The next step is metric, not Euler counting. Trim the outermost row and
column of cells on each side, leaving (A-2)(B-2) cells. Every remaining
cell is assigned to itself if it belongs to C, and otherwise to its
unique neighbour in D. A deleted cell in this trimmed array cannot have
o as that neighbour.

The assignments can be counted as follows.

* Straight crossing-origin vertices on one R path and their assigned
  leaves lie in a strip of width three. The leaves are perpendicular to
  the straight path, by the local lemma. Inside the trimmed cell array
  this accounts for at most 3(A-2) cells per path, in either orientation.
* A bend-origin vertex accounts for itself and at most one leaf: at most
  2M cells in total.
* A degree-three junction accounts for itself and at most one leaf; a
  degree-four junction has no leaf neighbour. Their total is at most
  2J_3+J_4.

This is an exhaustive assignment of physical cells. Endpoint junctions
are counted in the last item, not as straight path interiors. Hence

```
(A-2)(B-2) <= 3(A-2)g+2M+2J_3+J_4.                (9)
```

Combining (8),(9), using beta=c-1 and m=B+1, proves the unconditional
rectangular metric inequality

```
m <= t_R+c+4J_3+5J_4-a_M
     +(2M+2J_3+J_4)/(A-2)+2.                       (10)
```

For A>=10, t_R<=t and 2/(A-2)<=1/4 give the convenient weaker version

```
m <= M/4+t+c+(17/4)J_3+(41/8)J_4-a_M+2.            (11)
```

These are actual short-side bounds. The essential non-ledger input is (9):
straight corridors have bounded length in a rectangle and can dominate
only width-three strips. Long thin corridors satisfy it, since it is the
short side, not the diameter, on the left.

## A Proved Metric Subclass

If J_3=J_4=0, (11) already gives a short-side bound with error two. In
fact the complete geometry gives the stronger theorem

```
M/4+t+c >= min(W_0,H_0).                            (12)
```

Here is a direct proof, valid when W_0,H_0>=9. Every crossing-origin vertex
is straight degree two and has only crossing-origin vertices or o as
core neighbours. Continuing in both directions therefore yields an entire
row or column of crossing cells. Such full lines cannot have both
orientations: an intersection would be a degree-four junction. Let q
count them, let ell be their common length, and let d be the transverse
cell-array dimension. If q=0 choose ell=A,d=B.

Each full line has two ports to o, forms an independent cycle with o,
and has a full row or column of leaves on each perpendicular side.
The line cannot lie in an outermost cell row/column, since the outward
edge to o would survive pruning. These width-three bands are disjoint:
a shared leaf would have two dual neighbours, contradicting its degree.
Thus they account for exactly 3ell*q cells and

```
t>=2q, c>=q+1, d>=3q.
```

All remaining cells are bends or leaves whose parent is a bend or o.
A bend accounts for itself and at most one leaf. Every leaf with parent
o uses its own port, distinct from the 2q line ports. Hence

```
ell(d-3q) <= 2M+t-2q.
```

These are physical coverage and independent-cycle statements. They imply

```
M/4+t+c
 >= ell(d-3q)/8+3q+1
  = d+1+(ell/8-1)(d-3q)
 >= d+1 >= min(W_0,H_0),
```

because ell>=8. This proves (12). It permits bends and singleton carriers;
it does not assume M=0 or assume the entire core is straight. Bend-only
parts can form complicated paths, but their coverage costs at most 2M.

On a square n>=11, (6) and C_o<=4 now give

```
r+b+c >= M/4+t+c+1 >= n+1.
```

For n=3k+2 this yields 3(f-T)<=9, hence f<=T+3, for every feasible set
whose once-pruned dual has no crossing-origin junctions. This is a proved
subclass theorem, not the unrestricted global upper bound.

There is even a residue-sensitive reserve in this subclass. Here
ell=d=n-1=3k+1 and d-3q>=1, so the displayed proof yields

```
M/4+t+c >= n+(n-9)/8,
f-T <= 3-(n-9)/24.
```

No integrality or finite-size evidence is being substituted for the
coverage proof. This extra reserve does not extend to configurations with
junctions by any argument in this note.

The subclass includes the full parallel-bar family on (3s+1)-high
rectangles from the earlier countercheck. There M=0, t=2s, c=s+1, so
t+c=3s+1 equals the short side whenever W>=3s+1. The theorem does not
mistakenly charge that family's long dimension. No classification by
packing loss Lambda is being assumed or asserted.

## Square Comb And The Essential Boundary Term

The stronger unrestricted proposal M/4+t+c >= min(W_0,H_0)-O(1), omitting w,
is false even on squares, not merely on long thin rectangles.

For any s>=1 take n=3s+1, and preserve precisely

```
F={(0,y): 0<=y<=3s}
  union {(x,3j): 2<=x<=3s, 0<=j<=s}.
```

The vertical boundary spine and its leaves occupy columns 0 and 1.
Each horizontal tooth and its vertical leaves occupy its own three-row
band in columns 2 through 3s, truncated to two rows at the top or bottom.
These bands partition those columns. The tooth's one additional endpoint
leaf (1,3j) is already a leaf of the spine, giving exactly one attachment
of that tooth tree to the spine tree. There are no other forced edges
between the supports. Thus H is one tree spanning the board, rigorously
for every s.

Direct counts are

```
f=n+(s+1)(n-2)=3s^2+5s,
r=s+2, c=1, b=2s+2,
C_o=4, w=s+2, M=2s, t=s.
```

For b, there is one top hole and one bottom hole at x=1, and the right
side has 2s holes; the left side has none. There are no corner holes.

Consequently

```
M/4+t+c=(3/2)s+1,
M/4+(3/2)w+t+c=3s+4=n+3,
r+b+c=n+4.                                        (13)
```

The missing w term would therefore cause an unbounded shortfall on a
square. This also prevents importing a purported generic grid-tree bend
theorem with the stronger coefficients: this D is itself a tree.
This counterexample uses n congruent to 1 modulo 3. It refutes the
unrestricted rectangular/square theorem without w, not a separately
restricted residue-two theorem and not the weighted target itself.

Here the junction obstruction in (10) is concrete. In each band there is
one degree-three junction, at the left end of the long horizontal core
corridor; its other two core neighbours are endpoint bends. Thus

```
J_3=s, J_4=0, a_M=2s, g=s, t_R=s, beta=0.
```

Equation (8) is sharp: 3g=t_R+4J_3-a_M=3s. Nevertheless replacing its
remaining 2s junction cost by an O(1) error is impossible. In this family
the available credit M/4+(3/2)w=2s+3 pays that cost at the correct leading
order. The boundary interval credit is geometrically relevant, not an
inessential reformulation.

## Contact And Bend Packet Accounting

The following continuation keeps all counts physical. Let z count isolated
vertices of H, necessarily in U. Let e_1 count bend-origin vertices of
core degree one. Split the original exterior degree as

```
t=t_R+t_M+t_0,  t_C=t_R+t_M,
```

where t_M counts exterior edges to bend-origin vertices and t_0 counts
exterior edges to the deleted leaf cells. Thus t_C is the exterior degree
in C. These are edge counts, including multiplicity at o.

Contract each preserved carrier in H and suppress every hole with two
preserved neighbours. Delete degree-one holes and isolated holes. The
result is an actual forest on r vertices. Call its edges contacts, and
write q_ct for their number. Its component count is c-z, so

```
q_ct=r-c+z.                                        (14)
```

For a contact hole u, let a(u) count FF edges at its two preserved
neighbours perpendicular to the contact axis. There is at most one such
edge on either perpendicular side: two on the same side force the
six-cycle around a width-two, height-one rectangle, after rotation.

Each such FF edge is in a leaf cell adjacent across a UU edge to a bend
cell. Conversely every leaf-bend edge comes from exactly one such contact
incidence. Consequently

```
e_1=sum_contacts a(u),
tau=2q_ct-e_1>=0.                                  (15)
```

There is a concrete description of tau. Let q_bd count contacts at holes
on the outer boundary. Such holes are not corners and have only one valid
perpendicular side. On each valid side of any contact, zero transverse
FF edges give a bend-bend dual edge; one gives a leaf-bend edge. The
two-FF case is forbidden. Let d_MM count these contact-type bend-bend
edges. Then, exactly,

```
tau=d_MM+q_bd.                                     (16)
```

In particular tau is not an arbitrary choice of lost contacts or a signed
surplus that has been truncated. It counts missing transverse incidences,
with the missing outside side of a boundary contact charged once.

The core degree sum gives

```
J_3+2J_4+t_C=e_1+2(c-1).
```

Combining this with (14),(15) pays the junction load by actual carrier
packets and isolates:

```
J_3+2J_4+t_C+tau
 =2r+2z-2
 =M/2+w+C_o/2+2z-2.                                (17)
```

This retains the contact loss tau, boundary intervals w, and actual
exterior ports together. It does not assert the desired metric theorem.

## Opposite-Corner Matching

Every bend cell has a unique F corner and an opposite U corner v. Its
two neighbours of v inside that cell are U. The remaining possible F
neighbours of v are perpendicular, so there is at most one of them.

If there is none, v is an isolated vertex of H. If there is one, the
cell adjacent in that direction is either a leaf or another bend. In the
second case the two F corners are a knight move apart, with coordinate
differences 1 and 2 in some order. The two bend cells point to each other
by this same opposite-corner rule. Thus these knight-type bend-bend edges
form a matching on the bends that they meet.

Write k_MM for their number and Z_M for the number of bends whose opposite
corner is an isolated hole. The preceding cases are disjoint and exhaustive:

```
M=e_1+2k_MM+Z_M.                                   (18)
```

This includes singletons and boundary cells. A singleton still has its
actual four-cell packet before boundary truncation. If the opposite corner
is on the boundary, missing grid neighbours simply cannot be F; they do
not create an additional case in (18).

Let Z_X count incidences of crossing-origin cells with isolated H vertices
at their corners. For a crossing cell v, every one of its four corners
has either zero or one F neighbour outside that cell. A neighbouring
leaf contributes two such incidences, a neighbouring bend one, and a
neighbouring crossing or exterior port none. Therefore

```
a_M+Z_X=2J_3+4J_4,
2g=t_R+J_3+Z_X.                                   (19)
```

In combination with (17), this is the exact contact-to-corridor formula

```
g=r+z-1-J_4+(Z_X-t_M-tau)/2.                       (20)
```

For z=0 it becomes

```
g+J_4+(t_M+tau)/2=r-1.                             (21)
```

Thus the raw four-/five-unit junction allowance from (10) is not intrinsic.
The contact forest and local corner incidences cancel much of it. Equation
(21) still does not pay three units per interior corridor, so it is not
being presented as closure of the metric problem.

## Bend Strands And Their Rank

The graph induced by the bend-origin vertices in C is a disjoint union of
paths, including isolated vertices. A cycle would use both incident edges
at every bend and be a component disjoint from o, contradicting connectivity.

Call o and the crossing-origin junctions anchors. Every bend path has one
or two edges to anchors: it cannot have none, and its degree bound allows
at most two. Straight crossing-origin vertices cannot be anchors of these
edges by the earlier local lemma. Let P count the paths with two anchor
edges, with multiplicity if both go to the same anchor. These are the
through strands. The one-anchor paths are pendant strands. There are
exactly e_1 pendant strands, each with one true core endpoint.

Since all bend-bend edges are contact-type or knight-type,

```
M-e_1-P=d_MM+k_MM,
P=k_MM+Z_M-d_MM.                                   (22)
```

Contracting the straight corridors and the bend paths gives a connected
multigraph. Its non-pendant vertices are the J_3+J_4 junctions and o;
its non-pendant edges are the g corridor edges and the P through strands.
Contraction preserves cycle rank, so

```
g+P=J_3+J_4+c-1.                                  (23)
```

These are literal strand counts. In particular neither a knight edge nor
a contact-type edge may be paid again after its contribution to P in
(22) has already been used.

For z=0, (18) has a further geometric consequence. Every non-endpoint bend
belongs to exactly one knight pair. A through strand with k knight pairs
therefore has 2k bends and k-1 contact-type bend-bend edges. A pendant
strand with k knight pairs has 2k+1 bends and k contact-type edges.

Across a knight pair the two right-angle turns have opposite signs.
Traversing a strand, its edge directions consequently alternate between
one fixed main direction and transverse steps of either sign. A through
strand's main-coordinate displacement is k+1, and its transverse
displacement has absolute value at most k. In particular it cannot make
an uncharged reversal in its main coordinate. For exterior anchors this
statement uses the physical port positions, not a fictitious common
coordinate for o.

## Junctions Paid In A Larger Subclass

Here is a second actual metric theorem, allowing arbitrarily many junctions:

> If z=0 and P=0, then on a W_0 by H_0 board with both dimensions at least
> 11,
>
> `M/4+(3/2)w+t+c >= min(W_0,H_0)-2`.

The condition P=0 says that every bend path is pendant; its length need
not be one. This is different from the earlier no-junction hypothesis.
In particular the square comb has J_3=s but z=P=0.

Here is the complete payment and metric proof. Because z=0, (19) says
that a junction has degree one in R if it is of type J_3, and degree zero
if it is of type J_4. Since all bend paths are pendant, connectivity of
C implies that R is connected. Hence J_4=0, every J_3 vertex is joined
directly to o by one R edge, and all remaining R edges are loops at o.
Put j=J_3 and let q_0 count these loops. Then

```
g=j+q_0,  t_R=j+2q_0,  c=q_0+1,
e_1=2j+t_M,  k_MM=d_MM,
M=2j+t_M+2d_MM.                                    (24)
```

The first line counts the actual star-with-loops graph R. The second
counts its bend-path attachments and uses (18),(22), not a separate
assumption about the lengths of the pendant paths.

Substitute (24) into the carrier packet and contact identities (4),
(14)--(16). They give exactly

```
w=j+2q_0+t_M/2+delta_bd,
delta_bd=2+q_bd-C_o/2>=0.                           (25)
```

For the desired weighted budget S, all junctions now have a full payment:

```
S=M/4+(3/2)w+t+c
 =3j+6q_0+2t_M+t_0+1+(3/2)delta_bd+d_MM/2
 >=3g+2t_M+t_0+1+d_MM/2.                           (26)
```

It remains to use lengths, rather than equating an edge count to a side
length. Write X_2 for the number of straight crossing-origin core vertices.
Each is in one corridor path, so X_2<=A g. Assign deleted leaves to their
actual parents. A straight crossing accounts for three cells, a J_3
junction for two, the bends and their leaves for M+e_1, and o for t_0.
This gives the exact cell partition and its metric bound

```
AB=3X_2+2j+M+e_1+t_0
  =3X_2+6j+2t_M+2d_MM+t_0
 <=3(A+2)g+2t_M+2d_MM+t_0
 <=(A+2)(S-1).                                     (27)
```

The last step uses (26) and A+2>=4: the d_MM/2 credit pays for the
2d_MM cells in the longer pendant strands. Consequently

```
S >= 1+AB/(A+2)
   = min(W_0,H_0)-2B/(A+2)
   > min(W_0,H_0)-2.                               (28)
```

On a square, (6) and C_o<=4 imply r+b+c>n-1, hence r+b+c>=n by
integrality. Thus f<=T+3 for this class on n=3k+2, k>=3. This is a
proved junction-bearing subclass result, not a global theorem.

There is a sharper geometric version when every bend is itself a core
endpoint, e_1=M. Then d_MM=k_MM=P=0. A terminal J_3 corridor has a cap
of exactly six cells: its junction and leaf, and its two pendant bends
and their leaves. If the corridor points east, these cells occupy two
columns and three rows immediately to its west, including the junction
column. This holds for all three possible locations of the junction's
leaf (west, north, or south); the leaf neighbours of the two terminal
bends force the other two cells in that same rectangle. Rotation gives
the other directions.

The cap and corridor therefore fit in one width-three rectangle of length
at most A, rather than requiring an extra six-cell allowance. The q_0
spanning corridors are also width-three rectangles. All remaining cells
belong to the t_M two-cell exterior bend branches or the t_0 exterior
leaves. Thus

```
AB<=3A g+2t_M+t_0<=A(S-1),
S>=min(W_0,H_0).                                   (29)
```

This sharper subclass includes the square comb exactly: j=s, q_0=0,
t_M=t_0=d_MM=0, delta_bd=2, and (26) gives S=3s+4=n+3.

## The Remaining Interior-Strand Cost

The same telescope identifies the remaining cost when z=0 but P>0.
Let p count R edges between two J_3 vertices, q those between J_3 and o,
and h the loops at o. Isolated J_4 vertices are retained in R. Then

```
J_3=2p+q, t_R=q+2h, g=p+q+h,
P=p+J_4+(c-1)-h,
w=t_R+t_M/2+delta_bd.                              (30)
```

These follow from the degree-one/degree-zero structure in (19), the rank
identity (23), and the same packet substitution used in (25). In particular
(c-1)-h>=0, since the h loops are independent cycles of C.

The exact budget is now

```
S=P+3q+6h+d_MM/2+2t_M+t_0+1+(3/2)delta_bd
 =3g-2p+J_4+(c-1)+2h+d_MM/2+2t_M+t_0
   +1+(3/2)delta_bd.                               (31)
```

Thus boundary corridors are paid at three units and spanning corridors
at six. What is not paid automatically is two units for each
interior-to-interior corridor p. Through strands supply some compensating
rank and can join such corridors, but (31) alone does not control the
total lengths after those joins. This is a much narrower obstruction
than paying an arbitrary four- or five-unit charge at every junction.

The case of isolated holes also remains open. There Z_M and Z_X enter
(18)--(20), and cannot simply be charged several times against the same
component credit c.

## Short Through-Strand Merging

There is a geometric saving for part of the remaining P>0 case. Continue
to assume z=0. Call a corridor positive if it has at least one straight
crossing-origin vertex, and let g_+ count these corridors. A good short
through strand consists of one knight pair and has, at each end, a J_3
junction incident to a positive corridor.

**Claim.** The two positive corridors at such a strand have the same
orientation and point away from one another. Joining them across the
strand preserves monotonicity in their common axis.

Here is a coordinate proof, including the orientation obstruction. Rotate
or reflect so that the knight pair consists of the cells (0,0),(1,0),
with F corners (0,0),(2,1), respectively. Cell coordinates mean the
lower-coordinate corner. Their other neighbours are the crossing cells

```
v_1=(0,1), v_2=(1,-1).
```

The positive corridor at v_1 can point west or north, but not east: the
eastern cell contains the preserved vertex (2,1). Similarly v_2's corridor
can point east or south, but not west, because its western cell contains
(0,0). The remaining directions lead to the two bends, not to corridors.

If v_1 points west and v_2 south, their first straight crossing cells force
F at (-1,0) and (0,-1), respectively. Together with F at (0,0), these
make a forbidden turn of a carrier. If v_1 points north and v_2 east, they
force F at (2,2) and (3,1), giving the same forbidden turn at (2,1).
The only possibilities are therefore west/east or north/south.

In either remaining case the straight intervals have disjoint projections
on their common axis, with the short strand advancing between them.
Thus the saving concerns literal length, not merely a reduction of an
abstract graph's vertex count.

Select any collection of good short strands using each corridor-end
junction at most once. Each positive corridor can then have at most one
selected join at each end. The claim makes each resulting chain monotone
in one axis; a closed chain is impossible. Exterior ports remain separate
physical chain endpoints even when their abstract vertex is o. If l joins
were selected, there are g_+-l chains, and their straight crossing cells
satisfy

```
X_2 <= A(g_+-l).                                   (32)
```

One can always select at least half the good short strands. Their graph
on the J_3 end junctions has maximum degree two, since a J_3 junction has
only two bend neighbours when z=0. It is bipartite: each short strand
joins cell positions with a displacement (1,2) or (2,1), with signs.
Its components are paths or even cycles. Alternating two colours on
their edges and taking the larger colour class gives a matching of at
least ceil(B_good/2) edges, where B_good counts the good short strands.
Consequently the physical cell partition gives

```
AB <= 3A(g_+-ceil(B_good/2))+2J_3+J_4+M+e_1+t_0.    (33)
```

This is a genuine improvement over assigning a full board length to
every R edge. Zero-length R edges are not counted, and each selected
join saves one whole A-unit length allowance. It is not yet sufficient
for the global bound: P can include longer strands or strands ending at
knots or exterior bend ports, and no lower bound on B_good that pays
the entire 2p term in (31) has been proved.

## A Genuine Knight Length Discount

There is a metric resource for the remaining through-strand problem, not
just a new equality. Give each non-singleton carrier its actual axis, and
give each singleton either axis once and for all. Let K_parallel count
knight-type bend-bend edges whose two carriers have the same assigned axis.
On a square of vertex side n,

```
2(nr-f) >= n K_parallel.                            (34)
```

To prove this, for a horizontal carrier [a,b] assign outward insets a to
its left end and n-1-b to its right end. They sum to n minus its length.
Each end has at most two actual bend cells, including a singleton's two
formal ends at the same vertex. The same construction holds vertically.

A knight edge between two horizontal carriers joins facing ends. Indeed,
the two participating bend cells must each contain only their single F
corner, so the left carrier cannot extend rightwards into its bend cell,
and the right carrier cannot extend leftwards into its bend cell. Their
endpoint x coordinates differ by one or two. The two outward insets
therefore sum to (n-1)+1 or (n-1)+2, at least n. The vertical case is the
same. Knight edges form a matching on bends by (18), so each endpoint
inset is used at most twice. Summing proves (34).

The factor two is an endpoint-slot allowance, not an assumption that all
knight edges form a matching on whole carriers. This distinction includes
singletons and prevents overspending a carrier's length deficit.

The same n-unit tax is false for perpendicular knight pairs. For n>=4,
preserve a horizontal rod (x,0), 0<=x<=n-3, and a vertical rod
(n-1,y), 1<=y<=n-1. Their forced supports are disjoint trees: the
minimum distance between the preserved sets is three. Their nearby ends
give a knight-type bend-bend edge, but their outward insets are only
2 and 1. Both rods have length n-O(1). This is a paper counterexample
for every n, not finite evidence. Boundary credit is essential for such
perpendicular pairs; (34) must not be applied to them.

No allocation of these perpendicular events, together with the two-unit
interior-corridor cost in (31), has been proved here.

## Global Target And Exceptional Area

This continuation uses only the desired global quantity

```
K_global=r+b+c.
```

It does not propose a bounded stronger weighted target. On a square put
A=n-1, the cell side, and define the actual exceptional-cell count

```
Q_exc=2J_3+J_4+M+e_1+t_0.
```

Assigning each deleted leaf to its parent gives, without assuming z=0,

```
A^2=3X_2+Q_exc.                                    (35)
```

All isolate contributions can be retained in an elementary area bound.
Equations (14),(15),(17) imply

```
e_1<=2r,  2J_3+J_4<=4r+4z,  M<=4r.
```

Also z<=c and t_0<=t<=b, the last inequality following from (2) and
C_o<=4. Consequently

```
Q_exc<=10r+4z+t_0<=10K_global.                      (36)
```

This pays only for actual exceptional area. It does not treat an isolate
as four separate component credits, or assert that its incident branches
each cost a full board length.

Here is a useful conversion lemma. Suppose a geometric argument gives a
nonnegative length allowance L_cap with

```
X_2<=A L_cap,
3L_cap<=K_global-2+D,  D>=0.                        (37)
```

Then (35),(36) give

```
(A+10)K_global >= A^2+A(2-D),
K_global >= A-8-D+(80+10D)/(A+10) > n-9-D.          (38)
```

On n=3k+2 the original ledger therefore implies

```
3(f-T)<19+D.                                       (39)
```

In particular a debt-free geometric certificate D=0 proves f<=T+6.
The constant six is deliberately not optimized. The point is that all
exceptional cells, including isolate effects, have already been accounted
for using K_global itself. What remains is a genuine length allowance in
(37), not a uniform bound on a larger weighted expression.

## Thin Zigzag Rigidity

Assume z=0. The earlier main-direction statement can be sharpened:
the transverse steps of a bend strand must alternate in sign. Thus a
strand stays in two adjacent cell columns or rows; it cannot wander
transversely through an arbitrary sequence of knight steps.

To see this, orient a strand's main direction north. A knight pair
traversed eastwards has its F corners northwest in the first cell and
southeast in the second. If the next knight pair were also traversed
eastwards, the intervening vertical bend-bend edge would itself be a
knight edge: its two F corners would have differences 1 and 2. That would
give a bend two knight partners, contrary to the matching in (18).
The next transverse step is therefore westwards. The other case is its
reflection. Between successive pairs the edge is contact-type, as
required by the strand decomposition.

For a through strand with k pairs, translate the initial anchor to (0,0)
and take its first transverse step east. The bend cells are exactly

```
(0,i),(1,i) in that order, if i is odd;
(1,i),(0,i) in that order, if i is even;
1<=i<=k.
```

The final anchor is (k mod 2,k+1). The corresponding F corners in pair i
are

```
(0,i+1),(2,i) if i is odd;
(2,i+1),(0,i) if i is even.                         (40)
```

These coordinates are a consequence of the actual bend directions, not
a replacement model for F. Reflections and rotations cover every strand.

There is a useful length consequence. The F vertices at main levels
2,...,k each occur in two geometrically adjacent bend cells on the same
side of that F vertex, not in consecutive vertices of the bend path.
If their carrier is not a singleton, it must point
outwards, perpendicular to the strand's main axis. In particular the
knight pairs numbered 2,...,k-1 join parallel, outward-facing carriers.

Singleton axes can be chosen consistently with all these internal uses.
An internal use in a vertical strand occupies the two bend cells east or
west of the singleton; an internal use in a horizontal strand occupies
its north or south pair. Those pairs intersect, so they cannot belong to
two different bend paths. Two disjoint internal uses therefore prescribe
the same carrier axis.

With that choice of singleton axes, (34) proves

```
K_parallel >= sum_through strands max(k-2,0),
2(nr-f) >= n sum_through strands max(k-2,0).         (41)
```

This is a real inset discount for internal pairs of long strands. It is
not a second independent copy of their bend or contact credit: an
allocation that uses (41) must track which pairs have already been spent
in a merge or another length argument.

## Long Strands Paid Without A P Bound

Still assume z=0. Let k_s be the number of knight pairs in each through
strand, and let k_a be the corresponding number in each pendant strand.
The physical contact-edge decomposition gives

```
d_MM=sum_through(k_s-1)+sum_pendant k_a.             (42)
```

Put beta=c-1. Substituting P=p+J_4+beta-h into (31), and then using
(42), yields exactly

```
S=3g+1+C_bank-D_short,

D_short=(1/2)sum_through max(5-k_s,0),
C_bank=3J_4+3beta+2t_M+t_0+(3/2)delta_bd
       +(1/2)sum_pendant k_a
       +(1/2)sum_through max(k_s-5,0).              (43)
```

All summands of C_bank are nonnegative. This is a reallocation of the
single budget (31), not additional credit. Through strands with five or
more pairs have been fully paid, regardless of how many there are. The
unpaid costs of the remaining lengths are precisely

```
k_s=1: 2,   k_s=2: 3/2,   k_s=3: 1,   k_s=4: 1/2.  (44)
```

**Theorem.** If z=0 and every through strand has at least five knight
pairs, then f<=T+6 on n=3k+2, k>=3. There is no bound on P.

Indeed D_short=0, so S>=3g+1. Since
K_global=S+4-3C_o/4>=S+1, one has 3g<=K_global-2.
Use L_cap=g in (37), together with X_2<=A g, to obtain (39) with D=0.

There is also an unrestricted-strand-length result when p=0: (31)
directly gives S>=3g+1 and the same f<=T+6 conclusion. This allows P>0,
degree-four knots, and arbitrary strand lengths. It is not the same
condition as the previously proved P=0 subclass.

More generally, let l be any valid collection of the short-strand joins
from (32), and let g_zero=g-g_+. Using that geometric capacity, the
measured residual

```
D=max(0,D_short-C_bank-3g_zero-3l)                  (45)
```

gives (37) with L_cap=g_+-l, hence (39). Equations (43)--(45) exhibit
exactly which units have been allocated to long strands, joins, rank,
and exterior ports. No uniform bound on (45) is asserted or proposed as
a stronger global target. It can overestimate what is needed: actual
shortness of unmerged corridors and perpendicular boundary insets are
not yet included in this sufficient certificate.

## A Two-Pair Merge Obstruction

The short-pair merge theorem cannot simply be extended to all bounded
strand lengths. This already fails for k_s=2 in a feasible, isolate-free
square family.

For n=3s+1 or n=3s+2, s>=2, preserve the full spine x=0 and the teeth
{(x,3j): 2<=x<=n-1, 0<=j<=s}. The disjoint tooth bands attach once each
to the spine and cover the board, giving a spanning forced tree. When
n=3s+1 this is exactly the comb from (13). Delete only its preserved
spine vertex (0,3). In H this removes exactly the edge
(0,3)(1,3): the two vertical edges at (0,3) remain forced by their other
endpoints. Removing that edge from the original spanning tree produces
two trees. Neither endpoint becomes isolated: (0,3) retains its two
vertical forced edges, and (1,3) retains its edge to the tooth at (2,3).
All other degrees are unchanged. Thus the new configuration has z=0,c=2.

Its dual has the following through strand in cell coordinates:

```
crossing (1,1)
 -- bend (1,2) -- bend (0,2) -- bend (0,3) -- bend (1,3)
 -- crossing (1,4).
```

The first and last bend-bend edges are knight-type and the middle one
is contact-type. Both endpoint junctions have positive corridors pointing
east, each with n-3 straight crossing cells. Their combined straight
length is 2(n-3)>n-1. They cannot be charged as one monotone length
allowance A=n-1. The thin zigzag itself is monotone north-south; that
does not make its attached eastward corridors an east-west monotone chain.

This example is paid by the existing budget: its corridors are boundary
corridors, not unpaid interior ones, and the newly separated component
contributes to c. It is not a counterexample to the target. It refutes
only the attempted blanket extension of the short-strand merge lemma.

## Rigidity Of Short-Link Seams

There is additional geometry even for the k_s=1 strands. Retain only
positive corridors having at least two straight crossing cells, and good
short strands whose two endpoint corridors have that property. A connected
component of this good-strand graph has one common corridor orientation,
by the short-strand merge theorem.

Suppose this orientation is horizontal. At a junction of degree two in
the good-strand graph, the two neighbouring corridors point in the same
direction, opposite to the middle corridor. Their endpoint columns differ
by at most one, since each short strand advances one or two columns.
Their first two straight crossing cells therefore have a common column
label. At that label, each corridor requires horizontal FF edges on the
two carrier rows one below and two above its cell row.

The two neighbouring corridor rows must consequently differ by exactly
three. Their row difference is at most four, from the knight displacements.
Differences one or two give parallel FF edges at distance one or two;
difference four gives such edges on the two inward carrier rows. All
these alternatives force four- or six-cycles. Distinct neighbours cannot
have row difference zero in the available knight positions.

Hence one neighbour lies one row to one side of the middle junction and
the other two rows to its other side. Following the good-strand component
makes its transverse coordinate strictly monotone; there is no cycle.
The successive transverse advances alternate between one and two. After
orienting that advance north, its junction coordinates satisfy

```
v_(i+2)=v_i+(sigma,3),  sigma in {-1,1},             (46)
```

with one fixed sigma along the component. Vertical corridors give the
rotated formula. In particular such a component is a rigid sloping seam,
not an arbitrarily wandering chain. It cannot contain both ends of one
horizontal corridor, since those ends have the same row coordinate.

This supplies an actual endpoint-displacement relation for a future
boundary telescope. It does not bound the seam's length by its number
of endpoints: it can still have a linear number of junctions. Paying its
ends against the physical boundary, longer strands, and isolate patches
remains unproved. The cap results in the separate fault-line and
moving-phase notes are for their specified geometries and are not being
imported as a theorem for these general seam endpoints.

## Singleton Guardrail For This Continuation

An auxiliary shortcut, that z=0 forces every carrier to meet the boundary,
is false. A feasibility-only 6 by 6 check found the following configuration,
which can be verified directly:

```
F.FFF.
......
FF...F
...F.F
F....F
..FF..
```

Use coordinates x=0,...,5 from left to right and y=0,...,5 from top to
bottom. Its seven carriers are the singleton (0,0), the top interval
[2,4], the row-two interval [0,1], the right interval y=2,...,4, the
singleton (3,3), the singleton (0,4), and the bottom interval [2,3].
The contact graph has exactly the two paths

```
top interval -- (0,0) -- row-two interval -- (0,4),
right interval -- (3,3) -- bottom interval.
```

Their forced supports are trees on 19 and 17 vertices, respectively,
and are disjoint. These sizes follow by summing the single-carrier tree
supports and subtracting the three and two shared contact holes. They
cover all 36 vertices. Hence z=0 and c=2, but (3,3) is an interior
singleton carrier. It also has a through bend strand: in cell coordinates
given by the lower-coordinate corner, the path

```
crossing (1,3) -- bend (1,2) -- bend (2,2) -- crossing (2,1)
```

has its two internal bends paired by a knight edge. Thus z=0 does not
imply P=0 either. The bounds above use the full singleton packet and do
not make either rejected inference. No optimization or larger search
was used for this countercheck.

## Status Of The Metric Attempt

The standard connection between nonleaves of spanning trees and connected
dominating sets applies to the augmented dual, but it does not on its own
prove the required weighted grid theorem. No external minimum-link or
connected-domination theorem with these weights is invoked. In particular
one cannot discard o, treat its physically separate ports as one ordinary
grid location, and apply a theorem for connected subsets of a rectangle.

There are proved metric bounds for both the no-junction class and the
isolate-free, pendant-bend-strand class. Both give f<=T+3 on n=3k+2 in the
stated range. The latter explicitly pays arbitrarily many junctions and
includes the square comb. Independent review subsequently covered both these
arguments and the newer packet and strand arguments. None is formalized.

The global conversion (35)--(39) retains all isolates in the natural
quantity r+b+c; their local area does not require a stronger weighted
target. In the isolate-free case, (43) completely pays long through
strands. This proves f<=T+6 when every through strand has at least five
knight pairs, with no bound on P, and also when p=0 with arbitrary P and
arbitrary strand lengths. It does not prove the unrestricted z=0 case.

The unresolved lengths are one through four pairs, with the exact costs
in (44). Equations (32),(33) merge compatible one-pair strands; (40),(41)
give thin-zigzag rigidity and an internal parallel-pair inset discount.
A two-pair strand can instead join two long same-facing corridors, as
the explicit square countercheck shows. Short-link seams have the actual
drift (46), but their terminal displacement has not been allocated to
the remaining boundary and contact credits. Perpendicular inset events
and isolate-induced branching also remain unallocated. No uniform bound
on the sufficient residual (45) is being substituted for the target.

No unrestricted r+b+c >= 3k-O(1), no counterexample to that bound, and no
improvement to the established unconditional half-coefficient upper bound
is claimed. This continuation changes only this note. No bound is inferred
from finite evidence. The only feasibility search recorded in this note
remains the earlier 6 by 6 singleton countercheck, whose forest and
coverage proof is given above; the present continuation ran no search
or optimization.

## Continuation After The Audited Prefix

This continuation originally followed the independently reviewed prefix
through line 1320. It has since received independent review as well.
Its final status supersedes the earlier status snapshot above.

The unrestricted constant-gap bound is still not proved. The completed
addition below is a joint matching/rank estimate that reduces the remaining
cost to blocked positive interior corridor ends. It is not a claim that
those ends are always exhausted.

## Terminal Parity And Longer Safe Joins

Assume z=0. Use the normalized through strand in (40): its initial anchor
is (0,0), its main direction is north, its first transverse step is east,
and its final anchor is (k_s mod 2,k_s+1). Suppose both anchors have
positive R corridors.

The first corridor can only point west or south. Its north neighbour is
the first bend, and its east neighbouring cell contains F at (2,1).
At the last anchor, the south neighbour is the last bend. If k_s is odd,
the western neighbouring cell contains F at (0,k_s+1); if k_s is even,
the eastern neighbouring cell contains F at (2,k_s+1). Thus

```
initial corridor: west or south;
final corridor:   east or north, if k_s is odd;
                  west or north, if k_s is even.   (47)
```

These are necessary endpoint-direction restrictions, not an assertion
that all the remaining combinations are realizable. For k_s=1 the earlier
four-cycle argument excludes the mixed-orientation choices.

Call a through strand eligible when both anchors are J_3 junctions with
positive R corridors and those two corridors are parallel and point
away from one another. Equation (47) proves the length property needed
for every such strand, not just one-pair strands:

* A south/north pair has disjoint vertical projections, separated by the
  k_s+1 main-coordinate advance of the strand.
* A west/east pair is possible only when k_s is odd. Its two straight
  corridor intervals have disjoint horizontal projections, separated by
  the one-column advance between the anchors.

For an odd strand joined horizontally, the intervening bends can zigzag
back and forth in those two columns. The proof uses the ordered straight
intervals, not a false assertion that every step of that bend path is
horizontally monotone.

Select eligible strands using each corridor-end junction at most once.
As in (32), the positive corridors form ordered chains with no cycle.
If nu strands are selected, then

```
X_2<=A(g_+-nu).                                    (48)
```

This gives safe joins for the parallel three-pair cases and for two- or
four-pair cases whose corridor axis is the strand's main axis. It does
not join the same-facing even-pair configuration in the deleted comb.
Mixed-orientation end pairs are not eligible under this lemma.

## Matching Slack And Full Rank

Form the eligible-strand graph on all J_3 junctions, retaining isolated
vertices. Let m_E be its number of edges and let nu be a maximum matching.
Each junction has at most two bend ports, so this graph has maximum degree
two. It is bipartite: a through strand with k_s pairs has 2k_s+1 physical
grid edges between its anchors, hence reverses cell checkerboard parity.
Paths and even cycles therefore give its matching exactly, without a
grid optimization argument.

Let n_2E count junctions of eligible degree two. Define

```
sigma_match=n_2E-2m_E+3nu>=0.                       (49)
```

For a path with m>=1 edges, its contribution is
3 ceil(m/2)-m-1, which is nonnegative; an isolated vertex contributes zero.
For an even cycle with m edges it is m/2. This proves (49) componentwise.
In particular this retains the path-parity improvement over simply
replacing nu by m_E/2.

Now retain ALL through strands, eligible or not, in the graph obtained
from C by suppressing corridors and through strands and deleting pendant
strands. It is connected and has cycle rank beta=c-1.

Let n_i count J_3 junctions with i incident through-strand ports, i=0,1,2.
Let d_4 count through-strand incidences at J_4 junctions and d_o those at
o. Loops contribute two incidences. The degree sum of this connected
graph is

```
n_2-n_0+d_4+d_o=2beta-t_R+2J_4.
```

Let b_3 count ineligible through-strand incidences at J_3 junctions, and
let u_0 count J_3 junctions with eligible degree zero. Every ineligible
strand is counted at its two ends, so

```
2(P-m_E)=b_3+d_4+d_o.
```

At a J_3 junction, compare its full through degree with its eligible
degree. The six possible pairs are (0,0),(1,0),(1,1),(2,0),(2,1),(2,2).
Counting these gives

```
u_0=n_0+b_3-(n_2-n_2E).
```

Combining these three equalities with (49) proves the exact joint balance

```
2P-3nu=u_0+2beta-t_R+2J_4-sigma_match.              (50)
```

This is the useful rank gain. It accounts for ineligible edges at knots,
exterior ports, and nonpositive corridors rather than ignoring them.
High short-strand incidence forces rank only after the unjoined ends u_0
have been retained. Large u_0 can otherwise compensate the degree sum.

## Boundary Ends Versus Interior Ends

Write p_zero and q_zero for the zero-length R edges of interior and
exterior type, respectively. A loop at o has positive length, so
g_zero=p_zero+q_zero. Let u_root count eligible-degree-zero junctions
whose R corridor meets o. Finally, let u_int count eligible-degree-zero
junctions whose R corridor is positive and has its other endpoint at a
J_3 junction.

Every zero-length interior R edge contributes its two ends to u_0. Each
of the q exterior R edges has only one junction end. Thus, exactly,

```
u_0=u_root+2p_zero+u_int,  0<=u_root<=q,
t_R=q+2h.
```

Use (50) in the unsplit version of (43), namely

```
S=3g+1+3J_4+3beta+2t_M+t_0
  +(3/2)delta_bd+d_MM/2-2P.
```

For L_cap=g_+-nu, the result is the exact endpoint budget

```
S=3L_cap+1+B_end-u_int,                            (51)

B_end=J_4+beta+2t_M+t_0+(3/2)delta_bd+d_MM/2
      +sigma_match+2h+p_zero+3q_zero+(q-u_root).
```

Every summand of B_end is nonnegative. This is still the single natural
budget S=K_global-4+3C_o/4, not a separately assumed reserve. In particular
rank has not been added to the budget a second time.

Together with (48), the actual residual

```
D_end=max(0,u_int-B_end)                            (52)
```

satisfies the hypotheses of (37). Hence, for every configuration in this
isolate-free analysis,

```
3(f-T)<19+D_end.                                   (53)
```

**Endpoint-exhaustion theorem.** If z=0 and every end of a positive
interior R corridor is incident to at least one eligible through strand,
then f<=T+6 on n=3k+2, k>=3. There is no bound on P and no restriction
on through-strand lengths.

Indeed the hypothesis is exactly u_int=0, so (51) pays the geometric
capacity (48), and (53) has D_end=0. The theorem also applies whenever
the measured u_int is paid by B_end. Neither condition has been proved
automatic for general feasible sets.

## What This Proves In The One-Pair Case

Suppose every through strand has one knight pair and is eligible. Then
u_0 consists precisely of the junctions with no through-strand attachment:
their two bend paths are pendant. Also J_4=0, since such a knot could
have only pendant attachments and would be disconnected from o.

In this case the full-rank equation simplifies to

```
n_2-n_0=2beta-t_R,
2P-3nu=n_0+2beta-t_R-sigma_match.                   (54)
```

Thus adjacent short edges do not leave an uncontrolled half-P term after
rank is used. The obstruction is the terminal-cap count, and specifically
the interior terminal caps left in u_int after (51) pays the boundary
ones. If every such terminal cap lies on an exterior R corridor, the
endpoint-exhaustion theorem proves f<=T+6, allowing arbitrarily many
adjacent short edges and arbitrarily many through strands.

It would nevertheless be wrong to infer large beta from adjacency alone.
As an abstract rank countercheck, take a through-edge path
v_0,...,v_(2m). Give v_i, i>=1, an R edge to a new terminal-cap junction
u_i, and give v_0 an R edge to o. This entire R-plus-through graph is a
tree. Its counts are

```
P=2m, p=2m, q=1, h=0, beta=0,
n_0=2m, n_2=2m-1, nu=m,
2P-3nu=m.
```

The many terminal caps account for the degree-two short-path junctions.
This is NOT asserted to be a realizable grid configuration or a
counterexample to the upper bound. It proves that the proposed conclusion
cannot follow just from the R matching, maximum degree two, connectivity,
and cycle rank. Physical restrictions on the interior caps are necessary.

The fixed seam displacement (46) is such a restriction, but no argument
here pays all the u_int ends from their seam displacement. In particular
an end count has not been substituted for the possibly linear length of
a seam.

## Mergeable Two- To Four-Pair Strands

The parity test also closes a further genuine case of the short-strand
problem. Suppose z=0, and every through strand with fewer than five pairs
has two, three, or four pairs and is eligible in the sense of (47),(48).
All longer through strands remain unrestricted.

Let m_short count these short eligible strands. Their eligible graph
has a matching of size at least ceil(m_short/2). Their total short cost
in (44) is at most (3/2)m_short. The selected joins consequently supply
at least that much length allowance, since each gives three units.
The longer strands have already been paid by (43). Thus (45) has D=0
and f<=T+6 follows, with no bound on P.

More generally, if all short strands are eligible and N_i counts those
with i pairs, i=1,...,4, then the half-matching estimate gives

```
D_short-3nu <= (1/2)N_1-(1/2)N_3-N_4.             (55)
```

For example N_1<=N_3+2N_4 is a sufficient debt-free condition, before
using any other bank credit. Equation (51) can be stronger because it
also retains rank and boundary-end exhaustion.

These results do not include same-facing even-pair strands or
mixed-orientation end pairs. The deleted-comb example remains a valid
warning: its two-pair strand is paid by boundary/rank resources, not by
a false one-length merge. No universal payment for all the remaining
blocked ends has been proved.

## A Bounded Rank Countercheck

Feasibility-only checks on boards of sides six and seven were used to
test shortcuts during this continuation. No optimization or board larger
than seven was used, and no nonexistence inference from those checks is
used as a lemma.

In particular beta=0 does not force p=0, even when the sole through
strand is an eligible one-pair strand. The following 7 by 7 configuration
is a directly verifiable counterexample to that shortcut:

```
.FFF.F.
.....F.
F.F..F.
..F..F.
F....F.
F..F...
F..F.FF
```

Use x=0,...,6 left to right and y=0,...,6 top to bottom. Its seven carriers
are: A, the top interval x=1,...,3; B, column 5 at y=0,...,4; C, the
singleton (0,2); D, column 2 at y=2,3; E, column 0 at y=4,...,6; F,
column 3 at y=5,6; and G, the bottom interval x=5,6.

Their contact graph is exactly the path

```
E -- C -- D -- A -- B -- G -- F.
```

The six shared holes in that order are (0,3),(1,2),(2,1),(4,0),(5,5),
and (4,6); there are no other support intersections.

The seven single-carrier forced supports have sizes 7,4,8,8,16,5,7 in
that path order. Their only intersections are its six distinct contact
holes. Thus their union is a tree on 55-6=49 vertices: H spans the
whole board, c=1, z=0, beta=0.

The dual corridor graph has the interior path

```
junction (3,1) -- straight crossing (3,2) -- junction (3,3)
```

and the exterior corridor from junction (1,4) through straight crossing
(1,5) to o. Its only through bend strand is

```
junction (3,3) -- bend (2,3) -- bend (2,4) -- junction (1,4).
```

The other bend paths are pendant. Hence p=P=1, and the strand is
eligible. Its single merge pays its two-unit cost, so this example is
harmless for the new theorem. It shows why beta=0 cannot simply be used
to discard interior corridors.

## Current Conclusion After This Push

The unrestricted global bound, including the unrestricted z=0 case, is
still open in this note. The completed new step is (50),(51): matching
and the full R-plus-through rank pay every term except the explicitly
blocked positive interior corridor ends. This gives the proved T+6
endpoint-exhaustion theorem for arbitrary P and arbitrary strand lengths,
and the further mergeable two- to four-pair result above.

The remaining obligation is geometric: show that blocked interior ends
are paid by the displayed bank or by additional actual length loss, or
show directly that K_global is already large when this certificate does
not close. No uniform bound on the sufficient residual (52), and no
bounded stronger weighted target, is asserted. Isolate-induced branching
is also not solved by the exceptional-area estimate alone.

Audit status: independent review subsequently covered this continuation
through its original line 1660, with no findings. All new bounds above are paper
derivations; the bounded checks supplied only the explicit countercheck.

## Cap Continuation After The Audit Boundary

This continuation originally followed the independently reviewed prefix
through line 1660. The cap appendix below has since received independent
review with no findings. No unrestricted constant-gap theorem is
claimed, including in the isolate-free all-one-pair eligible case.

There are new physical deductions: blocked ends have disjoint chain-inset
slots; non-immediate terminal caps can be paid from their own pendant
paths; and short caps in the next two inward positions have literal
boundary-port or boundary-contact payments. A boundary-spine exception
is exhibited in an explicit isolate-free 13 by 13 example.

## Exact Spare Length And Axial Insets

Work on a square, A=n-1, with z=0. Fix the eligible graph and a maximum
matching as in (48)--(51). Put L_cap=g_+-nu and

```
Delta_len=A L_cap-X_2>=0.
```

Each resulting chain has one fixed corridor axis. Orient that axis so
that its nonempty straight-cell intervals are [a_i,b_i], in increasing
order, within {0,...,A-1}. The exact missing length of this chain is

```
A-sum_i(b_i-a_i+1)
 =a_1+(A-1-b_last)+sum_i(a_(i+1)-b_i-1).            (56)
```

All terms are nonnegative. These are chain-specific length allowances,
not a claim that their projections on different chains are disjoint
physical boundary holes.

For a blocked positive interior end v, let h(v) be its outward axial
inset to the first or last straight cell. For a horizontal corridor,

```
h(v)=x(v)+1  if its corridor points east,
h(v)=A-x(v)  if its corridor points west.
```

The vertical definition is the rotated one. This is an axial inset,
not distance to whichever board side happens to be closest. A blocked
end has eligible degree zero and is therefore an end of its matching
chain. Its h(v) occupies exactly one of the two exterior terms in (56).
No such slot is used twice. Consequently

```
sum_blocked ends h(v)<=Delta_len.                  (57)
```

For an immediate six-cell cap, the distance of the cap rectangle's back
edge from its outward board side is h(v)-2. Thus h=2 is a cap touching
that side, h=3 has its back edge one cell inward, and h=4 has it two
cells inward. Every positive interior corridor junction is an interior
cell vertex, so these h values are at least two.

Using exact spare length, rather than discarding it, (51) gives the
valid sufficient certificate

```
D_len=max(0,u_int-B_end-3Delta_len/A),
3(f-T)<19+D_len.                                   (58)
```

For this application of (37), use
L_cap-Delta_len/A=X_2/A as the length allowance. The substantive new
geometric input is (57); defining D_len alone is not a proof that it
is bounded.

There is also a necessary accounting warning. A join between an incoming
right end at axial coordinate a and an outgoing left end at b removes
the two endpoint insets whose sum is A+(b-a+1), and creates an internal
gap of b-a+1. Thus each join reduces Delta_len by A. At the same time
sigma_match, and hence B_end, increases by three in the formal account.
The combination B_end+3Delta_len/A does not increase merely by counting
both effects. More directly, (51) implies

```
u_int-B_end-3Delta_len/A = 1+3X_2/A-S.
```

Changing the matching cannot generate extra credit in this exact
expression. Geometry must provide the payment; matching, insets, and
seam drift are not three independent budgets.

## Paying Non-Immediate Terminal Caps

For the following cap analysis, assume every through strand is a
one-pair eligible strand. This is a restriction on the actual set, not
a normalization. A blocked positive interior end then has two pendant
bend paths. Let kappa(v) be the sum of their knight-pair counts. Their
contact-type edges are private to those paths, so (42) gives

```
sum_blocked caps kappa(v)<=d_MM.
```

**Cap lemma.** A terminal junction on a positive corridor cannot have
kappa(v)=1. Thus it is either an immediate six-cell cap, kappa(v)=0,
or has kappa(v)>=2 and can pay its whole unit from d_MM/2.

Here is a coordinate proof of the exclusion. A one-pair pendant path
has three bend cells followed by its deleted leaf. In the northward,
east-first normal form these bend cells are (0,1),(1,1),(1,2), and the
leaf is (0,2). Its FF edge is (0,2)(0,3). Thus a one-pair pendant forces
an FF extension of its first bend's F corner in the direction from the
anchor to that first bend. Rotate or reflect this observation as needed.

Now put the terminal junction at (0,0), with a positive corridor pointing
east. The first straight crossing cell forces horizontal FF edges with
endpoints

```
(1,2),(2,2) and (1,-1),(2,-1).
```

A pendant leaving north or south has its first F corner at (1,2) or
(1,-1), respectively. If it had one knight pair, the preceding observation
would add a vertical FF edge at that corner, giving a forbidden turn.

The only remaining possible location for the sole one-pair pendant is
the west port; the junction's leaf is then north or south. If the leaf
is north, the west bend's F corner is (-1,0). The other, immediate south
pendant forces the vertical FF edge (-1,-1)(-1,0), whereas the one-pair
west pendant would force (-2,0)(-1,0). This is again a forbidden turn.
The south-leaf case is its reflection. These exhaust the possibilities.

Let N_long count blocked caps with non-immediate pendant paths. The lemma
therefore proves

```
N_long<=d_MM/2.                                    (59)
```

No cap or vertex has been deleted or repaired. The deduction pays actual
non-immediate caps from actual disjoint pendant-path contributions. The
remaining blocked caps really have the six-cell geometry used below.

## Literal Boundary Payments For Short Caps

Use one of the remaining immediate caps, and orient its positive corridor
east. Its junction is at (a,y), its assigned six cells have columns a-1,a
and rows y-1,y,y+1, and its back face is the grid line x=a-1. There are
three possibilities for the junction's leaf: west, north, or south.

In every case at least one of the cap's three leaf cells corresponds to
a vertical FF edge on that back face. For a west leaf all three do; for
a north or south leaf the lower or upper back-face edge does. Choose one
such edge once per cap. The six-cell sets of distinct immediate caps are
disjoint as assigned dual-cell sets, even though their preserved carriers
or forced supports need not be disjoint.

### Caps With h=2

Here a=1 and the back face is the physical boundary x=0. If the junction's
leaf is west, that boundary face contains four consecutive F vertices.
They belong to one actual pure boundary carrier. No hole in this four-
vertex footprint is forced, and no separate unit per cap may be assumed
from that one carrier interval.

If the leaf is north, the boundary labels on rows y-1,...,y+2 are
F,F,U,F. The hole at (0,y+1) is a boundary contact; its upper F neighbour
also has a preserved inward neighbour. The south-leaf case is the
reflection. The boundary contact's one valid perpendicular dual edge
is a leaf-bend edge contained in the assigned cap. Hence different caps
of these two types use distinct q_bd contacts.

### Caps With h=3

Here a=2 and the selected back-face FF edge is on x=1, say between
rows j and j+1. Both mirror vertices (0,j),(0,j+1) are U: either being
F would be diagonally opposite one of the FF endpoints. The cell between
this UU boundary edge and the selected FF edge is a dual leaf attached
to o. It supplies an actual t_0 port.

The chosen inward leaf cell of the cap identifies the selected FF edge
and its mirror uniquely. Distinct caps therefore use distinct t_0 ports.
This pays one unit per such cap from the t_0 term of B_end, not from a
new copy of b.

### Caps With h=4

Here a=3 and the selected FF edge is on x=2. Its boundary mirror cannot
be FF, by the six-cycle around the width-two, height-one rectangle.
The two next-ring vertices on x=1 at the edge's rows are U by the
diagonal obstruction. Every F endpoint of the mirror has no preserved
inward neighbour and belongs to a pure boundary carrier.

For a fixed side, distinct caps choose distinct FF edges: the inward
leaf cell of each chosen edge belongs to its own assigned cap. Thus
their chosen boundary mirror edges are also distinct.

There are three cases for paying the chosen mirror edge.

* If the mirror is UU, its boundary cell is X and its inward neighbour
  contains the selected FF edge, hence is a leaf. Since z=0, this X is
  a J_3 junction with its sole R edge directly to o. This is a q_zero
  exterior corridor, not a positive corridor.
* If the mirror is FU and its hole is an open-boundary vertex with an
  adjacent boundary U on the other side, use that neighbouring UU edge.
  Its next-ring endpoints are also U by the same diagonal obstruction.
  The boundary cell is X and its inward neighbour contains an endpoint
  of the selected FF edge, so is M or a leaf. It cannot be a straight
  X_2 cell; (19) then makes it a J_3 with a zero-length R edge to o.
* If that FU hole instead has an F boundary neighbour on its other side,
  it is a q_bd contact. Both of its F neighbours have inward U neighbours:
  an inward F at either one would be diagonal to a selected FF endpoint.

For a fixed boundary UU edge, at most three chosen mirror edges can use
its q_zero credit: the edge itself and the immediately preceding or
following FU edge. The 3q_zero term in B_end is exactly sufficient.

At most one chosen FU mirror can use a given q_bd contact. Otherwise
both boundary edges incident to that hole have selected FF mirrors on
x=2. The two boundary F vertices and those FF edges force the eight-cycle
around a width-two, height-two rectangle. This contradicts feasibility.

These h=4 contact witnesses cannot coincide with the h=2 corner-cap
witnesses: the latter have an F neighbour with a preserved inward
neighbour, while the former have neither. Thus their q_bd payments are
jointly injective, not two separate uses of the same contact count.

The remaining corner case is also physical. If the hole of a chosen FU
mirror is a board corner, its other boundary neighbour is U by the
diagonal obstruction. The perpendicular boundary UU edge has a bend cell
on its inside, giving a t_M port. The chosen FU edge and this port identify
one another at that corner, so there is at most one charge per such port.
The coefficient two of t_M is more than sufficient. A direct UU mirror
at a corner in this construction would instead make the corner an H
isolate and is excluded by z=0.

Combining the three depths, let N_near count the immediate caps with
h=3 or h=4, together with the h=2 caps whose leaf is perpendicular to
their corridor. The construction proves the simultaneous bound

```
N_near<=t_0+3q_zero+t_M+q_bd.                       (60)
```

All port counts include their actual multiplicities. Mirrors on different
sides are different boundary edges; the corner case above prevents
silently treating a corner cell as two leaf ports. Since
(3/2)delta_bd>=(3/2)q_bd, (60) is paid by the existing nonnegative terms
of B_end. The zero-length R allowances are not also included in Delta_len,
which was defined only after zero R edges were discarded.

## A Combined Cap-Inset Theorem

The preceding deductions can be combined without imposing a normalization
of F. Continue to assume z=0 and all through strands one-pair eligible.
Pay N_long non-immediate caps by (59), and pay N_near immediate caps by
(60). These two classes are disjoint. Put

```
B_rem=B_end-N_long-N_near>=0,
V_rem=the remaining blocked immediate caps.
```

The inequality B_rem>=0 follows from termwise bounds in the single budget:
d_MM/2 pays N_long, while t_0+3q_zero+t_M+q_bd pays N_near. All of
these units occur in B_end with at least these coefficients. The terms
are not assumed independent; no unit within a term is assigned twice.

Use only the inset slots of V_rem in (57). The refined residual in (58)
satisfies

```
D_len <= max(0,
       sum_(v in V_rem)(1-3h(v)/A)-B_rem).          (61)
```

**Theorem.** In this actual all-one-pair eligible class, if every remaining
cap has h(v)>=A/3, then f<=T+6 for n=3k+2, k>=3. More generally the same
conclusion holds whenever the signed sum in (61) is at most B_rem.

This permits arbitrarily many blocked ends. It is a proved geometric
sufficient condition: the cap count is paid by disjoint pendant-path
units, literal boundary witnesses, and distinct chain-inset slots.
Negative contributions of deep caps have not been truncated separately.
Other unused chain-end slots and internal gaps remain available in the
exact Delta_len; they are not asserted to vanish.

The unrestricted condition has not been proved. The unclassified
immediate caps are precisely the h=2 straight boundary-spine type and
the caps with h>=5 not sufficiently paid by their insets or other bank
credit. A pure boundary interval is not automatically a fresh token
each time it supports another cap.

## What Signed Seam Displacement Supplies

For a horizontal short-link seam from (46), define the axial inset of
its junction v_i by A-x_i when its corridor points west, and x_i+1 when
its corridor points east. These are insets at the seam end of the
corridor, not automatically insets of the blocked cap at its other end.
The corridor directions alternate along the seam. Consequently (46)
implies

```
h(v_(i+2))-h(v_i) = -sigma for west-pointing corridors,
                     sigma for east-pointing corridors.           (62)
```

The signed increments alternate and telescope. In particular, for m>=2
links their two-parity sum is
h(v_(m-1))+h(v_m)-h(v_0)-h(v_1), not a positive unit per link.
Replacing those signed increments by their absolute values would lose
the cancellation and reuse a supposed depth debt down the whole seam.

For an individual positive unmerged corridor, the insets at its two ends
sum to A minus its straight length, with inset zero at a physical exterior
end. Thus the far-end cap insets can be obtained from seam-end insets
only while retaining the actual corridor lengths. No lower bound on all
the remaining far-end cap insets follows from the seam end count alone.
The needed nonlocal boundary/interval allocation is not supplied here.

## A Pure-Boundary Blocked-Cap Countercheck

The straight-spine exception is real, even in the isolate-free
all-one-pair eligible setting. A seven-by-seven feasibility check found
the seed below. Its properties, and those of the larger explicit example,
are verified by physical tree attachments rather than by a numerical
upper-bound claim.

```
..F..F.
F.F..F.
F....F.
F..F.F.
F..F...
.....FF
FFFF...
```

Its six carriers, in contact-path order, are column 2 at rows 0,1;
column 0 at rows 1,...,4; row 6 at columns 0,...,3; column 3 at rows
3,4; column 5 at rows 0,...,3; and row 5 at columns 5,6. Their only
contacts are at

```
(1,1), (0,5), (3,5), (4,3), (5,4),
```

in that order. Their single-carrier forced supports have sizes
7,10,9,8,13,7. Gluing along the five distinct contact holes therefore
gives a tree on 54-5=49 vertices. Thus the seed has z=0,c=1.

Here is an explicit 13 by 13 example, so the local countercheck is not
confined to a board below the main paper range. Let F_7 denote the seed
and preserve exactly

```
F_13={(x,y+6):(x,y) in F_7}
     union {(2,y),(5,y):0<=y<=5}
     union {(0,1),(0,4)}
     union {(8,y),(11,y):0<=y<=12}.                  (63)
```

First extend the seed to a 7 by 13 rectangle. The two upward spine
extensions on columns 2 and 5 add disjoint tree branches, each attached
once to the old tree. They cover columns 1,...,6 of the new six rows.
The stars at (0,1),(0,4) each attach once to the column-2 spine and
cover the remaining six vertices of column 0. The result is a spanning
tree on 91 vertices.

The full spine on column 8 covers the new columns 7,8,9, adding a tree
on 39 vertices. The only preserved vertex on the old right boundary
column 6 is (6,11), so exactly one forced edge joins this new tree to
the old one, through (7,11). The full spine on column 11 similarly
covers columns 10,11,12, but no F vertex on column 9 joins it to the
first component. The full forced graph therefore consists of trees on
130 and 39 vertices, with no isolates: z=0,c=2.

The old knight pairs are merely translated by (0,6). All new
bends are terminal: those beside the new left-boundary singletons attach
to leaves of the extended column-2 spine, and those beyond the old
right endpoint (6,11) attach to leaves of the column-8 spine. The old
pendant strand at the bottom remains pendant. Directly, M=19,e_1=13,
k_MM=3; two knight pairs lie in that old pendant strand, and the sole
through strand is the eligible one-pair path

```
junction (3,7) -- bend (2,7) -- bend (2,8) -- junction (1,8).
```

In particular the corridor

```
junction (1,8) -- straight crossing (1,9) -- junction (1,10)
```

has a blocked terminal cap at (1,10). Its two bends, (0,10) and (2,10),
are immediate pendant bends. The cap has h=2 and its outward boundary
footprint is the four vertices (0,12),...,(3,12), all F in one pure
boundary carrier. There is no boundary hole in this mirror footprint.

This disproves a hole-only local rule for every near-boundary blocked
cap, including in the isolate-free all-one-pair eligible class. It does
not disprove a joint interval or global-bank payment; this example has
ample global reserve. Nor does it prove that one pure interval can be
charged independently for every blocked cap it might support.
The 13-square has residue one. It refutes a residue-independent local
mirror rule, not a separately residue-two-only global theorem.

The only search in this continuation was the seven-by-seven feasibility
check. The 13 by 13 set was an explicit construction and direct edge
check, not an optimization. No board above 13 was checked.

## Current Cap-Geometry Conclusion

There is still no unrestricted global T+O(1) proof, nor a proof for every
isolate-free all-one-pair eligible configuration. The completed cap work
is (57), (59), and the literal near-boundary payments (60), together with
their non-reusing combination (61). Non-immediate terminal caps are paid
without a normalization, and immediate caps one or two back-face cells
inward have actual boundary-port/contact payments.

What remains is a nonlocal allocation for the surviving immediate caps,
especially straight caps backed by a preserved boundary interval and
intermediate-depth caps whose axial insets do not yet pay their units.
The signed seam identities do not by themselves supply that allocation.
The exact spare-length expression is matching-invariant, so it cannot
be improved merely by adding matching credit and then counting the same
lost length again.

Audit status: independent read-only review covered this appendix through
its original final line 2094, including the joint boundary payments and
explicit constructions, with no findings. The bounds are paper deductions;
the explicit examples
are counterchecks to the stated local shortcuts, not finite evidence for
a global upper bound.
