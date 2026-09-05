# Primal support components and cotree waste

## Setup

Let `G_n` be the `n x n` grid, `n >= 2`, and let `T` be a spanning
tree.  Write

```text
D = E(G_n) \ E(T)
```

and regard `S=(U,D)` as the primal graph formed by the omitted edges and their
endpoints.  Let

```text
d(v) = deg_S(v),
W    = sum_(v in U) (3-d(v)),
c_S  = number of connected components of S,
beta = |D|-|U|+c_S.
```

Here `beta` is the total cycle rank of `S`.  The plane-dual edges `D*`, with
the outer face left unsplit and parallel outer edges retained, form a spanning
tree of the `(n-1) x (n-1)` cell graph together with `OUT`.

The edges incident with one primal vertex form a dual cycle, including the
usual two-edge cycle at a corner.  Since `D*` is a tree, it cannot contain that
entire cycle.  Hence

```text
1 <= d(v) <= 3                 for every v in U.        (1)
```

Also

```text
|D| = 2n(n-1)-(n^2-1) = (n-1)^2.                       (2)
```

## Exact component theorem

Let `N_j` be the number of vertices of `S` of degree `j`.  For a component
`K`, let `L_K` and `N2_K` denote its numbers of degree-one and degree-two
vertices, with degrees measured in `S`.

**Theorem.** Every grid spanning tree satisfies

```text
W = 2N_1+N_2
  = |U|+2c_S-2beta
  = sum_(K component of S) (2L_K+N2_K).                 (3)
```

Consequently the proposed component-refined inequality

```text
W >= n+1+c_S                                             (C)
```

is equivalent to each of

```text
sum_K (2L_K+N2_K-1) >= n+1,                             (4)
|U|+c_S-2beta >= n+1.                                   (5)
```

**Proof.** By `(1)`, a degree-one vertex contributes two to `W`, a degree-two
vertex contributes one, and a degree-three vertex contributes zero.  This
proves the first and third expressions in `(3)`.  Euler's identity for the
possibly disconnected graph `S` gives

```text
beta=|D|-|U|+c_S.
```

Therefore

```text
|U|+2c_S-2beta = 3|U|-2|D|
                = sum_(v in U) (3-d(v))
                = W,
```

where the middle equality uses the handshaking lemma.  Subtracting `c_S` from
`(3)` proves the two equivalences.  QED

This is a genuine combinatorial reformulation, but not a proof of `(C)`.  Since
`D` is nonempty, `c_S>=1`, and `(C)` would imply the currently desired
universal bound `W>=n+2`.  For connected support it is exactly that bound; for
disconnected support it is strictly stronger.

There is also an exact translation to the established primal contour ledger.
Let `F=V(G_n)\U`, let `B(U)` count incidences of `U` with the four sides
(a supported corner counts twice), let `I_T(U)` count tree edges with both
endpoints in `U`, and let `c_F` count components of `G_n[F]`.  The identity

```text
W+1 = B(U)+I_T(U)+c_F
```

shows that `(C)` is equivalent to

```text
B(U)+I_T(U)+c_F >= n+2+c_S.                             (6)
```

Thus adding `c_S` does not remove the global congestion problem in a sweep or
channel proof; it asks the three existing resource classes to pay one extra
unit for every additional support component.

## What splitting the outer face actually does

Suppose `D*` contains `b` edges incident with `OUT`.  Replace `OUT` by one
private leaf for each of those edge occurrences, without adding boundary arcs.
The result is not generally a tree.  It is an acyclic graph with `b`
components.

Indeed, if the unsplit tree has `q` vertices and `q-1` edges, the split graph
has `q+b-1` vertices and the same `q-1` edges.  A forest with those counts has
exactly `b` components.  Equivalently, deleting `OUT` from a tree separates its
`b` incident branches, and attaching a private leaf to each branch does not
join them.

The number `b` is not the primal support component count `c_S`.  Here is a
small exact counterexample.  In the `3 x 3` grid, name the four cells

```text
A B
C D
```

and select the dual edges

```text
OUT-A, A-B, OUT-C, C-D.                                 (7)
```

They form a dual spanning tree.  Their primal representatives are

```text
(0,0)-(0,1),
(0,1)-(1,1),
(2,0)-(2,1),
(1,1)-(2,1).
```

These representatives form the single path

```text
(0,0)-(0,1)-(1,1)-(2,1)-(2,0).
```

Thus `b=2` but `c_S=1`.  Splitting `OUT` in `(7)` gives the two path
components `port-A-B` and `port-C-D`, not a spanning tree.  The complementary
eight primal edges are connected on nine vertices, so they are indeed a
primal spanning tree.

This counterexample rules out both candidate intermediate statements

```text
"D* remains a spanning tree after splitting OUT", and
"the split-outer forest has c_S components".
```

Additional boundary arcs can reconnect the split forest, but then the result
contains new edges not corresponding to omitted primal edges.  Their number
and placement require a separate convention and cannot be used in an Euler
count as though they belonged to `D*`.

## Medial contours and orthogonal turning

Take a sufficiently thin rectilinear regular neighborhood of `S`.  A connected
component `K` of cycle rank `beta_K` is a planar surface with `beta_K` holes.
Orient every outer boundary counterclockwise and every hole boundary
clockwise.  If `turn(K)` is the signed number of quarter turns, then the
orthogonal polygon turning theorem gives

```text
turn(K)=4(1-beta_K).
```

After summing over components,

```text
turn(S)=4(c_S-beta),
W=|U|+turn(S)/2.                                        (8)
```

Equation `(8)` is the exact Euler/medial-graph contribution.  It also shows
why turning number alone cannot prove a lower bound linear in `n`: the signed
turn is topological and only records `c_S-beta`; the remaining `|U|` term and
the fact that `D*` spans all cells still need a global width argument.

Geometric turns cannot replace all degree-two vertices.  In the `3 x 3`
example `(7)`, `S` is a five-vertex path.  It has two leaves and three
degree-two vertices, but only two of those three vertices are geometric turns;
the middle one is straight.  Hence

```text
W=2*2+3=7,
```

whereas the tempting leaf/turn count `2*leaves+turns` gives only `6`.  The
correct local identity counts every degree-two support vertex, straight or
turning.  For a rectilinear support tree `K`, `(3)` specializes to

```text
W(K)=|V(K)|+2,
```

which is independent of how many of its degree-two vertices turn.

Ordinary orthogonal perimeter has a similar limitation.  It depends on edge
length and on the chosen neighborhood thickness, while `W` depends only on
incidence degrees.  Signed turning has the canonical invariant `(8)`, but its
value is constant under arbitrarily long rectilinear subdivisions except for
the separately visible `|U|` term.

## Status of the width inequality

The exact unresolved statement exposed by these methods is `(4)`:

```text
sum_(support components K) (2L_K+N2_K-1) >= n+1.
```

Dual spanning says that the omitted-edge dual touches and connects all
`(n-1)^2` cells before the outer face is split.  Euler formulas, medial
turning, and rectilinear leaf identities account exactly for the left side,
but none of them converts cell spanning into the required `n+1` distinct
endpoint resources.  Any proof still needs a nonreuse theorem for rows,
columns, or medial channels.  Treating the split outer object as one tree, or
charging only geometric turns, silently assumes precisely such a theorem and
is invalid by the counterexample above.

Exhaustive enumeration of all primal spanning trees for `n=2,3,4` gives no
counterexample to `(C)`; the minimum values of `W-(n+1+c_S)` are respectively
`0,2,0`, and equality at `n=2,4` occurs with connected support.  This finite
check is evidence only, not an arbitrary-width proof.
