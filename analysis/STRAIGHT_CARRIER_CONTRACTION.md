# Straight-carrier contraction

## Result

Let `n >= 2`, let `F` be a set of vertices of the `n x n` grid, let
`U=V\F`, and put

```text
H = forcedEdgeGraph G F = G-E(G[U]).
```

Assume that `H` is acyclic. Every component of `G[F]` is a horizontal or
vertical interval; call these components **carriers**. Contract each carrier in
`H`, retaining every `U` vertex, and call the resulting graph `Q`. Isolated
`U` vertices may either be retained as isolated vertices or removed explicitly.

The contraction gives an exact local count and a branch-resolved carrier lemma,
but its direct global summation has a one-unit congestion at every branching
`U` vertex. Thus this route does not by itself prove the universal bound. The
precise obstruction already occurs in a `3 x 3` forced forest.

## 1. The contracted forest

`Q` is a bipartite forest. Its two vertex classes are the carriers and the
individual vertices of `U`; its edges are the `F-U` edges of the grid. There
are no `U-U` edges in `H`, and there are no edges between different carriers.

There is at most one edge in `Q` between a carrier `C` and a vertex `u in U`.
Indeed, two such edges, together with the path in `C` between their `F`
endpoints, would be a cycle in `H`. Any cycle in `Q` similarly lifts, by
inserting paths inside its carrier vertices, to a cycle in `H`. Hence `Q` is a
simple forest.

Write `k` for the number of nonisolated components of `Q` (equivalently, of
`H`), and `i` for the number of isolated `U` vertices.

## 2. Exact degree and boundary deficiency

For a carrier `C`, write

```text
l(C) = |C|,
B(C) = sum_{v in C} (4-deg_G(v)).
```

**Carrier degree formula.** Every carrier satisfies

```text
deg_Q(C) = 2 l(C) + 2 - B(C).                         (1)
```

**Proof.** The sum of the grid degrees on `C` is `4l(C)-B(C)`. Its `l(C)-1`
internal interval edges are counted twice, and every remaining incident edge
has its other endpoint in `U` and becomes one edge at `C` in `Q`. Therefore

```text
deg_Q(C) = 4l(C)-B(C)-2(l(C)-1)
         = 2l(C)+2-B(C).
```

This also handles a singleton, without choosing a genuine orientation. More
explicitly, if `C` is horizontal in row `r` from columns `a` through `b`, then

```text
B(C) = l(C)(1_[r=0]+1_[r=n-1]) + 1_[a=0]+1_[b=n-1],  (2)

deg_Q(C)
  = l(C)(2-1_[r=0]-1_[r=n-1])
      + 1_[a>0]+1_[b<n-1].                            (3)
```

The first term of (3) counts transverse attachments and the second counts the
two possible endpoint attachments. The vertical formula is obtained by
interchanging rows and columns. Formula (1) remains valid at corners and for
side-spanning carriers, so no boundary correction is hidden.

## 3. A branch-resolved carrier lemma

Fix a carrier `C`. Let `p(C)` be the number of its neighbors in `Q` that are
degree-one `U` vertices. Let `q(C)` be the number of carrier vertices in the
component of `Q` containing `C`.

**Lemma (private branches).**

```text
deg_Q(C)-p(C) <= q(C)-1,                               (4)
```

and hence, by (1),

```text
2l(C)+3-B(C) <= p(C)+q(C).                             (5)
```

**Proof.** Delete `C` from its tree component. Distinct edges formerly incident
with `C` enter distinct components, since a path joining two of their `U`
endpoints would complete a cycle through `C`. A branch counted by
`deg_Q(C)-p(C)` does not consist of a single degree-one `U` vertex. Since `Q`
is bipartite and has no `U-U` edges, that branch contains another carrier.
Choose one such carrier. The branches are disjoint, so these choices are
distinct and lie among the other `q(C)-1` carriers. This proves (4), and (5)
is (1) rearranged. QED

This is stronger and more explicit than merely bounding the degree of `C`: it
identifies the only uncharged attachments as private pendant `U` leaves.

## 4. Exact global congestion

For `u in U`, put `d_F(u)=|N(u) intersect F|`, and define

```text
beta = sum_{u in U} max(d_F(u)-1,0),
b    = |{u in U : d_F(u)>=2}|.
```

The quotient forest gives

```text
beta = c_F-k,                                          (6)
```

where `c_F` is the number of carriers. More importantly, summing the left side
of (4) gives the exact identity

```text
sum_C (deg_Q(C)-p(C)) = beta+b = c_F-k+b.              (7)
```

Indeed, a nonpendant `U` vertex of degree `d>=2` is counted once at each of its
`d` incident carriers. It contributes `d=(d-1)+1`, namely its contribution to
`beta` plus one. Thus the tempting global inequality

```text
sum_C (deg_Q(C)-p(C)) <= c_F-k                         (false)
```

misses exactly one unit for each branching `U` vertex. Branches are disjoint
for one fixed carrier, but not across carriers.

The smallest useful counterexample is

```text
UUU
FUF
UUU
```

in the `3 x 3` grid. The two singleton carriers share the central `U` vertex.
Each carrier has one nonpendant branch, while `c_F-k=2-1=1`. Consequently the
two sides of the false inequality are `2` and `1`. The forced graph is a tree
on seven vertices together with two isolated `U` vertices, so this is a valid
forced-acyclic example.

## 5. Row and column occupancy

Straightness also gives an exact projection ledger. If `R(C)` and `S(C)` are
the sets of rows and columns met by `C`, then

```text
|R(C)|+|S(C)|=l(C)+1,

sum_C |R(C)| + sum_C |S(C)| = |F|+c_F.                 (8)
```

In each fixed row, the intersections with carriers are exactly the `F`-runs in
that row; the analogous statement holds for columns. This records occupancy
without loss, but it supplies no multiplicity control for (7): the branching
vertex in the displayed counterexample is compatible with all row and column
run constraints.

## 6. Relation to the universal bound

Let `B_U=sum_{u in U}(4-deg_G(u))`. Since the total boundary deficiency of the
square is `4n`, the forest component ledger rewrites the desired inequality

```text
3|F|+4 <= n^2+3n
```

exactly as

```text
B_U+c_F+c_H >= n+4,                                   (9)
```

where `c_H=i+k` includes isolated `U` components. Equivalently,

```text
B_U+c_F+i+k >= n+4.                                   (10)
```

Proof of the equivalence: the forced-forest Euler identity is

```text
3|F|+c_F+c_H=n^2+B_F,
```

and `B_F+B_U=4n`; substitution and cancellation gives (9).

Equations (1), (6), (7), and (8) are the exact direct degree, forest, and
row/column occupancy ledgers developed here. Their global use leaves the
positive congestion term `b`, or equivalently the private pendant terms in
(5). Removing either without a new geometric argument is invalid. Therefore
the contraction yields the rigorous stronger local lemma (4)-(5), but not a
proof of (9).

## 7. Computational validation

`straight_carrier_count.py` independently constructs `H`, its carriers, and
`Q`. For every input it asserts straight intervals, quotient acyclicity,
(1), (4), (6), (7), and (8). It exhaustively checks all forced-acyclic sets
through the requested width and reports the first counterexample to the false
global summation.

Run:

```bash
python3 -m unittest discover -s analysis -p 'test_straight_carrier_count.py'
python3 analysis/straight_carrier_count.py --brute-max-n 4
```

These checks are finite validation only; the proofs above establish the carrier
identities and private-branch lemma for arbitrary `n`.

The exhaustive run checked `9`, `100`, and `2,278` forced-acyclic sets at
`n=2,3,4`, respectively. Every carrier assertion passed. There were no failures
of the universal target in this finite range. The traversal's first failure of
the false global branch sum is the boundary variant

```text
FUF
UUU
UUU
```

with the same values `2 > 1`; the interior example in Section 4 makes the
branch-overlap geometry more symmetric.
