# Forest extremal induction

## 1. Problem and outcome

Let `G=G_n` be the `n x n` grid, with `n>=2`.  Partition its vertices as `F union U` and
put

```text
H = G-E(G[U]).
```

Thus every edge having an endpoint in `F` belongs to `H`.  The hypothesis is
that `H` is a spanning forest.  The desired universal bound is

```text
3|F| <= n^2+3n-4.                                      (T)
```

I did not obtain a proof of `(T)`.  This note gives an independent reduction,
proves an exact minimal-counterexample exchange rule, and rules out several
natural boundary-row and local-discharge inductions.  The final static lemma
in Section 8 is a strictly narrower sufficient target: it only concerns
forests satisfying an explicit repeated-component-label condition at every
`U` vertex.  It contains no extremal quantity or inductive hypothesis.

The notation here takes `F` to be the set whose size is being bounded.  This is
the complement of the support set called `U` in the incidence-waste notes.

## 2. Two exact contractions

Let `b_F` be the boundary deficiency of `F`: a noncorner boundary vertex of
`F` contributes one and a corner contributes two.  Let `c_F` be the number of
components of `G[F]` and `c_H` the number of components of `H`, with isolated
vertices included.

Because `G[F]` is a subgraph of `H`, it is a forest and

```text
|E(G[F])|=|F|-c_F.
```

Summing grid degrees over `F` counts an `F-F` edge twice and an `F-U` edge
once.  Since `sum_(f in F) deg_G(f)=4|F|-b_F`, this gives

```text
|E(H)| = 4|F|-b_F-|E(G[F])|
       = 3|F|+c_F-b_F.
```

On the other hand, the spanning forest identity is `|E(H)|=n^2-c_H`.
Consequently

```text
3|F| = n^2+b_F-c_F-c_H.                               (1)
```

This independently recovers the boundary-component ledger.  In particular,
`(T)` is equivalent to

```text
b_F <= 3n-4+c_F+c_H.                                  (BC)
```

There is a second useful contraction.  Contract every component of `G[F]` in
`H`.  The result has one vertex for each `F` component and one vertex for each
original `U` vertex; its edges are precisely the `F-U` edges.  It is a forest,
including all isolated vertices, and hence

```text
c_H=c_F+|U|-e(F,U).                                    (2)
```

In particular, no two `F-U` edges can join the same `F` component to the same
`U` vertex, and the component-incidence graph has no alternating cycle.  This
is the component-incidence-tree version of comb separation, with no boundary
chosen.

Equations `(1)` and `(2)` are exact bookkeeping, not a proof of `(BC)`.

## 3. Why direct deletion of one side fails

A plausible rectangular strengthening is

```text
3|F| <= mn+2 min(m,n)+max(m,n)-4.                      (R)
```

It specializes to `(T)`.  When `m<=n`, deleting an outer row changes the
right side of `(R)` by `n+2`.  A clean induction would therefore need an outer
row containing at most `(n+2)/3` vertices of `F`.

That local rule is false even after the standard minimal-counterexample
normalization in Section 5.  The following `5 x 5` pattern writes `U` as `U`
and `F` as `.`:

```text
....U
UUUUU
.UUU.
.UUU.
.U.U.
```

Its four side `F` counts are `(4,3,4,3)`, all greater than `7/3`.  The forced
graph is a forest, and changing any one `U` vertex to `F` creates a cycle.
Thus choosing a counterexample maximal in `F` does not rescue cheap-side
deletion.

There is also a scalable, nonmaximal obstruction.  Take as `F` the noncorner
vertices of the left and right sides and columns `2,...,n-3` of the top and
bottom sides.  The four `F` segments and their inward teeth form disjoint
trees, so `H` is a forest.  For every `n>=8`, every side has more than
`(n+2)/3` vertices of `F`.  The checker verifies this family through `n=19`.

Deleting a whole outer layer has the exact merger ledger in
`BOUNDARY_PEELING_LEMMAS.md`, but its increment can be negative: the displayed
`4 x 4` example there has `L_4-L_2=-4`.  Hence neither a row, a column, nor an
annulus has to pay its own share of `(T)`.  Any valid peeling proof must carry
inherited component surplus, not only the current boundary word.

## 4. Forest orientation and the limit of local discharging

Root every component of `H` and orient its edges away from the root.  A vertex
of `F` has its full grid degree in `H`, so it sends at least
`deg_G(v)-1` edges away from itself.  Since each nonroot receives one edge,

```text
sum_(v in F) (deg_G(v)-1) <= n^2-c_H,
3|F|-b_F <= n^2-c_H.                                  (3)
```

Retaining the extra root forced by each component of `G[F]` sharpens `(3)` to
equality `(1)`.  Thus the natural `3`-unit discharge from an `F` vertex reaches
exactly the boundary-component bottleneck and no farther.

Several tempting local ways to finish this discharge are false:

* A forest-valid configuration need not have a boundary side of low `F`
  density, as Section 3 shows.
* Maximality does not give every `U` vertex two `U` neighbors.  The maximal
  `3 x 3` pattern `UU./UUU/...` has only one `U` neighbor at `(1,2)`.
* There need not be an `F` corner, or a boundary `F` vertex of grid degree two.
  In `U.U/U.U/U.U`, all four corners are `U`, while `H` is a forest.
* Charges cannot be assigned independently on the two chessboard colors.
  An arbitrarily long component of `G[F]` can alternate colors while using
  only one component credit, and the incidence contraction `(2)` allows a
  `U` vertex to join several different `F` components.  Forestness prohibits
  a repeated component at that one `U`, but gives no local bound on the number
  of different components.

The orientation calculation explains these failures: local degree charge has
already spent all information except `b_F,c_F,c_H`.

## 5. Exact one-vertex exchange

The forced-forest property is downward closed in `F`: changing an `F` vertex
to `U` only deletes edges from `H`.  The reverse move has an exact test.

**Exchange lemma.**  Let `u in U`, and let `C(v)` denote the component of `v`
in the current forest `H`.  Changing `u` from `U` to `F` preserves forestness
if and only if the labels in the multiset

```text
{C(u)} union {C(v): v in N_G(u) intersect U}           (4)
```

are all distinct.

**Proof.**  The move adds exactly the formerly absent edges `uv` with
`v in N(u) intersect U`.  Contract every component of the old `H`.  The new
edges become a star centered at `C(u)`.  They create no cycle exactly when no
edge is a loop and no two leaves have the same contracted endpoint.  Those
are precisely the assertions that all labels in `(4)` are distinct.  Lifting
the contraction preserves cycles.  QED

This also identifies both ways an attempted move can fail:

1. some `U` neighbor of `u` already lies in `C(u)`; or
2. two distinct `U` neighbors of `u` lie in the same other component of `H`.

The second case is easy to miss in a rule considering each new edge
separately.

## 6. Minimal-counterexample normal form

Suppose `(T)` is false and choose a counterexample with `|F|` maximal.  It has
the following static properties:

```text
(M1) H is a forest;
(M2) 3|F|>n^2+3n-4;
(M3) for every u in U, the labels in (4) contain a repetition.
```

Indeed, if `(M3)` failed, the exchange lemma would produce a valid set with
one more `F` vertex, and that set would still violate `(T)` more strongly.

Conversely, any forest can be extended greedily until `(M3)` holds.  Therefore
it is enough to prove `(T)` under `(M3)`: an arbitrary `F` extends to a maximal
`F'`, and a bound on `|F'|` bounds `|F|`.

Condition `(M3)` is stronger and more precise than a minimum-degree statement.
It permits a `U` leaf in `G[U]` when its unique omitted edge closes a path
already present in `H`; this is exactly what occurs in the `3 x 3`
counterexample to the two-neighbor rule.

## 7. Interaction with tree exchange

The exchange lemma is independent of choosing a complementary primal or dual
spanning tree.  It is nevertheless parallel to the basis-exchange formula in
`INCIDENCE_WASTE_EXCHANGE.md`:

* basis exchange minimizes the support of one selected dual tree and forces a
  protector for every removable private endpoint;
* vertex exchange maximizes `F` in the full forced forest and forces a repeated
  `H`-component label around every `U` vertex.

Neither statement bounds congestion.  In the first, one unsupported endpoint
can protect many fundamental cuts.  In the second, one `H` component can
witness `(M3)` at many `U` vertices.  Rooted laminarity does not fix this: a
single component path can revisit many vertex neighborhoods without making an
alternating cycle in the contracted incidence forest.

Thus a putative injection from maximal `U` vertices to components must include
a geometric noncongestion argument; maximality alone supplies no injection.

## 8. Smaller sufficient lemma

The full theorem is reduced to the following statement.

> **Repeated-label boundary lemma.**  Let `H=G_n-E(G_n[U])` be a forest.  Write
> `F=V-U`, and label every grid vertex by its component of `H`.  Suppose that
> for each `u in U`, the component labels on
> `{u} union (N(u) intersect U)` are not all distinct.  Then
>
> ```text
> b_F <= 3n-4+c(G_n[F])+c(H).                           (RL)
> ```

This is sufficient by Section 6 and identity `(1)`.  It is narrower than the
original problem in two useful senses: it only concerns inclusion-maximal
valid configurations, and its hypothesis is locally checkable once the
forest components are contracted.  It is noncircular: `(RL)` mentions no
cardinality of `F`, no dual tree, and no induction surplus.

A proof still needs one genuinely global fact.  Each boundary incidence above
the free allowance `3n-4` must be charged to an `F` component or an `H`
component, while repeated labels from `(M3)` must prevent the same component
from accepting too many such charges.  The incidence forest `(2)` gives the
right no-alternating-cycle constraint, but no bounded-congestion map has been
established.  This is smaller than the previous annular goal because it avoids
arbitrary merger histories and only treats the saturated endpoint of greedy
extension.

## 9. What a viable induction must retain

The checks and exact formulas impose the following requirements on any future
proof.

1. A rectangular or concentric induction must carry component surplus.  A
   scalar boundary density or fixed `+2` annular increment is false.
2. A minimal-counterexample proof should use the repeated-label alternatives
   in `(M3)`, not replace them by `deg_U(u)>=2`.
3. A discharging proof must charge whole contracted `F` and `H` components;
   vertex degree and chessboard color alone collapse to identity `(1)`.
4. Any exchange proof needs a congestion lemma.  The existence of an exchange
   protector or a repeated component label is only the local half.

One potentially useful next step is to place the component labels of `H` on
the cyclic boundary, contract each maximal equal-label interval, and prove a
noncrossing bound specifically under `(M3)`.  Unlike the false owner-pair Hall
rule, such a bound must retain components of `H` with no boundary incidence,
because they can supply the repeated labels that certify interior saturation.

## 10. Computational checks

`check_forest_extremal_induction.py` performs the following independent tests:

* exhaustive verification of the exchange lemma for every forest-valid binary
  pattern through `n=4`;
* validity, maximality, and side counts of the `5 x 5` cheap-side
  counterexample;
* the maximal `U`-degree-one and no-`F`-corner counterexamples; and
* the scalable four-boundary-segment family for `8<=n<=19`.

Run it with

```bash
PYTHONPATH=analysis python3 -m unittest check_forest_extremal_induction
```
