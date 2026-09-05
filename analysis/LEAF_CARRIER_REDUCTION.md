# Leaf-carrier reduction for the forced forest

## 1. Setup and outcome

Let `G=G_n`, `n>=2`, partition `V(G)=F disjoint-union U`, and put

```text
H=G-E(G[U]).
```

Assume that `H` is a forest. Contract every component of `G[F]`, but retain
the individual `U` vertices. The resulting bipartite incidence graph `J` is a
forest. Its carrier vertices are the components of `G[F]`.

There are two different notions of leaf in this setting.

* No carrier is literally a leaf of `J`. Every nonempty carrier has degree at
  least two.
* Delete from `J` the `U` vertices of degree zero or one. In the remaining
  carrier core, some carrier has degree at most one. Such a pruned-leaf carrier
  has many private `U` leaves, with an exact lower bound below.

The second statement is a genuine reducible-configuration theorem, but its
charge is insufficient at boundary-parallel intervals. A scalable family of
four disjoint boundary combs has only pruned-leaf carriers and every carrier
has an arbitrarily large local deficit. For `n>=8` it also has no favorable
one-row strip, and for `n>=11` no favorable side together with its adjacent
row. Thus the proposed leaf-carrier induction does not prove the sharp bound
without an additional inherited boundary or component surplus.

## 2. Exact carrier degree

Every component `C` of `G[F]` is a straight horizontal or vertical interval.
Write

```text
ell = |C|,
q(C) = sum_(v in C) (4-deg_G(v)),
d(C) = deg_J(C).
```

The absence of parallel edges in the forest `J` means that distinct `F-U`
edges incident with `C` have distinct endpoints in `U`. Hence `d(C)` is both
the number of `F-U` edges incident with `C` and the number of neighboring `U`
vertices. Degree summation on the interval gives

```text
2(ell-1)+d(C)=4ell-q(C),
```

and therefore

```text
d(C)=2ell+2-q(C).                                      (1)
```

The possible boundary cases are as follows. Reflections and exchanging rows
with columns are understood.

| position of `C` | `q(C)` | `d(C)` |
|---|---:|---:|
| disjoint from the boundary | `0` | `2ell+2` |
| transverse, with one noncorner endpoint on the boundary | `1` | `2ell+1` |
| transverse, joining two opposite sides away from corners | `2` | `2ell` |
| along one side, containing no corner | `ell` | `ell+2` |
| along one side, containing one corner | `ell+1` | `ell+1` |
| the whole side | `ell+2` | `ell` |
| a corner singleton | `2` | `2` |

These cases include all endpoint degeneracies. An interval that meets two
adjacent sides is either contained in one of them or is the common corner
singleton. In particular,

```text
d(C)>=2.                                               (2)
```

Thus a theorem asserting that the contracted incidence forest has a carrier
leaf is false in every nonempty case, not merely at an exceptional boundary
configuration. For example, in the `2 x 2` pattern

```text
FF
UU
```

the unique carrier has degree two and the two leaves of `J` are `U` vertices.

## 3. The valid pruned-leaf theorem

Call a neighboring `U` vertex of a carrier private when it has degree one in
`J`. Equivalently, it is a leaf of `H` attached to that carrier. Let `J_core`
be obtained from `J` by deleting all `U` vertices of degree at most one; retain
all carriers, including isolated ones.

**Proposition 3.1.** If `F` is nonempty, some carrier `C` has degree at most one
in `J_core`.

**Proof.** The graph `J_core` is a finite forest. Every retained `U` vertex has
degree at least two, since all its carrier neighbors were retained. If every
carrier also had degree at least two, every vertex of every nonempty component
of `J_core` would have degree at least two, impossible for a finite forest. If
`J_core` has an isolated carrier, that carrier already has degree zero. QED

Let `t` be this carrier's degree in `J_core` and let `a` be its number of
private neighboring `U` vertices. Since all other neighbors are exactly the
vertices counted by `t`, equations (1) and `t<=1` give

```text
a=d(C)-t >= 2ell+1-q(C).                               (3)
```

This is sharp: one may have `t=1` and equality in (3). It gives the following
rigorous favorable cases.

* If `q(C)=0`, then `a>=2ell+1`.
* If `q(C)=1`, then `a>=2ell`.
* Removing the packet consisting of `C` and its private leaves removes `ell+a`
  vertices, of which `ell` are forced. Thus ordinary area charge pays the
  three units per forced vertex whenever `a>=2ell`, in particular whenever
  `q(C)<=1`.
* In general the unpaid local amount is bounded exactly by

```text
3ell-(ell+a) <= q(C)-1.                                (4)
```

The packet deletion in the last two bullets is only local accounting. It
usually leaves a punctured grid, so the square or rectangular induction
hypothesis cannot be applied to the remainder without a theorem for such
domains. Formula (4) identifies what that stronger theorem would have to
carry: boundary-parallel intervals may consume almost all of `q(C)-1`.

## 4. Boundary counterexamples

For every `n>=8`, let `F` consist of

```text
{(r,c) : 1<=r<=n-2 and c in {0,n-1}}
union
{(r,c) : r in {0,n-1} and 2<=c<=n-3}.
```

Thus the left and right carriers have length `n-2`, and the top and bottom
carriers have length `n-4`; none contains a corner. Their forced stars are
four disjoint comb trees. No `U` vertex is adjacent to two carriers, so `H` is
the disjoint union of those trees and isolated `U` vertices. In particular,
`H` is a forest, every carrier is isolated in `J_core`, and all of its adjacent
`U` vertices are private.

For a top or bottom carrier,

```text
ell=n-4,       q(C)=ell,       a=d(C)=ell+2=n-2.
```

Consequently

```text
2ell-a=n-6.                                           (5)
```

The private leaves fail to pay the carrier's local area cost by an amount
growing linearly with `n`. Hence the strengthening

> every nonempty forced forest has a pruned-leaf carrier with `a>=2|C|`

is false, even when every carrier is a pruned leaf and every attachment is
private.

The same family rules out the natural strip repairs. For the plausible sharp
rectangular strengthening

```text
3|F| <= mn+2 min(m,n)+max(m,n)-4,                      (R)
```

the right side decreases by `n+2` when one side row is removed from an `n x n`
square. A favorable row would therefore need

```text
3|F intersect row| <= n+2.
```

Every side has at least `n-4` forced vertices, and
`3(n-4)>n+2` for `n>=8`. Thus no one-row boundary strip is favorable.

Removing a side row and its adjacent row changes the right side from the
square value `n^2+3n-4` to the `(n-2) x n` value `n^2+n-8`, a decrease of
`2n+4`. The top two rows of the displayed family contain `n-2` forced
vertices: the top carrier and one vertex from each side carrier. Therefore

```text
3(n-2)>2n+4
```

for `n>=11`. Even deleting the whole adjacent strip containing all inward
teeth of the top carrier is then unfavorable. Deleting only the carrier and
its private `U` neighbors avoids those two side vertices, but leaves a
nonrectangular punctured domain and has the deficit (5).

## 5. Consequence for induction

The leaf-carrier approach separates into a proved part and a false part.

**Proved reducible configuration.** There is always a straight carrier with at
most one nonprivate `U` attachment, and it has at least
`2|C|+1-q(C)` private leaves. Carriers with `q(C)<=1` have sufficient local
area charge.

**False universal strengthening.** One cannot always choose such a carrier
with enough private charge to absorb its forced vertices, nor can one repair
this by deleting one or two complete adjacent strips. Boundary-parallel combs
give unbounded deficits.

A viable induction must therefore retain at least one nonlocal quantity, such
as inherited boundary deficiency or the component surplus already exposed by
the annular ledger. Leaf pruning alone forgets exactly the resource needed to
pay (4).
