# Incidence-waste exchange ledger

This note records the direct spanning-tree facts that are currently proved and
separates them from two tempting but invalid boundary arguments.  Let `D` be a
spanning tree of the plane dual of the `n x n` grid.  For a primal vertex `v`,
let `d_D(v)` be the number of primal representatives of edges of `D` incident
with `v`, and put

```text
W(D) = sum_(d_D(v)>0) (3-d_D(v)).
```

The primal edges incident with a vertex trace a dual cycle, with the boundary
cases using `OUT` and possibly parallel dual edges.  A dual tree cannot contain
that complete cycle, so `0<=d_D(v)<=3`.  If
`N_j=|{v:d_D(v)=j}|`, endpoint counting gives

```text
W(D) = 2N_1+N_2
     = 3|supp(D)|-2(n-1)^2.
```

The desired universal first step is `W(D)>=n+2`.

## 1. Exact basis-exchange formula

Let `f` be an edge of `D`, and let `e` be a non-tree edge crossing the
fundamental cut of `f`, so `D'=D-f+e` is again a dual spanning tree.  Ignore
primal endpoints shared by the representatives of `e` and `f`, because their
incidence degrees do not change.  Among the remaining endpoints, let

```text
a = number of endpoints of e having d_D=0,
r = number of endpoints of f having d_D=1.
```

Then

```text
W(D')-W(D) = 3(a-r).
```

Proof.  At an unshared removed endpoint, decreasing a degree at least two adds
one to `W`, while changing `1` to `0` subtracts two.  Thus a removed degree-one
endpoint differs by `-3` from the baseline contribution `+1`.  At an unshared
added endpoint, increasing a positive degree subtracts one, while changing
`0` to `1` adds two.  Thus a newly supported endpoint differs by `+3` from the
baseline contribution `-1`.  There are equally many unshared added and removed
endpoints, so the baseline terms cancel.

Consequences for a tree minimizing `W` within its dual graph:

* Every valid exchange satisfies `a>=r`.
* If `f` is the unique selected edge incident with a vertex `x`, then every
  edge crossing the fundamental cut of `f` either is incident with `x` or has
  a previously unsupported endpoint.  Otherwise the exchange has `r>=1` and
  `a=0`.
* More generally, any exchange that removes two unshared degree-one endpoints
  must introduce at least two unsupported endpoints.

These are exact local saturation constraints.  They do not yet bound how many
fundamental cuts can charge the same unsupported endpoint.

## 2. Complementary-tree ledgers

Let `T` be the primal tree complementary to `D`, let `U=supp(D)`, and define

```text
Q = sum_(u in U) q(u),
S = sum_(u in U) (deg_T(u)-1),
```

where `q` is zero in the interior, one on a noncorner side vertex, and two at a
corner.  Every vertex outside `U` has its full grid degree in `T`, and

```text
W(D)=Q+S.
```

If `f_i` and `f_e` count, respectively, interior and noncorner boundary
vertices outside `U`, then the tree degree sum gives the exact leaf/branch
ledger

```text
S = |U|-2-2f_i-f_e.
```

Indeed, `sum_v(deg_T(v)-2)=-2`.  The contribution from `U` is `S-|U|`, while
full interior, noncorner boundary, and corner vertices outside `U` contribute
`2`, `1`, and `0`.

For any vertex set `A` in a tree, if `q_T(A)` is the number of tree edges
crossing its cut, then

```text
q_T(A)=c(T[A])+c(T[V\A])-1.
```

This follows by contracting every component induced on each side of the cut.
It is useful exact bookkeeping, but a nested sequence of such cuts need not
have monotone surplus.

## 3. Invalid full-side path argument

A previously proposed side identity started by taking, for each side, the full
`n-1`-edge boundary path as a subpath of `T`.  That premise is unavailable.  A
dual spanning tree must contain an edge incident with `OUT`; its primal
representative is a boundary edge omitted from `T`.  It may omit several
boundary edges, potentially on several sides.  Therefore the four full side
paths cannot all be subpaths of `T`, and no four-side telescoping argument may
use that identity without first replacing the broken sides by a rigorously
defined path-segment decomposition.

## 4. Failed owner-pair Hall target

In the forced-forest formulation, put `F=V(G)\U` and
`H=G-E(G[U])`.  An unconditional proposed Hall condition assigned each
boundary incidence of `F` to its component of `G[F]` and its component of `H`,
then asked for

```text
|X| <= 3n-4 + |phi_F(X)| + |phi_H(X)|
```

for every set `X` of boundary incidences.  This is false because components of
`H` not owning boundary incidences can carry most of the required charge.

For a reproducible family, take all vertices to be `U` except:

* the noncorner vertices on the left and right sides;
* columns `2,...,n-3` on the top and bottom sides.

Those full vertices form four path components, and `H` is a forest.  For the
set `X` of all their boundary incidences,

```text
|X|=4n-12,
|phi_F(X)|=4,
|phi_H(X)|=4.
```

Thus the proposed inequality becomes `4n-12<=3n+4`, which fails for `n>=17`.
At `n=17`, the exact component checker gives
`(Q_U,c_F,c_H)=(12,4,173)`: the 169 omitted owner components explain the
failure.

The corrected global target must retain every component of `H`:

```text
4n-Q_U <= 3n-4+c_F+c_H,
```

equivalently

```text
Q_U+c_F+c_H >= n+4.
```

By the exact component identity, this is precisely `W(D)>=n+2`; it is a clean
restatement, not yet a proof.  Any refined matching argument must either charge
the formerly unowned `H` components or prove an independent bound that pays for
discarding them.
