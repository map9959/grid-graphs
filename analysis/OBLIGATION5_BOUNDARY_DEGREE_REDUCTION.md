# Obligation 5: boundary-degree reduction

This note concerns only the old residue-two baseline. Let `G` be the plane
`n x n` grid, let `U` be a set of primal vertices, and suppose that the dual
edges of all primal `U-U` edges connect every bounded face to `OUT`. Put

```text
rho = (n-1)^2,
K(U) = 3|U| - 2rho - n.
```

The desired assertion for `n=3k+2`, `k>=1`, is `K(U)>=5`.

## 1. Congruence reduction

Since `n=2 (mod 3)` and `rho=(n-1)^2=1 (mod 3)`, one has

```text
K(U) = -2rho-n = 2 (mod 3).
```

Consequently it is enough, and necessary, to exclude `K(U)<=2`. This wording
matters: congruence alone does not exclude `..., -4, -1, 2`.

## 2. Run identity

Let `R` be the total number of nonempty maximal `U`-runs over all rows and
columns, and let `beta` be the cycle rank of the full `U-U` dual graph. If `E`
is its edge count, then

```text
E = 2|U|-R,
E = rho+beta,
K(U) = 2R+2beta-|U|-n.
```

These are exact, but they do not by themselves constrain how the connected
dual graph reaches `OUT`. The following equivalent form retains precisely that
information.

## 3. Exact tree-cotree budget identity

Choose any spanning tree `D` of the connected `U-U` dual graph. Regard its
edges as primal grid edges, and let

```text
T = G minus the primal edges dual to D.
```

By plane tree-cotree duality, `T` is a primal spanning tree. Every edge removed
from `G` has both endpoints in `U`; hence every vertex outside `U` has full grid
degree in `T`.

For a boundary vertex `v`, assign its number of incidences with the four sides
of the square:

```text
q(v) = 0  for an interior vertex,
q(v) = 1  for a noncorner boundary vertex,
q(v) = 2  for a corner.
```

Define the boundary-port count and the `U`-degree excess by

```text
Q = sum_{u in U} q(u),
S = sum_{u in U} (deg_T(u)-1).
```

Both are nonnegative integers. Then

> **Boundary-degree identity.** `K(U)=Q+S-n`.

Proof. The tree `D` has `rho` edges. If `d_D(u)` is the number of their primal
representatives incident with `u`, double counting endpoints gives

```text
2rho = sum_{u in U} d_D(u).
```

The complementary-tree definition and `deg_G(u)=4-q(u)` give

```text
d_D(u)
  = deg_G(u)-deg_T(u)
  = 3-q(u)-(deg_T(u)-1).
```

Summing over `U` yields `2rho=3|U|-Q-S`, and rearrangement proves the
identity. In particular, although the individual degree-excess summands can
change with the chosen dual spanning tree, their total `S` is forced to be
`K+n-Q`. Thus no optimization over `D` is hidden in the statement.

The identity is also an exact symbolic bridge between the two requested
languages:

```text
2R+2beta-|U|-n = Q+S-n.
```

Here `Q` records boundary sites available to dual `OUT` ports, while `S` is the
total degree capacity left in the complementary primal tree after reserving one
tree edge at every `U` vertex.

## 4. Dual-tree incidence waste

The same identity has a choice-free form. Let `D` be the selected dual
spanning tree and let `d(v)` count its primal edge representatives incident
with a primal vertex `v`. A dual tree cannot contain every edge surrounding a
primal vertex, so `0<=d(v)<=3`. If `N_j` counts vertices with `d(v)=j`, then

```text
Q+S = sum_(d(v)>0) (3-d(v)) = 2N_1+N_2.
```

Indeed, the support `U_0={v:d(v)>0}` minimizes `Q+S`; adding a vertex with
`d(v)=0` adds exactly three. Double counting the endpoints of the `(n-1)^2`
tree edges gives the displayed equality. Thus the universal first step is
exactly the incidence-waste inequality

```text
2N_1+N_2 >= n+2.
```

For `n=3k+2`, equality must then be excluded; congruence promotes strictness to
`2N_1+N_2>=n+5`. This formulation removes the auxiliary choice of `U`, but the
geometric inequality remains unproved.

## 5. Exact forced-forest component decomposition

There is also an exact formulation with no chosen tree. Put `F=V(G)\U` and

```text
H = G minus E(G[U]).
```

Dual connectivity is equivalent to `H` being a spanning forest. Let `c_F` be
the number of components of the induced graph `G[F]`, including isolated full
vertices, and let `c_H` be the number of spanning components of `H`, including
isolated U vertices. Let `Q_U` be the boundary-side incidence count of U, so
the corresponding count on F is `4n-Q_U`.

Since both `G[F]` and `H` are forests,

```text
|E(G[F])| = |F|-c_F,
|E(H)| = n^2-c_H.
```

On the other hand, summing grid degrees over F counts every F-F edge twice and
every F-U edge once, hence

```text
|E(H)| = 4|F|-(4n-Q_U)-|E(G[F])|.
```

Eliminating the edge counts and using `|U|+|F|=n^2` gives

```text
K(U) = Q_U+c_F+c_H-n-2.
```

Consequently the two exact geometric targets are

```text
Q_U+c_F+c_H >= n+4                              (universal K>=2),
Q_U+c_F+c_H >= n+7  when n=3k+2, k>=1.          (obligation 5)
```

The committed curvature-five controls make the second inequality sharp. Their
triples `(Q_U,c_F,c_H)` at `n=5,8,11,14` are respectively
`(7,4,1)`, `(6,8,1)`, `(5,11,2)`, and `(5,14,2)`.
`residue_two_obligation5_components.py` checks the decomposition independently.

This component form explains why an edge-count lower bound alone fails:
boundary-heavy examples may have cheap edge count but compensate with many
components of `G[F]` or `H`. The missing theorem must retain all three terms.

The exact basis-exchange formula and two rejected attempts to globalize it are
recorded in `INCIDENCE_WASTE_EXCHANGE.md`. In particular, a full-side path need
not lie in the complementary primal tree, and an owner-pair Hall condition that
counts only boundary-owning `H` components is false. The corrected global Hall
target is just the exact component inequality above; it supplies no proof by
itself.

## 6. The exact missing lemma

After the identities above, the entire obligation is reduced to the following
single geometric statement.

> **Low-budget tree-cotree exclusion (missing).** Let `n=3k+2`, `k>=1`.
> There is no spanning tree `T` of the `n x n` grid and vertex set `U` such
> that (i) every edge outside `T` has both endpoints in `U`, (ii) the duals of
> the edges outside `T` form a dual spanning tree, and
> `Q+sum_(u in U)(deg_T(u)-1)<=n+2`.

This is smaller than a general frontier-coverage lemma: it concerns one primal
tree, has no width-sized state, and only has to rule out the low budget. It is
also exact. Given the missing lemma, the boundary-degree identity excludes
`K<=2`; the congruence then gives `K>=5`. Conversely, any counterexample with
`K<=2` supplies the forbidden pair by choosing a dual spanning tree. Therefore
none of the remaining difficulty has been concealed in a one-way relaxation.

A possible two-step strengthening would be

```text
Q+S >= n+2 for every square,                         (A)
Q+S = n+2 implies n is not 2 modulo 3.              (B)
```

Neither (A) nor (B) is proved in the repository, so they must not be used as
lemmas. The combined low-budget exclusion above is the smallest exact missing
claim needed here.

## 7. Candidate lemmas explicitly rejected

The following shortcuts cannot be claimed.

1. **Boundary ports alone pay the constant.** The claim `Q>=n+5` is false.
   Direct counts on the committed connected equality patterns give
   `Q=6,5,5,5` at `n=5,8,11,14`, respectively.
2. **Degree excess alone pays the width.** The claim `S>=n` is false. Since the
   same patterns have `K=5`, the exact identity gives
   `S=4,8,11,14`; the `n=5` value is already a counterexample.
3. **A dual cycle is forced at equality.** This is false: the committed `n=5`
   and `n=8` equality patterns have `beta=0`.
4. **Planarity bounds the raw boundary word by a constant.** This is false.
   Noncrossing nested component intervals can be arbitrarily numerous, and the
   committed affine `A23` control already violates the old `4/3/9` signature.
   Planarity only forbids alternating `A,B,A,B` occurrences for disjoint
   connected components.
5. **A component has contiguous packet support.** This is false at `n=11`: an
   exact curvature-five path has one component in packet groups 1 and 3 but not
   2, and the next row reconnects the silent carrier.
6. **A scalar row potential suffices.** Exact complete `n=5,n=8` transitions
   falsify each of `weight>=Delta(debt)`,
   `weight>=Delta(branch_cost)`, and
   `weight>=Delta(debt+branch_cost)`. The pooled run/countdown quotient also
   drops the `n=8` terminal constant from five to two.
7. **Every full boundary side is a path in the complementary tree.** This is
   false because the dual tree needs at least one edge incident with `OUT`, and
   every such edge removes its primal boundary representative from the
   complementary tree.
8. **Boundary incidences admit a Hall charge to only their owning `G[F]` and
   `H` components.** This fails on the four-boundary-segment family for every
   `n>=17`; the many interior isolated components of `H` carry the missing
   charge. See `INCIDENCE_WASTE_EXCHANGE.md`.

Items 1--3 are direct counterexamples to tempting consequences of the new
identity. Items 4--8 explain why replacing the missing low-budget cut lemma by
the repository's failed bounded-port, row-local, or side-owner arguments is
invalid.

## 8. What a proof of the missing lemma must use

Any successful proof has to couple `Q` and `S`. A boundary port can be cheap
only if the complementary tree carries the corresponding interior attachment;
branching or merging that attachment is measured by `deg_T(u)-1`. Conversely,
small `S` forces most `U` vertices to be leaves of `T`, so nested dual branches
must be separated by planar cuts and eventually paid at boundary incidences.

The currently proved port inequality

```text
branch_cost <= perimeter_ports - ported_components
```

does not yet provide this coupling, and the centered identity

```text
M_s-(s-1)^2 = (q_s-d_s)+beta_s
```

does not telescope to `Q+S>=n+3` without an additional statement charging a
component that survives a cut either to a final boundary incidence or to a
distinct unit of primal-tree degree excess. Establishing exactly that injective
cut charge, under the low total budget `Q+S<=n+2`, is the unresolved
width-independent step.

## 9. Executed direct-proof program

`DIRECT_PROOF_EXECUTION_STATUS.md` records the completed attempt to execute the
boundary-peeling, multi-exchange, equality-phase, and construction program. The
comb, arbitrary-exchange, maximality, and radial-ledger foundations are now
proved. Exact counterexamples rule out scalar annular telescoping and
owner-local component charging. The remaining universal step is a
boundary-rooted two-forest rank theorem coupled to a component-resolved
inherited potential; neither statement is claimed proved.
