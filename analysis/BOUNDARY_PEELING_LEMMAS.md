# Boundary peeling and comb separation

This note uses only the following forced-forest formulation.  Let `G_n` be the
simple `n x n` grid, let `U` be a set of vertices, put `F=V(G_n)\U`, and set

```text
H = G_n - E(G_n[U]).
```

Thus an edge is in `H` exactly when at least one endpoint is in `F`.  The
hypothesis throughout is that `H` is a forest.  This is the condition relevant
to a support set of a complementary dual tree.  No connectivity of `H` or of
`G_n[F]` is assumed.

For any graph `K`, `c(K)` denotes its number of nonempty connected components;
in particular `c(empty graph)=0`.  Write

```text
c_H = c(H),                    c_F = c(G_n[F]).
```

For `v=(i,j)`, define its boundary deficiency

```text
q_n(v) = 4-deg_G_n(v).
```

It is `0` in the interior, `1` at a noncorner boundary vertex, and `2` at a
corner.  Set `Q_U=sum_(u in U) q_n(u)`.  This definition includes all four
corners with multiplicity two.  If `F` has no boundary vertex, every boundary
quantity involving `F` below is zero; no fictitious empty component is added.

## 1. The comb-separation lemma (proved)

Here is the graph-theoretic fact used by the peeling calculation.

**Lemma.** Let `K` be a forest whose vertices are partitioned into `B` and `I`.
Let `P_1,...,P_p` be the components of `K[B]` and `C_1,...,C_c` the components
of `K[I]`.  Form a bipartite multigraph `J_K` with these `p+c` components as
vertices and one edge for every edge of `K` between `B` and `I`.  Then `J_K` is
a forest.  Consequently:

1. no two crossing edges join the same pair `(P_i,C_j)`;
2. there is no alternating cycle of boundary and inner components; and
3. if `t` is the number of crossing edges, then

```text
c(K) = c + p - t.                                      (1)
```

The `P_i` may be viewed as comb backbones and the crossing edges as teeth.  In
particular, two teeth of one backbone cannot end in the same inner component.

**Proof.** Each `P_i` and `C_j` is a tree, being a connected subgraph of the
forest `K`.  Contract all of its edges.  Edge contraction in a forest cannot
create a cycle: if the contracted graph had a cycle (including two parallel
edges), replacing each contracted vertex by the unique paths in its original
tree would give a cycle in `K`.  The resulting multigraph is exactly `J_K`,
possibly together with the isolated vertices corresponding to components
without crossing edges.  Thus `J_K` is a forest.  The contractions change
neither the number of components nor the `t` crossing edges.  Euler's formula
for the contracted forest gives `c(K)=(p+c)-t`.  This also covers `B` or `I`
empty under the convention above.

The forest assumption is essential.  Merely knowing the counts `p,c,t` does
not prevent two teeth from returning to one inner component.

## 2. Exact outer-layer deletion (proved)

Assume `n>=3`.  Let `B` be the outer boundary cycle and `I=V(G_n)\B`, naturally
identified with `G_(n-2)`.  There are

```text
|B| = 4n-4,       |E(G_n[B])| = 4n-4,
|E(B,I)| = 4n-8.
```

Write `H^o=H[I]` and `F^o=F cap I`.  On the boundary cycle let `x_UU` and
`x_FF` count edges with both endpoints in `U` and both endpoints in `F`,
respectively.  Among the radial edges `E(B,I)`, define `y_UU` and `y_FF`
similarly.

Because `H[B]` is obtained from a cycle by deleting exactly the `x_UU` edges,
forest-validity forces `x_UU>=1`, and `H[B]` has exactly `x_UU` path
components.  It has `4n-8-y_UU` teeth.  Applying (1) gives the exact identity

```text
c_H = c(H^o) + x_UU + y_UU - (4n-8).                  (2)
```

Likewise, `G_n[F cap B]` is a disjoint union of boundary paths.  Its number of
components is

```text
p_F = |F cap B|-x_FF.
```

This remains correct when `F cap B` is empty: both terms are zero.  The only
other exceptional cyclic case would be `F cap B=B`, but then the whole
boundary cycle lies in `H`, contradicting forest-validity.  There are `y_FF`
`F`-teeth, so

```text
c_F = c(G_(n-2)[F^o]) + |F cap B|-x_FF-y_FF.          (3)
```

Equations (2) and (3) are the requested outer-layer deletion identities.  They
can also be obtained from `c=|V|-|E|`, but the comb proof records the stronger
separation information that is needed when layers are joined.

## 3. The global component ledger (proved)

Let `u=|U|`, and partition the grid edges into `UU`, `UF`, and `FF` edges with
counts `e_U,e_X,e_F`.  Since `H` is a forest,

```text
c_H = n^2-(e_X+e_F) = e_U-n^2+2n,
c_F = (n^2-u)-e_F,
Q_U = 4u-2e_U-e_X.
```

The middle formula also holds for `F=empty`: both sides are zero because then
`e_F=0` and `u=n^2`.  Summing and using
`e_U+e_X+e_F=2n(n-1)` yields

```text
Q_U+c_F+c_H = 3u-2(n-1)^2+2.                         (4)
```

For a dual-tree support, the incidence-waste identity is
`W=3u-2(n-1)^2`.  Therefore (4) proves the exact equivalences

```text
W >= n+2
iff Q_U+c_F+c_H-2 >= n+2
iff Q_U+c_F+c_H >= n+4.                              (5)
```

This is an equivalence, not by itself a proof of the inequality in (5).

## 4. Exact annular merger ledger (proved)

The comb lemma gives a useful refinement of (2)-(3).  For either forest
`K=H` or `K=G_n[F]`, discard isolated vertices of its incidence graph `J_K`.
Let

```text
a_K = number of boundary backbones having at least one tooth,
s_K = p_K-a_K,
mu_K = sum over components Z of J_K of
       (number of inner vertices of Z - 1).
```

Thus `s_K` counts unattached boundary components and `mu_K` counts the inner
components actually merged through the outer annulus.  Since every nontrivial
component of `J_K` is a tree, its edge count is its number of vertices minus
one.  Summing gives

```text
t_K=a_K+mu_K,
c(K)=c(K[I])+s_K-mu_K.                               (6)
```

For `n>=4`, the deficiency of `U cap I` as a subset of its `(n-2) x (n-2)`
grid is exactly the number of radial edges whose inner endpoint is in `U`.
Denote it by `Q_U^o`.  If

```text
L_n(U)=Q_U+c_F+c_H,
```

then (6), once for `F` and once for `H`, proves

```text
L_n(U)-L_(n-2)(U cap I)
  = Q_U-Q_U^o+s_F+s_H-mu_F-mu_H.                     (7)
```

This is exact: the merger terms cannot simply be dropped.

## 5. Scalar merger inequalities: status

### Disproved

The most tempting induction would assert that the right side of (7) is at
least `2`.  It is false already for `n=4`.  In row notation, take

```text
.UU.
.UU.
UUUU
....
```

Here `H` is a forest and

```text
(Q_U,c_F,c_H)                         = (4,3,1),
(Q_U^o,c_F^o,c_H^o)                   = (8,0,4),
(s_F+s_H, mu_F+mu_H)                  = (3,3),
L_4-L_2                               = -4.
```

This also disproves the weaker assertions `L_n-L_(n-2)>=0` and that each new
annulus must supply its own two units.  The inner layer has surplus `12-6=6`,
all of which is consumed while producing the tight outer value `L_4=8`.

### Conjectural

The following narrower merger estimate survived the exhaustive search but is
not proved here:

```text
mu_F+mu_H <= rho_U,                                   (8)
```

where `rho_U` is the number of radial edges whose inner endpoint is in `U`
(`rho_U=Q_U^o` for `n>=4`).  Exhaustion gives minimum slack `rho_U-mu_F-mu_H`
equal to `0` for `n=3` and `4` for `n=4`.  A proof needs a simultaneous charge:
an inner `F` component can be merged in both the `F`-comb and the coarser
`H`-comb, so separate injections do not automatically combine.  Moreover,
even (8) alone is too weak in (7), because `Q_U^o` is already subtracted there.

### Exact remaining bottleneck

Let the inherited surplus be

```text
sigma_o=L_(n-2)(U cap I)-(n+2).
```

Assuming the desired bound on the inner grid gives `sigma_o>=0`.  Equation (7)
shows that the precise annular statement sufficient to continue induction is

```text
Q_U-Q_U^o+s_F+s_H-mu_F-mu_H >= 2-sigma_o.             (9)
```

The counterexample above is tight in (9): both sides are `-4`.  The unresolved
issue is therefore not comb separation or component bookkeeping; those are
exact.  It is to control the two merger counts jointly by current boundary
charge *and inherited inner surplus*.  Any scalar argument that forgets
`sigma_o` is already ruled out by the displayed `4 x 4` pattern.

## 6. Exhaustive verification

`check_boundary_peeling_lemmas.py` enumerates every binary pattern through
`n=4`, retains exactly those for which `H` is a forest, and independently
checks (1), (4), (6), the target inequality at these sizes, the counterexample,
and the stated evidence for (8).  The forest-valid census is

```text
n=2: 9 patterns
n=3: 100 patterns
n=4: 2278 patterns
```

The checker is evidentiary support for the formulas; the proofs above do not
depend on exhaustive computation.
