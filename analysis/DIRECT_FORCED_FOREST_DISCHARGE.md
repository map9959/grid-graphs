# Direct forced-forest discharge

## 1. Setup and conclusion

Let `n >= 2`, let `G=G_n` be the `n x n` grid, and partition its
vertices as `F union U`.  Put

```text
H = forcedEdgeGraph G F = G-E(G[U]).
```

Assume that `H` is acyclic.  For `u in U`, define

```text
d_F(u) = |N_G(u) intersect F|.
```

The following three nonnegative integer parameters are the natural credits:

```text
i     = |{u in U : d_F(u)=0}|,
beta  = sum_(u in U) max(d_F(u)-1,0),
k     = number of nonisolated connected components of H.
```

Here `beta` is a weighted branching credit.  A vertex of `F`-degree `j`
contributes `j-1`, not merely one, when `j>=2`.

The exact direct-discharge identity is

```text
3|F| + i + beta + 2k = n^2+B_F,                       (D)
```

where

```text
B_F = sum_(f in F) (4-deg_G(f)).
```

Consequently the desired bound has the subtraction-free equivalent form

```text
3|F|+4 <= n^2+3n
iff
B_F+4 <= 3n+i+beta+2k.                                (BI)
```

Over the integers, `(BI)` is

```text
B_F-i-beta-2k <= 3n-4.                                (BI-Z)
```

Thus the proposed discharge is exact only with coefficient two on every
nonisolated `H` component.  With that coefficient, it is equivalent to the
original theorem and is not by itself a reduction.  The superficially
stronger version with one credit per nonisolated component is false; Section 4
gives a `4 x 4` counterexample.

## 2. Component decomposition over the integers

Write

```text
c_F = c(G[F]),
c_H = c(H).
```

Components include isolated vertices, while `c(G[F])=0` when `F` is empty.

**Theorem 2.1 (forced-forest Euler identity).** If `H` is acyclic, then

```text
3|F|+c_F+c_H=n^2+B_F.                                 (E)
```

**Proof.** Since `G[F]` is a subgraph of `H`, it is a forest, and hence

```text
|E(G[F])|+c_F=|F|.                                    (1)
```

Summing the grid degrees on `F` counts an `F-F` edge twice and an `F-U`
edge once.  Every such edge is in `H`, so

```text
4|F|-B_F = 2|E(G[F])|+|E(F,U)|,
|E(H)|   = |E(G[F])|+|E(F,U)|
         = 4|F|-B_F-|E(G[F])|.
```

Substitute `(1)` to obtain

```text
|E(H)|=3|F|+c_F-B_F.                                  (2)
```

The spanning forest `H` also satisfies

```text
|E(H)|+c_H=n^2.                                       (3)
```

Equating `(2)` and `(3)` proves `(E)`.  All displayed equations are additive
natural-number equations except the explanatory rearrangement in `(2)`; in
Lean, `(E)` is already `grid_component_reduction`.  QED

**Theorem 2.2 (component-credit decomposition).** With `i`, `beta`, and `k`
as above,

```text
c_H=i+k,                                              (4)
c_F=beta+k.                                           (5)
```

**Proof.** Because `n>=2`, every grid vertex has positive grid degree.  Every
vertex in `F` is therefore nonisolated in `H`.  A vertex in `U` has exactly
`d_F(u)` incident edges in `H`, so the isolated vertices of `H` are exactly
the `i` vertices of `U` with `d_F(u)=0`.  This proves `(4)`.

Let

```text
U_+={u in U:d_F(u)>0},       p=|U_+|.
```

Delete the `i` isolated vertices from `H`.  The resulting forest has
`|F|+p` vertices, `k` components, and

```text
|E(G[F])| + sum_(u in U_+) d_F(u)
```

edges.  Euler's forest identity and `(1)` give

```text
(|F|-c_F)+sum_(u in U_+) d_F(u)=|F|+p-k.
```

Cancel `|F|` in `Int` and rearrange:

```text
c_F = sum_(u in U_+) (d_F(u)-1)+k = beta+k.
```

For a subtraction-free Lean proof, replace each positive `d_F(u)` by
`(d_F(u)-1)+1`, justified by positivity, sum this equality over `U_+`, and use
`sum 1=p`.  No cancellation in `Nat` is then hidden.  QED

Substituting `(4)` and `(5)` in `(E)` proves `(D)`.  Applying `omega` to `(D)`
proves the equivalence `(BI)` without any natural-number subtraction.

## 3. Exact outer-boundary facts

Let `P` be the outer boundary cycle.  It has `4n-4` vertices and edges.  Let

```text
f       = |F intersect V(P)|,
u       = |U intersect V(P)|,
a       = number of corners in F,
x_FF    = number of F-F edges of P,
x_UU    = number of U-U edges of P.
```

Then

```text
f+u=4n-4,             B_F=f+a.                        (6)
```

The second identity is important: traversing the boundary cycle counts a
corner once, whereas boundary deficiency counts it twice.

**Lemma 3.1 (the boundary must contain an unforced edge).**

```text
x_UU>=1.                                                 (7)
```

**Proof.** A perimeter edge is absent from `H` exactly when both endpoints are
in `U`.  If `x_UU=0`, every edge of `P` belongs to `H`, so `P` is a cycle in
`H`, contrary to acyclicity.  QED

In particular, merely proving that not every boundary vertex is in `F` is too
weak: acyclicity forces two cyclically consecutive boundary vertices in `U`.

**Lemma 3.2 (boundary-run ledger).** The graph `H[P]` is obtained from `P` by
deleting its `x_UU` edges and therefore has exactly `x_UU` path components.
Moreover, `G[F intersect V(P)]` has

```text
p_F=f-x_FF                                               (8)
```

components.  This includes `F intersect V(P)=empty`, when both sides are zero.
The only exceptional cyclic case would be `F intersect V(P)=V(P)`, and Lemma
3.1 excludes it.

If both letters occur and `r` is the number of cyclic `F`-runs, then equivalently

```text
x_FF=f-r,             x_UU=u-r,             p_F=r.     (9)
```

**Proof.** Deleting `m>=1` edges from a cycle produces a spanning forest with
`m` path components.  For `(8)`, every `F`-run with `s` vertices contains
`s-1` `F-F` edges; summing `s-(s-1)` over the runs gives `f-x_FF`.  Equation
`(9)` is the same calculation for both letters.  QED

These are all exact consequences of the cyclic boundary word.  They do not
prove `(BI)`: boundary path components can be joined through the interior, and
components of `H` with no boundary vertex, especially isolated `U` vertices,
contribute to the right side of `(BI)` without appearing in the word.

## 4. Counterexample to one component credit

Consider `n=4` and the pattern

```text
FFFF
UUUU
UUUU
FFFF
```

The forced graph `H` is the disjoint union of two comb trees.  The upper tree
is the top horizontal path together with the four edges from it to the second
row; the lower tree is analogous.  There are no other forced edges.  Hence
`H` is acyclic and

```text
k=2.
```

Every `U` vertex has exactly one neighbor in `F`, so

```text
i=0,                   beta=0.
```

The four `F` corners contribute eight to `B_F`, and the four noncorner `F`
boundary vertices contribute four.  Thus

```text
B_F=12,                3n-4=8.
```

The proposed inequality with only one credit per nonisolated component fails:

```text
B_F-i-beta-k = 12-0-0-2 = 10 > 8.
```

With the coefficient forced by Theorem 2.2, equality holds:

```text
B_F-i-beta-2k = 12-0-0-4 = 8 = 3n-4.
```

The same coefficient issue already occurs on the `2 x 2` pattern with one
row in `F` and one row in `U`: `B_F=4`, `i=beta=0`, and `k=1`, so one component
credit gives `3>2`, while two give equality.

## 5. Lean-oriented statement

The robust formal target should avoid signed subtraction:

```lean
/-- `i` counts `U` vertices of forced degree zero, `beta` is the sum of
    `d_F u - 1`, and `k` counts edge-containing components of `H`. -/
theorem square_forced_discharge_ledger
    {n : Nat} (hn : 2 <= n) (F : Finset (GridVertex n n))
    (hH : (forcedEdgeGraph (gridGraph n n) (F : Set _)).IsAcyclic) :
    3 * F.card + isolatedUCount n F + branchCredit n F
        + 2 * nonisolatedForcedComponentCount n F =
      n * n + boundaryDeficiencySum n n F

theorem square_forced_target_iff_boundary_discharge
    {n : Nat} (hn : 2 <= n) (F : Finset (GridVertex n n))
    (hH : (forcedEdgeGraph (gridGraph n n) (F : Set _)).IsAcyclic) :
    3 * F.card + 4 <= n * n + 3 * n <->
      boundaryDeficiencySum n n F + 4 <=
        3 * n + isolatedUCount n F + branchCredit n F
          + 2 * nonisolatedForcedComponentCount n F
```

Suggested definitions are

```text
isolatedUCount = |{u in univ\F : d_F(u)=0}|,
branchCredit   = sum_(u in univ\F) (d_F(u)-1).
```

Natural subtraction is harmless in `branchCredit`: it is pointwise truncated,
so it is exactly `max(d_F(u)-1,0)`.  For the component count, count components
whose support meets `F`; when `n>=2`, these are exactly the nonisolated
components of `H`, because every edge of `H` has an endpoint in `F` and every
`F` vertex has positive degree in `H`.

The proof should proceed by two structural lemmas implementing `(4)` and `(5)`,
rewrite `grid_component_reduction`, and finish both displayed theorems with
`omega`.  The boundary-cycle lemmas are independently formalizable, but they
do not close the second theorem.  Closing it with coefficient two is exactly
the original universal forced-forest bound; no complete proof follows from
the outer boundary word and forest Euler identities alone.
