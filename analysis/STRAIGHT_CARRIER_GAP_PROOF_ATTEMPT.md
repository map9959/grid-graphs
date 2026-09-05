# Straight-carrier gap inequality: proof attempt and charging obstruction

## Outcome

Let `n >= 2`, let `F` be forced-acyclic in the `n x n` grid, let
`U=V\F`, and let `g` be the internal axial gap count from
`STRAIGHT_CARRIER_GAP_INEQUALITY.md`.

The proposed carrier-congestion charging route does not prove

```text
3|F|+2g <= n^2+3n-4.                                  (G2)
```

There is a clean injective charging lemma for branching `U` vertices, proved
below, but it charges nonroot carrier credits that are already needed by the
target ledger. Equality examples show that treating this charge as additional
or consumable is false. There is also no injection from gaps to their `U`
vertices: perpendicular gaps can share a vertex.

This note does not give a counterexample to `(G2)`. It gives a concrete
counterexample to the requested additive charging lemma and isolates the
remaining statement exactly. Consequently the finite evidence in
`STRAIGHT_CARRIER_GAP_INEQUALITY.md` must not be upgraded to a theorem on the
basis of carrier contraction.

## 1. Exact reduction

Use the notation of `STRAIGHT_CARRIER_CONTRACTION.md`:

```text
c_F = number of components of G[F],
i   = number of isolated U vertices in H,
k   = number of nonisolated components of H,
B_U = sum_(u in U) (4-deg_G(u)).
```

The forced-forest Euler identity is

```text
3|F|+c_F+c_H=n^2+B_F,
c_H=i+k,
B_F+B_U=4n.
```

Therefore

```text
3|F|+2g <= n^2+3n-4
iff
B_U+c_F+i+k >= n+4+2g.                                (L)
```

This is subtraction-free and is the appropriate Lean target. In particular,
the gap strengthening is not obtained by changing any contraction formula;
it requires two genuinely additional units on the right of the already open
unstrengthened ledger.

## 2. What branching contraction actually proves

Contract every `F` component and retain the individual nonisolated `U`
vertices. The resulting bipartite graph `Q` is a forest. Put

```text
d_F(u) = deg_Q(u),
b       = |{u in U : d_F(u)>=2}|,
beta    = sum_(u in U) max(d_F(u)-1,0).
```

The exact formulas from `STRAIGHT_CARRIER_CONTRACTION.md` are

```text
beta = c_F-k,                                          (C1)
sum_C (deg_Q(C)-p(C)) = beta+b.                        (C2)
```

Here `p(C)` counts degree-one `U` neighbors of `C`.

There is nevertheless a valid injectivity lemma.

**Branch-to-carrier injection.** Choose one carrier root in every nonisolated
component of `Q` and orient all edges away from the root. For each branching
`U` vertex `u`, choose one carrier child of `u`. Such a child exists because
`u` has one parent edge and degree at least two. Distinct branching vertices
have distinct chosen children, because a rooted-forest vertex has a unique
parent. Hence

```text
b <= c_F-k = beta.                                     (I)
```

This proof is Lean-suitable. A convenient abstract statement is:

```lean
theorem branchingU_inj_nonrootCarrier
    (Q : SimpleGraph (Sum Carrier U))
    (hforest : Q.IsAcyclic)
    (hbip : everyEdgeJoinsCarrierAndU Q) :
    Exists fun owner : BranchingU Q -> NonrootCarrier Q roots =>
      Function.Injective owner
```

The concrete formalization should define the map using the rooted parent
forest and prove injectivity from uniqueness of `parent`. The codomain has
cardinality `c_F-k`, one nonroot-carrier allowance removed for each of the `k`
carrier-rooted components.

Lemma `(I)` explains the one-unit overlap in `(C2)`, but it does not create a
new credit. Replacing `(C2)` by the numerical upper bound
`beta+b <= 2beta` spends the same `c_F-k` carrier resource a second time.

## 3. Concrete failure of additive payment

Consider the forced-acyclic `4 x 4` pattern

```text
FUUF
FUUF
UUUU
FFFF
```

Its row masks are `(9,9,0,15)`. Direct contraction gives

```text
B_U=4,  c_F=3,  i=0,  k=1,  g=0,
b=2,    beta=2=c_F-k.
```

Thus `(L)` is tight:

```text
B_U+c_F+i+k = 4+3+0+1 = 8 = n+4+2g.
```

Both branching vertices inject into the two nonroot carriers, as `(I)` says,
but there is no expendable credit. If the two carrier credits are consumed to
pay congestion, the proposed remaining ledger becomes

```text
B_U+i+(beta-b)+2k = 4+0+0+2 = 6 < 8.
```

So the implication

```text
"pay every branching unit by a distinct component credit"
  => enough unspent boundary/component credit for (L)
```

is false even with `g=0`. This is not a mere injectivity defect: an injection
exists, but its codomain is already fully used by the equality ledger.

The gap-tight `12 x 12` witness from
`STRAIGHT_CARRIER_GAP_INEQUALITY.md`, with row masks

```text
4093, 1, 513, 2301, 2049, 2817,
2169, 2049, 2957, 2081, 1, 4093
```

makes the obstruction sharper:

```text
B_U=5, c_F=11, i=1, k=1, g=1,
b=10, beta=10,
B_U+c_F+i+k = 18 = n+4+2g.
```

All ten nonroot-carrier credits are images of branching vertices, while every
one of the eighteen units in `(L)` is necessary. Any proof that pays branching
congestion and then also counts the same carrier credits in `(L)` double
counts; any proof that removes them after payment fails numerically.

## 4. Gap injectivity audit

On one fixed row, horizontal carriers are disjoint closed intervals in a
linear order. An internal horizontal gap is defined only between consecutive
carriers. Therefore two horizontal gaps in that row are disjoint and cannot
nest. The same argument applies to one column. Gaps on different parallel
lines are disjoint because their fixed coordinates differ. Thus there is no
same-axis nesting issue under the stated definition.

Perpendicular gaps can intersect. The forced-acyclic `7 x 7` row masks

```text
8, 8, 0, 99, 0, 8, 8
```

render as

```text
UUUFUUU
UUUFUUU
UUUUUUU
FFUUUFF
UUUUUUU
UUUFUUU
UUUFUUU
```

There is one horizontal gap in row `3` and one vertical gap in column `3`.
Both contain `(3,3)`. The four length-two carriers have disjoint forced combs,
so `H` is a forest. In fact the shared central vertex has `d_F=0`; it is not a
branching vertex in `Q` at all.

Consequently the map "gap -> a U vertex in the gap" is not automatically
injective, and assigning ownership to a gap vertex does not align gaps with
branching congestion. One can choose different vertices in this particular
example, but no such choice follows from maximality or from the contraction
identities, and gap length cannot be used: the certified `12 x 12` equality
witness has one gap of length three but only two units of gap credit.

## 5. Remaining theorem

After all exact contraction formulas and the valid injection `(I)`, the
unproved content is still precisely `(L)`:

```text
B_U+c_F+i+k >= n+4+2g.
```

Neither `(C1)`, `(C2)`, carrier degree
`deg_Q(C)=2|C|+2-B(C)`, nor the row/column occupancy identity contains the
linear `n+4` lower bound. Moreover `(L)` with `g` erased is the universal
forced-forest inequality already identified as open in the surrounding
analysis. The stronger assertion cannot be completed by an algebraic
rearrangement of those formulas.

A successful proof needs a new geometric noncongestion theorem that proves
`(L)` directly and permits credits used in the rooted branch injection to be
reused only through an explicit structural decomposition. Calling the rooted
injection a payment, without such a decomposition, is invalid on the two tight
examples above.
