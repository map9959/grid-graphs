# Full-degree vertices in a grid spanning tree

## Statement and status

Let `G_n` be the `n x n` grid, with `n>=2`, and let `T` be any spanning tree
of `G_n`. Define

```text
F(T) = {v : deg_T(v)=deg_G(v)},
U(T) = V(G_n)\F(T).
```

The proposed universal theorem is

```text
3|F(T)| <= n^2+3n-4.                                  (T)
```

This is exactly the previously used universal incidence-waste bound, not a
consequence of the elementary degree-deficiency packing bound. The direct-tree
form removes the auxiliary choice of a support set and a forced graph, but it
does not remove the missing geometric inequality. I did not find a proof of
`(T)`. Sections 2 and 3 verify the equivalence in both directions. Section 6
proves a genuinely weaker universal theorem, rather than presenting another
equivalent reformulation as progress.

## 1. Exact child-slot ledger

Put

```text
q(v) = 4-deg_G(v).
```

Thus `q` is zero in the interior, one at a noncorner boundary vertex, and two
at a corner. For `v in U`, let

```text
delta(v) = deg_G(v)-deg_T(v),
Q = sum_(v in U) q(v),
S = sum_(v in U) (deg_T(v)-1).
```

Every vertex of a tree with at least two vertices has positive tree degree, so
`delta(v)` lies in `{1,2,3}` for `v in U`. Pointwise,

```text
delta(v) = (4-q(v))-deg_T(v)
         = 3-q(v)-(deg_T(v)-1).
```

The grid has `2n(n-1)` edges and the tree has `n^2-1` edges. Consequently the
number of omitted edges is `(n-1)^2`, and summing their two endpoints gives

```text
2(n-1)^2 = sum_(v in U) delta(v) = 3|U|-Q-S.           (1)
```

The term `deg_T(v)-1` is literally the number of children of `v` if the tree is
rooted through its parent edge; changing which vertex is the root merely moves
one exceptional slot. Formula `(1)` avoids that exception by using unrooted
excess directly.

Since `|F|=n^2-|U|`, `(1)` yields the exact identity

```text
3|F| = n^2+4n-2-(Q+S).                                (2)
```

Therefore

```text
(T)  iff  Q+S >= n+2.                                 (CS)
```

This checks the constant carefully: subtracting the right side of `(T)` from
the right side of `(2)` leaves exactly `n+2`, not `n`, `n+1`, or `n+4`.

## 2. Omitted-edge and bipartition forms

Let `D=E(G_n)\E(T)`. In the plane dual, including the exterior face `OUT` and
retaining parallel boundary dual edges, `D*` is a spanning tree. This is the
standard planar tree-cotree theorem: `D*` has `(n-1)^2` edges, one fewer than
the number `(n-1)^2+1` of faces, and a dual cycle would correspond to a primal
cut disjoint from `T`, contradicting connectivity.

Let `d_D(v)` count omitted primal edges incident with `v`. Then `d_D(v)` is
`delta(v)`, and `U` is exactly the support of `D`. No vertex can have
`d_D(v)=4`: that would isolate it in `T`. If

```text
N_j = |{v : d_D(v)=j}|,
```

endpoint counting gives

```text
Q+S = sum_(v in U) (3-d_D(v))
    = 2N_1+N_2
    = 3|U|-2(n-1)^2.                                  (3)
```

Thus `(T)` is also exactly

```text
2N_1+N_2 >= n+2.                                      (IW)
```

The grid bipartition provides two separate endpoint equations: every omitted
edge has one black and one white endpoint, so

```text
sum_j j N_j^black = sum_j j N_j^white = (n-1)^2.
```

These equations reproduce `(3)` after adding colors. They do not prove `(IW)`:
they contain no restriction preventing incidence from being packed into many
degree-three support vertices. Any bipartition proof needs an additional
geometric or acyclicity lemma.

## 3. Equivalence with the forced-forest theorem

For a set `U subseteq V(G_n)`, put `F=V\U` and

```text
H(U) = G_n-E(G_n[U]).
```

Every edge incident with `F` belongs to `H(U)`. The following two assertions
are equivalent:

1. Every spanning tree satisfies `(T)` for its actual full-degree set.
2. Every `U` for which `H(U)` is a forest satisfies
   `3|V\U|<=n^2+3n-4`.

For `1 => 2`, extend the forest `H(U)` to a spanning tree of the connected grid.
Every vertex in the designated set `F` is then full in the extension, although
some designated `U` vertices may become full too. Hence the tree theorem bounds
the extension's full set and therefore also bounds `|F|`.

For `2 => 1`, take `U=U(T)`. Every edge incident with an actual full vertex is
in `T`, so `H(U) subseteq T` and is a forest. Applying assertion 2 gives `(T)`.

The possible strict inclusion between the designated `F` and the extension's
actual full set is why merely saying "extend the forest" without checking the
inequality direction is incomplete.

For completeness, if `b_F=sum_(v in F)q(v)`, `c_F=c(G_n[F])`, and `c_H=c(H)`,
forest edge counting gives

```text
3|F| = n^2+b_F-c_F-c_H.
```

Thus `(T)` is also equivalent to

```text
b_F <= 3n-4+c_F+c_H.
```

This is useful bookkeeping but is not a smaller lemma.

## 4. Direct proof attempts and their exact stopping points

### Rooted child slots

Rooting `T` and charging the children of full vertices gives their full local
contribution. After the root correction is eliminated, the result is exactly
`(1)`. All unspent charge is `Q+S`, so a child-slot proof still has to establish
`Q+S>=n+2`. Rooting alone supplies no congestion rule for slots belonging to
different full components.

### Leaf counts

The tree identity `sum_v(deg_T(v)-2)=-2` gives, if `f_i` and `f_e` count full
interior and full noncorner boundary vertices,

```text
S = |U|-2-2f_i-f_e.
```

Substitution into `Q+S>=n+2` is exact, but does not force enough leaves in `U`.
A long alternating full path can consume only one component credit, while a
single non-full vertex can join several different full components without
creating a cycle.

### Boundary combs

The perimeter edges present in `T` form disjoint path segments. Contracting
these segments and the components attached to them gives a forest, so two teeth
cannot join the same pair of contracted components and alternating component
cycles are forbidden. This separation is real, but it does not bound how many
different components one segment or one non-full vertex can meet. Consequently
it does not supply the missing `n+2` charge.

### Induction on leaves or components

Deleting a leaf of `T` does not usually produce a spanning tree of a smaller
square. Deleting an outer row or layer does produce a smaller grid, but can
merge many inherited components; its local charge need not be nonnegative.
Thus a valid induction must retain a component-merger potential. Once all such
components are retained, the scalar terminal inequality is again the
forced-forest form above.

### A useful conditional target

If `m` is the number of omitted perimeter edges, then the endpoints of those
edges are in `U`. Since a proper edge subset of a cycle has at least as many
incident vertices as edges, and `q>=1` on the perimeter,

```text
Q >= m.
```

Hence the genuinely sufficient, but non-universal, condition

```text
m + sum_(u in U)(deg_T(u)-1) >= n+2                  (4)
```

implies `(T)`. This identifies a concrete boundary-comb/child-slot target, but
known low-boundary configurations show that one cannot expect `m` alone to be
linear in `n`.

## 5. Actively checked claims

`check_full_degree_grid_tree_bound.py` exhaustively enumerates all spanning
trees through a requested small width. It checks `(1)`, `(2)`, `(3)`, the
omitted-edge count, `Q>=m`, and the proposed theorem. It also reports the
minimum observed `Q+S`, so finite verification is not mistaken for a proof.

The exhaustive results for `n=2,3,4` are:

```text
n   spanning trees   min(Q+S)   n+2
2              4          4       4
3            192          7       5
4         100352          6       6
```

Thus there is no counterexample through `n=4`; `n=4` attains equality. These
finite results validate the constants and identities but do not establish an
arbitrary-width theorem. The checker prints one edge set attaining each
minimum. The restriction `n>=2` is necessary: for the degenerate `1 x 1` grid,
the sole vertex is full but the proposed right side is zero.

## 6. A smaller unconditional lemma

Although `(T)` remains unproved in arbitrary width, the following weaker result
is immediate and genuinely smaller than the desired `n+2` incidence-waste
claim.

**Lemma.** For every `n>=2` and every spanning tree of `G_n`,

```text
Q+S >= 3,  if n == 1 (mod 3),
Q+S >= 4,  otherwise.                                  (5)
```

Equivalently,

```text
3|F| <= n^2+4n-5,  if n == 1 (mod 3),
3|F| <= n^2+4n-6,  otherwise.                          (6)
```

**Proof.** The perimeter is a cycle, so `T` omits at least one perimeter edge.
Both endpoints are non-full. Their total boundary deficiency is at least two,
and `S>=0`; hence `Q+S>=2`.

By `(3)`,

```text
Q+S == -2(n-1)^2 (mod 3).
```

This residue is zero when `n==1 (mod 3)` and one otherwise. The least integer
at least two in the relevant residue class is respectively three or four. This
proves `(5)`, and `(6)` follows from `(2)`. QED

For `n=2`, `(5)` reaches `n+2` and proves `(T)`. For larger widths it is much
weaker than the desired linear charge, but it is an unconditional theorem with
a complete proof, not an equivalent restatement. The enumeration shows that it
is not sharp at `n=3` or `n=4`.

## Conclusion

The recasting is exact:

```text
3|F(T)|<=n^2+3n-4
iff Q+S>=n+2
iff 2N_1+N_2>=n+2
iff the corresponding forced-forest inequality holds for every U.
```

The assertion requires `n>=2`, and exhaustive enumeration verifies it through
`n=4`, with equality at `n=2,4`. The arbitrary-width geometric inequality
remains open. The direct-tree language clarifies that the missing ingredient is
a linear lower bound on boundary deficiency plus non-full child slots; degree
sums, bipartition, leaf identities, and comb contraction alone reproduce the
ledger but do not provide that lower bound.
