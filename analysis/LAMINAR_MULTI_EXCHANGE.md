# Laminar cuts and multi-edge incidence-waste exchange

This note continues `INCIDENCE_WASTE_EXCHANGE.md`.  The grid has vertex set
`[0,n-1]^2`, `G*` is its plane dual (including `OUT` and parallel boundary
edges), and `D` is a spanning tree of `G*`.  If `h` is a dual edge, `h*`
denotes its primal representative.  Put

```text
d_D(v) = |{h in D : v is an endpoint of h*}|,
U(D)   = {v : d_D(v)>0},
Z(D)   = V(G)\U(D),
W(D)   = sum_(v in U(D)) (3-d_D(v)).
```

As in the earlier note, the dual edges represented by the primal edges at a
vertex form a dual cycle, so `d_D(v)<=3`.  Also

```text
W(D)=3|U(D)|-2|D|=3|U(D)|-2(n-1)^2.                 (1)
```

The results below do not prove `W(D)>=n+2`.  They identify exactly what
laminarity and waste minimality provide, and isolate the remaining
augmentation statement.

## 1. Arbitrary multi-edge exchange

For `F subseteq D` and `E subseteq E(G*)\D`, call `(F,E)` a tree exchange if

```text
D' = D-F+E
```

is a spanning tree.  Necessarily `|F|=|E|`.  Define

```text
L_D(F,E) = {v in U(D) : every D-edge represented at v belongs to F
                         and no edge of E is represented at v},
A_D(E) = {z in Z(D) : some edge of E is represented at z}.
```

Thus `L_D(F,E)` consists of the old support vertices lost by the exchange, while
`A_D(E)` consists of the newly supported vertices.  Shared primal endpoints
and multiple changes at one vertex require no special treatment.

**Theorem 1 (exact multi-edge formula).**  Every tree exchange satisfies

```text
W(D-F+E)-W(D) = 3(|A_D(E)|-|L_D(F,E)|).             (2)
```

**Proof.**  The support of the new tree is exactly

```text
(U(D)\L_D(F,E)) union A_D(E).
```

Both trees have the same number of edges.  Subtracting (1) for the two trees
therefore gives (2).  This also proves that no endpoint-by-endpoint
independence assumption is hidden in the formula.  QED

For one-edge exchange, `L_D({f},{e})` is precisely the set of endpoints of `f*`
having `D`-degree one and not also incident with the added edge.  Formula (2)
therefore specializes to the formula in the earlier note.

**Corollary 1 (global saturation).**  If `D` minimizes `W` over all dual
spanning trees, then every tree exchange obeys

```text
|A_D(E)| >= |L_D(F,E)|.                             (3)
```

This is the strongest conclusion available directly from global waste
minimality: every simultaneous exchange must introduce at least as many
distinct unsupported vertices as it deletes supported vertices.

## 2. Rooted fundamental cuts

Fix a root `rho` of `D`.  For each `f in D`, orient `f` away from `rho` and let
`S_f` be the vertex set of the component of `D-f` not containing `rho`.  Let

```text
B_f = delta_G*(S_f).
```

This is the fundamental bond of `f`; in particular, `f in B_f`.

**Theorem 2 (rooted-shore laminarity).**  The family `{S_f:f in D}` is
laminar.  More precisely, for any `f,g in D`, either

```text
S_f subseteq S_g,  S_g subseteq S_f,  or  S_f intersect S_g is empty.
```

Also, for any dual edge `e=xy`,

```text
e in B_f  iff  f lies on the unique D-path from x to y.                (4)
```

**Proof.**  `S_f` is the descendant set below the child endpoint of `f`.
Two child vertices are ancestor-related, giving containment, or lie in
different rooted branches, giving disjointness.  Removing `f` separates `x`
and `y` exactly when their unique tree path uses `f`, which proves (4).  QED

The shores are laminar; the bond edge sets `B_f` generally are not laminar as
sets of edges.  Equation (4) also shows why rooted laminarity gives no
congestion bound: one non-tree edge belongs to every fundamental bond on what
may be a long tree path.

There is one exact condition for combining choices from these cuts.

**Theorem 3 (simultaneous-exchange criterion).**  Let `F subseteq D`.  Contract
each component of `D-F` to one vertex and retain the edges of `E` between the
resulting vertices, including multiplicity.  Then `D-F+E` is a spanning tree
if and only if this contracted graph is a tree.  In that event `|E|=|F|`.

**Proof.**  Each component of `D-F` is already a tree.  Contracting these
components preserves whether the added edges connect all components and
whether they create a cycle.  There are `|F|+1` components, so a tree on the
contracted vertices has `|F|` edges.  QED

In particular, merely choosing a distinct `e_f in B_f-D` for every `f in F`
does not imply a simultaneous exchange.

## 3. Fundamental bonds and primal cycles

Let

```text
T = {h* : h notin D}.
```

**Theorem 4 (complementary tree and bond-cycle correspondence).**  `T` is a
primal spanning tree.  For every `f in D`,

```text
{h* : h in B_f} = C_T(f*),                           (5)
```

where `C_T(f*)` is the unique primal cycle in `T+f*`.  Consequently a possible
one-edge replacement `e in B_f-{f}` is exactly a primal tree edge `e*` on
`C_T(f*)-{f*}`.

**Proof.**  We use the elementary plane-duality fact that a bond in one of a
connected plane graph and its dual is represented by a cycle in the other.
It remains valid when the dual has parallel boundary edges.  If `T` contained
a primal cycle, its represented dual bond would contain no edge of `D`,
contradicting connectivity of `D`.  Thus `T` is acyclic.  Euler's formula gives

```text
|T|=|E(G)|-(|V(G*)|-1)=|V(G)|-1,
```

so `T` is a spanning tree.  The fundamental bond `B_f` is a bond, hence its
primal representatives form a cycle.  It contains `f*`, while all its other
edges have dual representatives outside `D` and hence belong to `T`.  The
uniqueness of the cycle in `T+f*` proves (5).  QED

This correspondence is useful for locating replacements, but it does not
turn nested dual shores into edge-disjoint primal cycles.

## 4. The valid protector lemmas

For a tree edge `f`, write

```text
P_f = {v endpoint of f* : d_D(v)=1}.
```

Call an endpoint in `Z(D)` of a proposed added edge a protector.  The following
statement includes the cases of one or two private endpoints and is stronger
than assigning one unspecified protector to one private vertex.

**Theorem 5 (sharp one-edge protector inequality).**  Suppose `D` minimizes
`W`, `f in D`, and `e in B_f-{f}`.  Then

```text
|Z(D) intersect endpoints(e*)|
    >= |P_f \ endpoints(e*)|.                        (6)
```

Thus an added edge avoiding one private endpoint has an unsupported endpoint;
an added edge avoiding two private endpoints has two distinct unsupported
endpoints.

**Proof.**  `D-f+e` is a tree.  Its lost support is exactly
`P_f\endpoints(e*)`, and its new support is exactly
`Z(D) intersect endpoints(e*)`.  Apply (3).  QED

**Theorem 6 (multi-edge protector inequality).**  Under the same minimality
assumption, every simultaneous exchange satisfies

```text
|{unsupported vertices incident with E}|
 >= |{supported vertices whose every D-incidence lies in F
       and which are not incident with E}|.                            (7)
```

**Proof.**  This is Corollary 1 with the definitions expanded.  QED

Inequality (7) permits an abstract injection from the lost set into the newly
supported set for one already constructed simultaneous exchange.  It does
not provide a cutwise injection, choose the incident added edge receiving a
lost vertex, or make injections for different exchanges compatible.  Those
stronger conclusions are false or unsupported, as the next section records.

## 5. Exhaustive counterexamples to natural decongestion claims

The checker `check_laminar_multi_exchange.py` uses coordinates `(row,column)`,
enumerates all 192 dual spanning trees for the `3 x 3` grid, and checks (2) for
all `192^2` ordered pairs of trees.  It found the following witnesses.

### 5.1 No common protector for one cut

Consider the minimum-waste tree (`W=7`) whose primal representatives are

```text
((0,0),(0,1)), ((1,0),(1,1)),
((1,1),(1,2)), ((0,1),(1,1)).
```

For `f*=((0,0),(0,1))`, the vertex `(0,0)` is private.  Among the replacement
edges in `B_f-{f}` avoiding `(0,0)` are

```text
e*=((0,1),(0,2)), with unsupported endpoint set {(0,2)},
e*=((1,0),(2,0)), with unsupported endpoint set {(2,0)},
e*=((1,2),(2,2)), with unsupported endpoint set {(2,2)}.
```

Their protector sets have empty intersection.  Hence Theorem 5 cannot be
strengthened to say that a private rooted cut has one vertex protecting every
replacement across it.

### 5.2 A protector can be reused across cuts

In the same minimum-waste tree, the unsupported vertex `(2,0)` protects the
replacement

```text
remove ((0,0),(0,1)), add ((2,0),(2,1)),
```

at private vertex `(0,0)`, and the same added edge protects

```text
remove ((1,0),(1,1)), add ((2,0),(2,1)),
```

at private vertex `(1,0)`.  Thus local protector occurrences are not
automatically injective across rooted cuts.  This witness does not rule out a
more global matching after a simultaneous exchange has first been selected;
Theorem 6 gives exactly that much and no edgewise realization of it.

### 5.3 Independent fundamental-cut choices need not combine

Take the dual tree with primal representatives

```text
f_0*=((0,0),(0,1)), f_1*=((0,1),(0,2)),
     ((1,0),(1,1)),      ((1,1),(1,2)).
```

The distinct choices

```text
e_0*=((0,1),(1,1)) in B_(f_0)-D,
e_1*=((1,1),(2,1)) in B_(f_1)-D
```

each cross the indicated fundamental cut, but
`D-{f_0,f_1}+{e_0,e_1}` is not a tree.  This directly refutes the naive
laminar augmentation rule.  The contracted-tree condition in Theorem 3 is
indispensable.

## 6. The remaining low-waste augmentation statement

There is a useful exact formulation of what an exchange proof still has to
produce.  It is deliberately not labeled a theorem.

**Low-waste laminar augmentation/decongestion statement `LA(n)` (unproved).**
If a dual spanning tree `D` of the `n x n` grid has `W(D)<=n+1`, then there are
nonempty `F subseteq D` and `E subseteq E(G*)\D` such that

```text
(i)  E is a tree after the components of D-F are contracted;
(ii) |A_D(E)| < |L_D(F,E)|.
```

By Theorem 3, (i) says that this is a genuine simultaneous exchange.  By
Theorem 1, (ii) says that it strictly lowers `W`.  Therefore `LA(n)` would
prove `W(D)>=n+2`: choose a global minimum-waste tree; if its waste were at
most `n+1`, `LA(n)` would contradict minimality.

Conversely, if the desired bound is true, `LA(n)` has an empty hypothesis.
Thus, without additional structural restrictions on `F` and `E`, `LA(n)` is
an exact exchange reformulation of the missing bound rather than progress on
it.  The smallest substantive missing ingredient is a construction satisfying
both the contracted-tree condition and the strict distinct-endpoint inequality
at once.

The low-waste hypothesis does expose many boundary vertices: every supported
noncorner boundary vertex contributes at least one to `W`, and every supported
corner contributes at least two.  Hence `W<=n+1` implies that at most `n+1` of
the `4n-4` boundary vertices are supported, so at least `3n-5` are unsupported.
Their incident primal edges lie in the complementary tree `T`.  Fundamental
replacements can therefore be sought on the cycles in (5).  The attempted
route stalls for two precise reasons demonstrated above:

1. A replacement edge can cross many nested bonds and reuse the same
   unsupported endpoint, so local protector counts do not sum.
2. Separately valid choices on those bonds need not satisfy the contracted
   tree condition.

Theorem 6 resolves endpoint decongestion only after a simultaneous exchange
exists, while Theorem 3 resolves feasibility only after the full edge set is
chosen.  No proved argument here couples the two.  That coupling, preferably
using the long boundary portions of `T` while controlling distinct newly
supported endpoints, is the isolated open step.

## 7. Reproduction

Run

```text
python3 analysis/check_laminar_multi_exchange.py
```

The script has no third-party dependencies.  It verifies the arbitrary
exchange formula exhaustively on `n=3`, confirms that the protector witnesses
occur in a globally minimum-waste tree, and prints the three counterexamples
used above.
