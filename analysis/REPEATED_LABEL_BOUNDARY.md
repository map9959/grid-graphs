# Repeated-label boundary lemma

## 1. Outcome

This note isolates the repeated-label boundary lemma `(RL)` from
`FOREST_EXTREMAL_INDUCTION.md`.  The attempted component charge does not prove
it.  There are three main conclusions.

1. The contracted component-incidence graph is a forest, and the component
   labels of `H` on the cyclic boundary are noncrossing.
2. The restriction to configurations satisfying `(M3)` does not make `(RL)` a
   weaker theorem.  The assertion of `(RL)` for all such configurations is
   logically equivalent to the original universal bound `(T)`.
3. The natural discharge of boundary incidences above `3n-4` fails if a token
   may use only its owning `F` and `H` components, even under `(M3)`.  Allowing
   all components instead makes the required capacity inequality exactly
   `(RL)`.  Repeated labels do not bridge this gap: their witnesses already
   have unavoidable congestion on a `2 x 2` maximal example.

Thus no proof of `(RL)` is claimed.  The exact blocker is a non-owner,
bounded-congestion rule that makes interior `H` components available to the
boundary.  M3 gives existence of repeated labels but no such congestion bound;
planar noncrossing gives order but no such availability rule.

## 2. Setup and exact equivalence

Let

```text
H=G_n-E(G_n[U]),             F=V(G_n)-U,
c_F=c(G_n[F]),               c_H=c(H).
```

Let `b_F` count one incidence at each noncorner boundary vertex of `F` and two
at each corner.  For every forest-valid configuration, the edge ledger gives

```text
3|F|=n^2+b_F-c_F-c_H.                              (1)
```

Condition `(M3)` says that, for every `u in U`, the `H`-component labels on

```text
S(u)={u} union (N(u) intersect U)
```

contain a repetition.  The proposed lemma is

```text
b_F <= 3n-4+c_F+c_H.                               (RL)
```

**Proposition 2.1.** The assertion of `(RL)` for every forest-valid
configuration satisfying `(M3)` is equivalent to the universal assertion

```text
3|F| <= n^2+3n-4                                  (T)
```

for every forest-valid configuration.

**Proof.** If `(T)` holds universally, substitute `(1)` to get `(RL)`, in
particular on the M3 class.  Conversely, start from any forest-valid `F` and
repeatedly change a vertex from `U` to `F` whenever this preserves forestness.
The finite process stops at a set `F*` satisfying `(M3)` by the exchange lemma.
Applying `(RL)` and `(1)` to `F*` gives

```text
3|F*| <= n^2+3n-4.
```

Since `F` is contained in `F*`, the same bound holds for `F`.  QED

Consequently, M3 is a useful normal form, but calling `(RL)` a strictly
narrower sufficient target overstates the reduction.  It is syntactically
narrower and locally recognizable after components are known, but its
universal truth has exactly the strength of `(T)`.

## 3. Incidence forest and boundary order

Contract each component of `G_n[F]` in `H`.  Let `J` be the resulting bipartite
graph, with one color class consisting of the `F` components and the other
consisting of the individual vertices of `U`.  Its edges are the `F-U` grid
edges.

**Lemma 3.1 (incidence forest).** `J` is a forest.  Its connected components,
together with isolated `U` vertices, are exactly the components of `H`.

**Proof.** Contracting edges in a forest cannot create a cycle, including a
two-cycle of parallel edges.  Contracting every `F-F` edge of `H` gives `J`.
Contraction also preserves the component partition.  QED

In particular, two vertices of `U` have the same `H` label exactly when they
belong to the same tree of `J`.  Thus M3 has the following exact form:

> For every `u in U`, some two vertices of `S(u)` lie in the same tree of `J`.

It is important that the repeated pair need not contain `u`; see Section 5.

**Lemma 3.2 (noncrossing boundary labels).** Let `A` and `B` be two distinct
components of a plane graph embedded in a closed disk.  Their boundary
occurrences cannot alternate cyclically as `A,B,A,B`.  Hence the labels of the
components of `H` on the boundary cycle of the grid form a noncrossing
partition.  The same holds for the components of `G_n[F]`.

**Proof.** If four boundary points occurred in alternating order, join the two
`A` points by a path in `A` and the two `B` points by a path in `B`.  A small
perturbation at any additional boundary contacts turns the first path into a
crosscut of the disk.  Its endpoints separate the two selected `B` points on
the boundary, so every path between them intersects the crosscut.  This
contradicts disjointness of the components.  QED

This proves the suggested planar restriction, but it gives no numerical bound
on repetitions.  Arbitrarily deep nested noncrossing words are topologically
possible.  More importantly for `(RL)`, a component may have no boundary
occurrence at all, so the cyclic word does not record every available `c_H`
credit.

## 4. Discharging above `3n-4`

Regard `b_F` as a set of boundary-incidence tokens, with a corner represented
twice.  Give `3n-4` tokens for free and give each `F` component and each `H`
component capacity one.  Merely asking whether all remaining tokens fit in
these undifferentiated capacities says

```text
b_F-(3n-4) <= c_F+c_H,
```

which is exactly `(RL)`.  This version of the discharge is bookkeeping, not a
proof.

The first noncircular localization is to let a boundary token use only its
owning `F` component and its owning `H` component.  For a set `X` of tokens,
write `phi_F(X)` and `phi_H(X)` for those owner sets.  Unit-capacity matching,
with the common free reservoir, requires the Hall inequalities

```text
|X| <= 3n-4+|phi_F(X)|+|phi_H(X)|                 (OH)
```

for every `X`.

There is a convenient exact test for `(OH)`.  For each boundary-owning `F`
component `C`, let `w(C)` be its number of boundary incidences.  Group these
components by their containing `H` component `D`.

**Lemma 4.1 (owner-Hall optimization).** The maximum over token sets `X` of

```text
|X|-|phi_F(X)|-|phi_H(X)|
```

is

```text
sum_D max(0, sum_(C contained in D) (w(C)-1)-1),      (2)
```

where only boundary-owning `F` components occur in the inner sum.

**Proof.** Once `X` uses an owner `C`, adding all other tokens of `C` increases
the objective without adding an owner.  For a fixed `H` owner `D`, adding a new
`F` owner changes the objective by `w(C)-1`, which is nonnegative.  Therefore a
profitable group uses all its boundary-owning `F` components, pays one for each
of them and one for `D`, and groups with negative total are omitted.  Different
`H` owners are independent.  QED

The owner rule is false even after maximalization.

**Proposition 4.2.** For every `n>=17`, there is a forest-valid configuration
satisfying `(M3)` for which `(OH)` fails.

**Proof.** Start with `F` consisting of

* the noncorner vertices on the left and right sides; and
* columns `2,...,n-3` on the top and bottom sides.

The four boundary paths and their inward teeth are four disjoint trees, so `H`
is a forest.  Let `X` be the incidences of these original boundary vertices.
Then

```text
|X|=4n-12,       |phi_F(X)|=4,       |phi_H(X)|=4.
```

Greedily enlarge `F` until M3 holds.  Every original token remains, while
adding vertices to `F` can merge its `F` and `H` owners but cannot split them.
Thus the two owner counts of this fixed `X` remain at most four.  Inequality
`(OH)` would imply

```text
4n-12 <= 3n-4+4+4=3n+4,
```

which is false exactly when `n>=17`.  QED

This also explains why the many initially isolated interior components of `H`
cannot simply be discarded.  They are global credits in `(RL)`, but they do
not own the boundary tokens that need them.

## 5. What M3 does not supply

A repeated label at `u` is an `H` component occurring at least twice on
`S(u)`.  One might assign each `u` to one such witness and then route charge
through distinct witnesses.  Even the injective first step is false.

**Counterexample 5.1 (reused witness).** In the `2 x 2` pattern

```text
U.
U.
```

`H` is one tree.  Both `U` vertices satisfy M3, and their only repeated label
is the single component of `H`.  The pattern is inclusion-maximal in `F`, but
there is no matching from its two `U` vertices to repeated-label witnesses.

Congestion is not caused only by the small grid.  In the maximal pattern

```text
U.U
U.U
U.U
```

`H` is a spanning tree and its one label witnesses M3 at all six `U` vertices.

Nor can the repeated pair always be chosen to include the center `u`.  In

```text
.UU
.UU
.U.
```

the top-right vertex `u` has a component label different from both of its `U`
neighbors, while those two neighbors have the same label.  Thus M3 at `u` is
certified only by the second alternative in the exchange lemma.

These examples invalidate two direct ways of converting M3 into component
capacity.  Noncrossing does not repair them: all labels in the first two
examples are identical, so their boundary words are maximally noncrossing.

## 6. Exhaustive tests

`check_repeated_label_boundary.cpp` enumerates all binary patterns through
`n=5`.  It independently constructs `H`, its component labels, `G_n[F]`, and
the owner groups in `(2)`.  The complete census is

```text
n   forest-valid   M3-maximal   minimum RL slack
2              9            4                  0
3            100           26                  2
4          2,278          138                  0
5        116,252        2,164                  3
```

Here the RL slack is `3n-4+c_F+c_H-b_F`, minimized over M3 patterns.  The
checker also establishes over these finite domains that

* no forest-valid boundary label word violates Lemma 3.2;
* no M3 pattern violates owner Hall through `n=5`;
* witness matching fails from `n=2` onward;
* center-involving repetition fails from `n=3` onward; and
* every repeated-label witness component in an M3 pattern through `n=5`
  touches the boundary.

The last observation is a strengthened intermediate claim with finite support
only; no proof is known here.  Even if true in general, boundary contact alone
does not bound how many M3 neighborhoods one component can witness, as the
`3 x 3` one-label example shows.

Compile and run the complete check with

```bash
g++ -O3 -march=native -fopenmp \
  analysis/check_repeated_label_boundary.cpp \
  -o /tmp/check_repeated_label_boundary
/tmp/check_repeated_label_boundary
```

## 7. Exact blocker

The proposed proof reaches the following fork.

* Restrict each excess boundary token to its geometrically evident owner
  components.  The resulting Hall statement is genuinely stronger than RL,
  but Proposition 4.2 disproves it under M3.
* Permit a token to use arbitrary components, including interior components
  with no boundary ownership.  The capacity condition is exactly RL and hence,
  by Proposition 2.1, exactly the original theorem.
* Use M3 witnesses to expose those non-owner components.  Counterexample 5.1
  shows that witnesses have no unit congestion, while planar noncrossing only
  orders components that already reach the boundary.

Therefore the missing statement cannot be just maximality, noncrossing of the
boundary word, or acyclicity of the incidence graph.  It must quantitatively
route concentrated boundary demand to non-owner `H` components with a capacity
that tolerates repeated M3 witnesses.  No such route or compensating weighted
charge is established here; asserting its total capacity without localization
is precisely `(RL)` again.
