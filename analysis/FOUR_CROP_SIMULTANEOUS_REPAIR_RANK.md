# Four-crop simultaneous-repair rank

## 1. Scope and outcome

This note attempts a purely planar induction for the forced-forest bound.  Let

```text
G = G_n,             V(G)=F disjoint-union U,
H = G-E(G[U]),       H a forest.                         (1)
```

Thus every edge incident with `F` is forced.  The desired inequality is

```text
3|F| <= n^2+3n-4.                                      (2)
```

For `n>=6`, use the four corner-anchored `(n-3) x (n-3)` crops: retain either
the first or the last `n-3` rows, independently retain either the first or the
last `n-3` columns, and call the resulting rectangles `Q_NW,Q_NE,Q_SW,Q_SE`.
The same argument applies to any specified four total-three crops.

The approach gives three rigorous statements.

1. There is an exact frame-loss/component-split identity.  Because every
   component of `G[F]` is a straight interval, only `H`-components can split
   under a crop.
2. Simultaneous repairs have an exact graphic formulation after contracting
   the components of the cropped forest.  This gives an explicit sufficient
   four-crop rank inequality and proves that inequality would close the
   `n -> n-3` induction.
3. Planarity makes the crop-boundary component partitions noncrossing and the
   outside reconnection graph a forest.  It does not prove the repair-rank
   inequality.  The missing datum is bundle independence: cyclic order forgets
   both parallel edges in the component quotient and which omitted edges are
   forced together when one `U` vertex is changed to `F`.

No enumeration or computer-assisted evidence is used below.  No proof of (2)
is claimed.

## 2. Crop notation

Fix one crop `Q`, put `m=n-3`, and write

```text
F_Q = F intersect Q,          U_Q = U intersect Q,
H_Q = H[Q],                   ell_Q = |F setminus Q|.
```

Let `b(F)` be the boundary deficiency of `F` in `G_n`, with a corner counted
twice, and let `b_Q(F_Q)` be the analogous quantity in the `m x m` crop.  Let

```text
c_F  = c(G[F]),               c_F(Q) = c(G[Q][F_Q]),
c_H  = c(H),                  c_H(Q) = c(H_Q).
```

Components with no vertex in `Q` are called vanished.  Denote their numbers by
`v_F(Q)` and `v_H(Q)`.  If `a_H(Q)=c_H-v_H(Q)` is the number of old
`H`-components meeting `Q`, define the net `H`-split rank

```text
sigma_H(Q) = c_H(Q)-a_H(Q).                              (3)
```

Thus an old component whose intersection with `Q` has `s` components
contributes `s-1` to `sigma_H(Q)`.

## 3. Straight intervals remove the `F`-split term

**Lemma 3.1 (straight interval restriction).** Every component of `G[F]` is a
horizontal or vertical grid interval.  Its intersection with a contiguous
rectangle is therefore empty or connected.  Consequently

```text
c_F(Q)=c_F-v_F(Q).                                      (4)
```

**Proof.** Three forced vertices on a two-edge grid walk cannot make a right
angle: together they would occupy three corners of one unit cell, and all four
edges of that cell would then be in `H`, contrary to acyclicity.  Hence a
connected `F`-component lies in one row or one column.  Connectivity in the
induced grid graph then fills every vertex between its extreme vertices, so it
is an interval.  The intersection of two intervals on one line is empty or an
interval.  Distinct old components cannot merge after restriction.  This
proves (4).  QED

This is stronger than merely saying that `G[F_Q]` is a forest.  It shows that
all positive component creation in a crop belongs to `H`, not to `G[F]`.

## 4. Exact frame-loss identity

The forest ledger on the large square and on the crop is

```text
3|F|   = n^2+b(F)-c_F-c_H,
3|F_Q| = m^2+b_Q(F_Q)-c_F(Q)-c_H(Q).                    (5)
```

Since `n^2-m^2=6n-9`, subtracting the two equations and using (3)-(4) gives the
following exact identity.

**Proposition 4.1 (frame loss equals exposed split rank).**

```text
3(ell_Q-2n)
  = -9+b(F)-b_Q(F_Q)-v_F(Q)+sigma_H(Q)-v_H(Q).          (6)
```

Equivalently,

```text
sigma_H(Q)
  = 3(ell_Q-2n)+9-b(F)+b_Q(F_Q)+v_F(Q)+v_H(Q).          (7)
```

**Proof.** In (5), substitute `|F_Q|=|F|-ell_Q`,
`c_F(Q)-c_F=-v_F(Q)`, and
`c_H(Q)-c_H=sigma_H(Q)-v_H(Q)`, then rearrange.  QED

Formula (7) is the precise valid version of “high frame loss forces many
component splits.”  Frame loss above `2n` gives three units of split rank per
lost `F` vertex only after paying the change in boundary deficiency and the
vanished-component terms.  Dropping those terms is not justified.

Summing over the four crops gives the equally exact simultaneous ledger

```text
sum_Q sigma_H(Q)
  = 3 sum_Q (ell_Q-2n) + 36 - 4b(F)
      + sum_Q (b_Q(F_Q)+v_F(Q)+v_H(Q)).                 (8)
```

This is a genuine four-crop rank identity, but `sigma_H` is outside
reconnection rank, not yet repair rank.

## 5. Noncrossing boundary components

Traverse the boundary of `Q` cyclically and label every encountered vertex by
its component of `H_Q`.  Repeated vertices of one label form a block of a
noncrossing partition.

**Lemma 5.1 (noncrossing labels).** Two distinct `H_Q`-components cannot occur
in cyclic order `A,B,A,B` on the crop boundary.  The same is true for the
components of `G[F_Q]`.

**Proof.** A path in `A` joining the two selected `A` occurrences can be
perturbed at incidental boundary contacts to a crosscut of the closed crop
disk.  Its endpoints separate the two selected `B` occurrences on the boundary.
Every path between those occurrences must meet the crosscut by the Jordan
curve theorem, contradicting disjointness of `A` and `B`.  QED

There is also a canonical independent interpretation of `sigma_H(Q)`.  For
each old `H`-component meeting `Q`, contract every component of its intersection
with `Q` and contract every component of its part outside the interior of `Q`.
Keep the crossing edges.  The resulting incidence multigraph is a forest,
because it is obtained from a subgraph of `H` by contractions.  In each of its
trees, root one cropped-component vertex.  Every other cropped-component
vertex supplies one fundamental cut separating it from the root; equivalently,
successively adjoining the cropped-component vertices has partition-merger
rank one each.  There are exactly `s-1` such independent split tokens when an
old component has `s` cropped pieces, and hence exactly `sigma_H(Q)` in total.
The connecting paths may share outside edges, so this statement is deliberately
about partition rank, not an injection into distinct physical outside edges.

Thus (7) really does produce independent *splits*.  The remaining question is
whether those splits can be represented by independent repairs inside `Q`.

## 6. Exact bundled graphic rank of repairs

The omitted edges of `H_Q` are exactly the `U_Q-U_Q` grid edges.  Contract each
component of `H_Q` to one vertex.  For an omitted edge `e=xy`, let `bar(e)` be
the corresponding edge in the resulting multigraph; it may be a loop or may be
parallel to another edge.

For `u in U_Q`, define its forced bundle

```text
B_Q(u) = {bar(uv): v in U_Q and uv is a grid edge}.      (9)
```

Changing `u` from `U_Q` to `F_Q` inserts the entire bundle, not a chosen edge
of it.  For `R subseteq U_Q`, put `B_Q(R)=union_(u in R) B_Q(u)`.  An edge with
both endpoints in `R` is included only once.

**Lemma 6.1 (exact simultaneous-repair criterion).** The repaired forced graph
on `F_Q union R` is acyclic if and only if the quotient multigraph
`B_Q(R)` is a forest, where a loop is a cycle and two parallel edges form a
two-cycle.

**Proof.** The repaired graph is obtained from the forest `H_Q` by inserting
exactly the omitted edges represented by `B_Q(R)`.  Contracting every tree
component of `H_Q` preserves and reflects cycles made using inserted edges: a
quotient cycle lifts through the unique paths in the contracted trees, while
contracting a cycle in the repaired graph gives a loop, a parallel pair, or a
longer cycle in the quotient.  QED

Define the bundled repair rank

```text
rho(Q) = max {|R|: R subseteq U_Q and B_Q(R) is a forest}.              (10)
```

This is the exact quantity needed by crop induction.  It is not the ordinary
graphic rank of all omitted quotient edges.  The ground objects in (10) are
overlapping edge bundles indexed by vertices.

## 7. The sufficient four-crop inequality

Set

```text
d(Q) = max(0,ell_Q-2n).                                (11)
```

The desired simultaneous-repair statement can now be made explicit.

**Four-crop bundled-rank inequality (FR).**

```text
sum_(Q in {NW,NE,SW,SE}) rho(Q) >= sum_Q d(Q).          (FR)
```

An explicit injection form, stronger than `(FR)`, is as follows.  For every
crop make `d(Q)` formal demand tokens.  Inject the tokens tagged by `Q` into
distinct vertices `r_Q(t) in U_Q` so that

```text
union_t B_Q(r_Q(t))
```

is a forest for each fixed `Q`.  Lemma 6.1 then proves that all selected
vertices are a simultaneous repair of that crop.

Here is a useful sufficient condition on such an injection.  Order the tokens
of one crop.  Require each new bundle to be a tree in the component quotient,
to meet the union of the earlier bundles in exactly one quotient vertex, and
to have every other quotient vertex fresh.  Induction on the token order shows
that the union remains a forest.  This is a concrete “private child component”
condition; unlike bare cyclic order, it controls independence.

**Proposition 7.1.** If `(FR)` holds for every forced forest on `G_n`, and (2)
holds for side `n-3`, then (2) holds for side `n`.

**Proof.** If some crop has `d(Q)=0`, use that crop with no repair.  Otherwise,
if every crop had `rho(Q)<d(Q)`, integrality would give
`sum_Q rho(Q)<sum_Q d(Q)`, contrary to `(FR)`.  Hence some crop has a repair
`R` with

```text
|R| >= ell_Q-2n.
```

Apply the side-`n-3` bound to the repaired forced forest:

```text
3(|F|-ell_Q+|R|) <= (n-3)^2+3(n-3)-4 = n^2-3n-4.
```

Since `3|R|>=3ell_Q-6n`, rearrangement gives
`3|F|<=n^2+3n-4`.  QED

Thus `(FR)` is neither bookkeeping equivalent to (2) nor an owner-only Hall
statement.  It is a precise sufficient rank lemma for the proposed induction.

## 8. Where the planar injection stops

Equations (7)-(8) and Lemma 5.1 suggest assigning split tokens to boundary
interfaces and repairing inward in the nesting order of the noncrossing
partition.  This does not establish the private-child condition in Section 7.
There are two exact losses of information.

### 8.1 Parallel quotient edges

Suppose two components `A` and `B` have nonalternating boundary occurrences,
for example cyclic word

```text
A A B B.
```

Two separated candidate repairs may each contain one omitted edge from `A` to
`B`.  Either candidate alone is valid.  Selecting both puts two parallel
`A-B` edges in the contracted quotient and therefore creates a cycle.  In the
plane, the two edges together with the unique paths in `A` and `B` form a
Jordan curve.  The Jordan argument detects the dependence after both edges
are chosen; it does not choose one candidate or provide a second fresh
component for the other.

The cyclic word is identical whether there is one `A-B` candidate or many.
Straightness of `G[F]` does not restore the missing multiplicity: `A` and `B`
may be carried by straight interval components with comb teeth while the
boundary partition remains `A A B B`.

### 8.2 Bundles rather than selectable edges

A repair vertex can force two, three, or four omitted edges at once.  Even if a
distinguished edge represents a desired split, another edge in the same bundle
may be a loop in the quotient, may be parallel to an earlier edge, or may close
a longer cycle.  Conversely, a star bundle can consume several units of
ordinary graphic rank while contributing only one repaired vertex to (10).

The noncrossing partition records only

```text
boundary occurrence -> H_Q-component.
```

Bundle independence depends on the strictly richer map

```text
repair vertex -> multiset of edge-labelled pairs of H_Q-components.     (12)
```

Neither cyclic order nor the number `sigma_H(Q)` determines (12).  Nested
blocks may repeatedly use the same parent component, and two locally valid
bundles may have no private child even though every component block is
noncrossing.

## 9. Exact blocker

The planar part realizes the split count `sigma_H(Q)` as independent
fundamental-cut tokens of an **outside connector forest**.  The induction needs
an injection of only `d(Q)` tokens into vertices whose **inside forced
bundles** form a forest.  There is no canonical map from the first graphic
object to the second.

More precisely, a completion of this proof must establish at least one of the
following genuinely stronger facts.

1. A private-child theorem assigning enough outside split edges to repair
   vertices so that every assigned bundle introduces a fresh quotient
   component.
2. A bounded-congestion theorem showing that the parallelism and extra edges
   in (12) lose no more rank than the boundary and vanished-component credits
   in (7).
3. A direct four-crop inequality `(FR)` that retains the full edge-labelled
   bundle multigraphs, not merely their cyclic component partitions.

Without one of these additions, the proposed implication

```text
large frame loss -> many H splits -> equally many simultaneous repairs
```

breaks at its second arrow.  The first arrow is exactly (7); the second is not
a consequence of planar noncrossing.  Cyclic order controls alternation of
component blocks, while simultaneous repair is graphic independence of
edge-labelled, overlapping bundles.  Jordan curves explain the resulting
cycles but do not prevent parallel bundle reuse.
