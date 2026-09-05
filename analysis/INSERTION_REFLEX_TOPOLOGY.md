# Reflex corners versus insertion topology

## Setup

Let `H=forcedEdgeGraph G F=G-E(G[U])` be a spanning forest of a rectangular
grid, where `U=V-F`.  For `u in U`, let `S_u` be the star of the new `U-U`
edges incident with `u`.  An insertion cycle `C_u` consists of one or two
edges of `S_u` and the unique appropriate path in `H`.  Assume that the
resulting rectilinear cycle is simple, as it is for the canonical circuits in
`CanonicalInsertionCircuit.lean`.

Write

```text
t(C) = number of orthogonal turns of C,
q(C) = number of convex corners of the closed disk bounded by C,
r(C) = number of reflex corners of that disk.
```

The terms "inside" and "enclosed" below mean the open bounded component of
the complement of `C`.  This convention is necessary: an `F`-component used
by the `H`-path generally meets the boundary of the cycle and is not an
enclosed component.

## The exact formulas

### One insertion disk

For every simple rectilinear insertion cycle,

```text
q(C)-r(C)=4,
t(C)=q(C)+r(C)=4+2r(C).                                 (1)
```

This is the complete topological formula for one cycle.  Its disk has Euler
characteristic one regardless of the number of reflex corners.  In
particular, `r(C)` is geometric complexity, not a component or hole count.
For any family with one selected cycle for each owner,

```text
2 sum_(u in U) r(C_u) = sum_(u in U) t(C_u)-4|U|.        (2)
```

Consequently the proposed turning inequality is exactly

```text
2 sum_u r(C_u) + 3|F| + c(G[U]) + 3 <= n^2+3n.          (3)
```

Equation (3) is not a consequence of Euler characteristic.  It is false even
when each owner's circuit is chosen to minimize its reflex corners: the exact
`9 x 9` counterexample and replay are in
`INSERTION_CIRCUIT_CONGESTION.md` and `minimum_reflex_gate.py`.

A weaker unconditional geometric estimate is

```text
2 sum_u r(C_u) <= sum_u (length(C_u)-4),                 (4)
```

because every turn occurs at a distinct cycle vertex.  This has no component
credit and is generally too weak for (3).

### A whole star bundle

For any spanning forest `H` and any added edge set `S`, the cycle rank obeys

```text
beta_1(H union S)
  = |S|-[c(H)-c(H union S)].                            (5)
```

Indeed `|E(H)|=|V|-c(H)`, and (5) follows immediately from
`beta_1(K)=|E(K)|-|V|+c(K)`.  For the full insertion star this specializes to

```text
beta_1(H union S_u)=bundleCycleDefect(H,F,u)
                   = |S_u|-starAttachmentGraphicRank(H,F,u).  (6)
```

Equivalently, after contracting the `H`-components, central loops and repeated
noncentral component labels are precisely the independent cycle events.
This is the exact cycle-space formula.  It contains no turn or reflex term.
A selected insertion cycle supplies one nonzero vector in this cycle space;
its reflex corners do not supply independent vectors.

For the forced-grid specialization, summing the local defect/rank ledger gives

```text
sum_u bundleCycleDefect(u) + sum_u starAttachmentGraphicRank(u)
  = 2|E(G[U])|.                                         (7)
```

The factor two is unavoidable because each physical `U-U` edge occurs in the
star of both endpoints.  Thus even cycle-defect occurrences are not globally
injective without retaining owner labels or paying an endpoint-fiber term.

### Genuine component boundaries

There is an exact component/hole formula, but it applies to boundaries of a
regular neighborhood, not to insertion cycles.  If a compact rectilinear
region `X` has `c(X)` components and `h(X)` holes, orient outer boundaries
positively and hole boundaries negatively.  Then

```text
signedConvex(X)-signedReflex(X)=4(c(X)-h(X)).            (8)
```

For a thin regular neighborhood of a plane graph `K`, `h(X)=beta_1(K)` and
the right side is `4(c(K)-beta_1(K))`.  Formula (8) may be used for a medial
boundary of `G[F]`, `G[U]`, or a support graph.  It cannot be transferred to
`C_u`: an insertion disk is not normally a boundary component of any of those
neighborhoods.

## A forced-grid counterexample

The following `6 x 6` set is inclusion-maximal forced-acyclic:

```text
FUUFUU
FUUUUF
UUUFUF
FFUUUF
UUUUUF
UFFFUF
```

Rows and columns are numbered from zero.  For `u=(0,2)`, the canonical
shortest-lex insertion cycle is

```text
(0,2),(0,1),(0,0),(1,0),(2,0),(3,0),(3,1),(4,1),
(5,1),(5,2),(5,3),(5,4),(5,5),(4,5),(3,5),(2,5),
(2,4),(2,3),(1,3),(0,3),(0,2).                          (9)
```

Only `(0,2)(0,1)` is inserted; all other edges of (9) form the unique `H`
path.  The other `U` neighbor of `u` is `(1,2)`.  Its `H`-component differs
from that of `u`, while `(0,1)` is in the component of `u`.  Hence the full
owner star has two edges, graphic rank one, and

```text
bundleCycleDefect(u)=2-1=1.                             (10)
```

The cycle has eight turns.  By (1),

```text
r(C_u)=(8-4)/2=2.                                       (11)
```

Its strictly interior grid vertices are

```text
(1,1),(1,2),(2,1),(2,2),(3,2),
(3,3),(3,4),(4,2),(4,3),(4,4),
```

and all ten are in `U`.  Moreover `G[U]` is connected.  These facts can also
be checked directly from the displayed six rows.  Forced acyclicity,
inclusion-maximality, canonical selection, the eight turns, and the component
counts are independently replayed by the exact row grammar and insertion
checker used in `insertion_circuit_congestion.py`.

This one example disproves all of the following candidate injections:

```text
reflex corners -> distinct strictly enclosed G[F]-components,
reflex corners -> distinct G[U]-components or component-separation events,
reflex corners -> distinct cycle-basis events created by the owner's star.
```

The respective resource counts are `0`, at most `1` (and zero merger events),
and `1`, whereas there are two reflex corners.  The first failure is stronger
than boundary ambiguity: there is no strictly enclosed `F` vertex at all.

There is also a separate owner-forgetting failure at `2 x 2`:

```text
UU
FF
```

Both owners select the same physical facial cycle.  Thus owner-labelled
cycles, even before corners are considered, do not inject into a global
cycle-space basis or bounded faces.

## What laminarity can and cannot prove

Unique paths in a plane forest do not make insertion disks laminar.  Two
owner-labelled cycles may share a path, meet tangentially, or have overlapping
interiors.  Laminarity therefore requires a separately proved selection or
uncrossing theorem; it cannot be assumed from forest uniqueness.

Even under such an extra theorem, laminarity controls only signed curvature.
For a laminar family of disks, let `k_D` be the number of immediate child
disks of `D`.  The exposed region obtained from `D` by deleting its children
has Euler characteristic `1-k_D`, so

```text
signed turn of the exposed region = 4(1-k_D).           (12)
```

Summing (12) over the containment forest gives `4` times the number of maximal
disks, since the sum of the child counts is the number of nonroots.  Reflex
and convex corners on the individual boundaries cancel in this signed sum.
Their unsigned reflex total can still grow while the containment forest and
all component/hole counts stay fixed.  Noncrossing therefore supplies order,
not the unit-capacity resources needed by (3).

## Rigorous conclusion

The available exact aggregate relations are (2), (6), (7), and (8).  They
live in different ledgers:

```text
reflex geometry:       2R = T-4|U|,
owner cycle space:     beta_u = bundleCycleDefect(u),
global star incidence: sum(beta_u+rank_u)=2|E(G[U])|,
component topology:    signed curvature=4(c-h).
```

No termwise injection between these ledgers is valid, and the new exact gate
shows that no aggregate theorem proving (3) can hold as stated.  Any replacement
must add geometric hypotheses or additional positive slack.
