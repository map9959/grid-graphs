# Residue-Two Component Budget Reassessment

Date: 2026-09-05. Status: independently reviewed deductions from the existing
exact ledger. The five-unit boundary bound and target component obstructions
are now proved in `lean/GridGraphs/Accounting/BoundaryFiveBudget.lean`. Equality corner
counts, the unique perimeter gap, and next-ring exclusion are also checked in
`BoundaryFiveEquality.lean`; the remaining peeling geometry is paper-level. This is
not a solution of the conjecture. No optimization or finite grid search was used.

## 1. One Objective For Both Sides

Let `n=3k+2`, `G=gridGraph n n`, `U=V\F`, and let `H` contain every grid
edge incident to `F`. Assume `H` is a forest. Define

```text
f = |F|,
r = number of components of G[F],
c = number of components of H on ALL n^2 vertices,
b = sum_(u in U) (4-deg_G(u)),
B = r+c+b.
```

In particular, isolated U vertices count toward `c`, and U corners count twice
toward `b`. The existing `grid_component_reduction` and total boundary
deficiency `4n` give

```text
3f+B = n^2+4n = 9k^2+24k+12.                         (1)
```

For completeness, sum grid degrees over F. This gives `4f-(4n-b)`.
Subtract the `f-r` internal F edges that were counted twice to get
`|E(H)|=3f+r-4n+b`. Forest Euler gives `|E(H)|=n^2-c`, proving (1).

This identity is old. Its following consequences reorganize the research
targets; they must not be mistaken for a proof of the required minimum.

The forced-set optimization equivalence implies

```text
3P(3k+2) + min_(F feasible) B(F) = 9k^2+24k+12.
```

Consequently the conjecture is exactly

```text
min B = 3k+9,   1 <= k <= 4,
min B = 3k+12,  k >= 5.                              (2)
```

For stable target deficit `d=(3k^2+7k)-f`, an integer possibly negative,

```text
B = 3k+12+3d.                                       (3)
```

The affine score `3k^2+6k+5` therefore has `B=6k-3`, irrespective of how
its component and boundary contributions are individually distributed.
It pays `3(k-5)` excess units. An exact successor has `Delta B=3`; the
affine successor has `Delta B=6`.

A direct proof of `B>=3k+12` for all feasible F when `k>=5` would close the
stable upper side without first constructing the common channel routing or
proving its two exclusions separately. This is an alternative endpoint, not
a claim that the new inequality is easier. In particular, excluding only the
profiles `B=3k+6` and `B=3k+9` is insufficient without a baseline lower bound.

## 2. A Global Obstruction To The Counter Skeleton

Always `c>=1`. A perimeter UU edge is necessary, or the whole perimeter is a
cycle in H. This alone gives `b>=2`, but the corner cells give substantially
more:

**Boundary lemma.** For every feasible F on an `n x n` grid with `n>=5`,
`b>=5`.

Proof: at each corner, its two boundary neighbors cannot both be F. They are
opposite vertices of the corner unit cell and would force its four edges.
The four pairs of boundary neighbors are disjoint for `n>=4`, so at least
four distinct noncorner boundary vertices are U. If `b<=4`, these are exactly
the boundary U vertices, one from each pair, and no corner is U. No two can
be adjacent when `n>=5`: on one side, the near-corner positions are separated
by `n-3>=2`; noncorner boundary vertices on different sides cannot be adjacent.
There is then no perimeter UU edge, a contradiction. Interior U vertices
do not affect this argument. QED

There is useful rigidity at equality. If `n>=6` and `b=5`, all corners
belong to F and exactly five noncorner boundary vertices belong to U. Choose
one U witness for each corner pair; these four witnesses are pairwise
nonadjacent. The fifth boundary U vertex must be adjacent along a side to
one witness, or the perimeter cycle survives. It cannot be adjacent to two:
near-corner witnesses on the same side are at distance `n-3>=3`, and
noncorner vertices on different sides cannot be adjacent. Consequently there
is EXACTLY ONE perimeter UU edge, and H contains the spanning perimeter path
obtained by deleting it. Every boundary vertex lies in one H component.

This is a useful boundary-first gate for the optional b=5 construction class:
four near-corner choices plus one adjacent extra boundary U vertex determine
its boundary pattern. The unrestricted interior is still the hard problem;
this is not a bounded-interior grammar or a claim that every optimum has b=5.

Thus, for `k>=1`, any stable-target-count feasible set satisfies

```text
r+c+b = 3k+12,
r <= 3k+6.                                          (4)
```

These are global consequences, independent of repair radius or a chosen
coordinate grammar:

| Proposed actual maximal component count | Necessary condition | Impossible range |
|---|---|---|
| `r>=4k+1` | `4k+1<=3k+6` | `k>=6` |
| `r>=4k` | `4k<=3k+6` | `k>=7` |

The counter subdivision in `RESIDUE_TWO_COUNTER_INTERVAL_SURGERY.md` has
`4k+1` nodes and target summed length. It therefore cannot be realized for
any k in its intended range `k>=7` with those nodes as distinct maximal
preserved components. At k=7 the target allows at most 27 components; the
counter demands 29 and even retaining the affine 28 is too many. This is
stronger than the recorded failures of particular owner placements. It does
not invalidate the abstract tree arithmetic. Merging nodes into a maximal
interval changes the specified skeleton; overlapping intervals also require
rechecking its cardinality formula.

The same budget implies average maximal interval length at least

```text
(3k^2+7k)/(3k+6) = k+1/3-2/(3k+6) > k.
```

Hence bounded islands cannot constitute an exact arbitrary-width family.
Tiles remain possible only if segments concatenate into long straight
components. A retained `4k`-component architecture must eventually lose or
merge a linear number of its components. This is not a theorem that every
new family must be obtained by modifying the affine family.

## 3. Physical Connectors Are Particularly Restricted

Two perpendicular F-neighbors of a vertex are opposite corners of a unit
cell. All four cell edges then touch F, contradicting acyclicity. Therefore
every U vertex has zero, one, or two F-neighbors, opposite when there are two.
The same observation ensures G[F] components are straight intervals.

Contract the maximal F intervals, delete pendant U leaves, set isolated U
vertices aside, and suppress the remaining degree-two U vertices. The result
is a forest S whose vertices are the r intervals. For an unverified candidate,
retain parallel edges: two distinct connectors between the same intervals
already create a cycle and must not collapse to one simple edge.

Let `u_j` count U vertices with j F-neighbors, and let `a` count nonisolated
components of H. Then

```text
u_2 = r-a,
c = a+u_0,
B = b+u_2+2a+u_0.                                  (5)
```

Thus an interval-incidence tree can coexist with many isolated U vertices.
Proving that tree connected is not the same as proving H connected. Conversely,
H need only be a forest for a valid lower bound; disconnected incidence is
not itself an obstruction to feasibility.

## 4. Exact Neighborhood And Matching Formulation

This is a second deduction, not an additional upper bound. Assume a candidate
F has straight maximal components, with family I. For `J in I`, let `N(J)`
be its grid neighbors in U, let `ell(J)=|J|`, and let
`b_J=sum_(v in J)(4-deg_G(v))`. No outside vertex has two neighbors in one
straight interval, so

```text
|N(J)| = 2ell(J)+2-b_J.
q(J) = |N(J)|-1.
delta(A) = |union_(J in A) N(J)| - sum_(J in A) q(J).
```

All slack arithmetic here is over integers. Then

```text
H is acyclic iff delta(A)>=1 for every nonempty A subset I.       (6)
```

Proof: the full-neighborhood bipartite graph on `A` and `N(A)` has
`|V|-|E|=delta(A)`. In a forest this is its positive component count.
Conversely, choose all interval vertices on a cycle of the contracted graph.
Their full-neighborhood graph is connected and contains that cycle, hence
has `delta<=0`. Contracting the straight components preserves cycles.

By Hall's theorem, (6) is also equivalent to assigning q(J) distinct tokens
of each J to different vertices of N(J), even after ANY ONE chosen U vertex
is forbidden. The matching may depend on the forbidden vertex. One ordinary
matching, or deleting just one fixed vertex, does not suffice.

Example: the four corners of a 3x3 grid as F have four singleton intervals
with one token each and only four neighbors in total. Ordinary matching
exists, but forbidding a perimeter midpoint defeats it. Here `delta(I)=0`
and H contains the perimeter cycle.

There is an exact uncrossing identity, taking `delta(empty)=0`:

```text
delta(A)+delta(D)-delta(A union D)-delta(A intersect D)
  = |N(A) intersect N(D)|-|N(A intersect D)| >= 0.                (7)
```

If F is feasible, A and D intersect nontrivially, and both have slack one,
then their union and intersection also have slack one, and

```text
N(A) intersect N(D) = N(A intersect D).
```

This gives an exact nonreuse rule for overlapping tight families. However,
under the local connector restriction, `delta(A)=|A|-|E(S[A])|`: this is
ordinary forest sparsity in another form. The missing new mathematics is a
GRID-GEOMETRIC reason that a forbidden score forces a deficient family.
Generic Hall or uncrossing lemmas alone cannot close the problem.

## 5. Revised Analytic Gates

1. Budget before topology. Any proposed exact family must specify symbolic
   r, c, b and satisfy (1), not just sum the interval lengths. Do not promote
   a finite observed component formula to an arbitrary-width theorem.
2. Attempt a successor with `Delta B=3`. Allow a growing ordered interface
   of interval identities and attachment ancestry, including merging old
   intervals. If a merge closes an old attachment path, identify the physical
   connection removed or rerouted. Coordinates and topology should be designed
   together, not in an abstract-tree-first pipeline.
3. One optional sufficient subclass is `b=5, c=1, r=3k+6`. At the target
   it has `u_0=0`, `u_2=3k+5`, `u_1=6k^2+2k-1`. A successor would have
   `Delta r=3`, `Delta u_2=3`, `Delta u_1=12k+8`, and `Delta f=6k+10`.
   This is a conjectural design restriction, NOT a necessary normal form.
   No existing base is asserted to meet it. If it fails, allow other b and c
   budgets rather than infer that the target is impossible.
4. On the upper side, try to prove the minimum in (2) directly by counting
   realized interval neighborhoods. Use (7) only where its nonempty-overlap
   hypothesis holds. The first substantive gate is a geometric inequality or
   classification reducing possible tight profiles; simply restating (2) as
   Hall expansion is not progress. The existing global contour route remains
   available in parallel.
5. Treat the stable formula as falsifiable. A larger feasible score disproves
   its upper side; an unconditional all-configuration lower bound on B above
   `3k+12` at a stable width disproves its lower side. Failure of a construction
   subclass proves neither. No explanation of the k=5 threshold follows yet
   from (1)-(7).

## 6. Resource And Verification Policy

No new exact-grid optimization, enumeration, SAT/SMT, or state-product search
above 15x15. Being at most 15x15 is not permission for a long run. Any proposed
search needs a sharply stated falsification question, explicit runtime/memory
caps, and approval before execution. Prefer no search at this stage.

Checking an already explicit coordinate witness is not optimization: a grid
edge scan and forest check are polynomial. Existing large witnesses may be
inspected or replayed; a short deterministic check of a new explicit witness
may be useful, but no large check was run here. Finite checks remain debugging
evidence, never the arbitrary-width proof.

The five-unit boundary lemma and component obstructions are now checked in
`BoundaryFiveBudget.lean`, with symbolic regression tests at sides 20 and 23.
The full build passed on 2026-09-05 (7,521 jobs); the new theorems depend only
on Lean's standard logical axioms. Both boundary modules and the tests have
subsequently passed on Lean 4.33.1 (8,728 jobs), with the same axiom audits.
The single-gap equality case and all-U next ring are now checked; the remaining
two-way attachment reduction in `BOUNDARY_FIVE_PEELING.md` is still paper-level.
The entire library has not yet completed a full build after the toolchain upgrade.
