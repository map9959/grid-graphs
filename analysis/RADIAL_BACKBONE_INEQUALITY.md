# Radial backbone inequality: exact obstruction

## Status

I did not obtain a proof of

```text
a_H+a_F+r_UU >= r_UF+2r_FF+4.                         (R4)
```

Nor did I find a full-grid counterexample.  The argument that initially looks
like a proof by contracting the two boundary cycles is not valid: the inner
disk can join several arcs of the inner cycle before the radial incidence
graph is formed.  This note gives the exact rank inequality that remains, an
explicit counterexample to the annular-only version, and the precise point at
which cyclic-word, Euler, unit-cell, and contraction arguments stop.

The existing exhaustive results through `n=5` remain the strongest rigorous
verification of (R4).  The analysis below does not promote the conjecture to a
theorem.

## 1. The annulus and its four exceptional cells

Let `B` be the boundary cycle of the `n x n` grid and let `C` be the boundary
cycle of the inner `(n-2) x (n-2)` grid.  For `n>=4`,

```text
|B| = 4n-4,          |C| = 4n-12,          |R| = 4n-8,
```

where `R` is the set of radial edges from `B` to `C`.

The radial map is not a matching.  Every noncorner vertex of `C` is the inner
endpoint of one radial edge, while every corner of `C` is the inner endpoint
of two radial edges.  Hence

```text
|R| = |C|+4.
```

Equivalently, the annulus is a cyclic chain of `4n-8` cells.  At an ordinary
cell, two consecutive spokes have distinct adjacent inner endpoints and one
outer edge between their outer endpoints.  At each of four corner cells, the
two spokes have the same inner endpoint and their outer endpoints are joined
by a two-edge path through an outer corner.  Treating the annulus as an
ordinary ladder loses exactly these four doubled spokes.

For a radial edge, the first letter below is its outer label and the second its
inner label.  Thus `r_UF`, for example, counts a spoke from an outer `U` to an
inner `F`.

## 2. The exact contraction identity

Put

```text
K_H = H[I],                    K_F = G[I cap F],
```

where `I` is the whole inner `(n-2) x (n-2)` grid, not merely its boundary
cycle `C`.  Contract every component of `H[B]` and every component of `K_H`.
Keep the radial `H`-edges.  Since `H` is a forest, the resulting incidence
multigraph `J_H` is a forest.  Define `J_F` in the same way using the boundary
`F`-runs, the components of `K_F`, and the `FF` spokes.

For `X` equal to `H` or `F`, let

```text
i_X = number of inner-component vertices incident with J_X,
k_X = number of nontrivial connected components of J_X.
```

Each nontrivial component of `J_X` is a tree.  If it has `a` boundary vertices
and `i` inner vertices, it has `a+i-1` edges.  Summing over its `k_X`
nontrivial components gives

```text
mu_H = i_H-k_H,                mu_F = i_F-k_F.          (1)
```

Since `rho_U=r_UU+r_FU` and the exact radial ledger gives

```text
a_H+a_F+r_UU-r_UF-2r_FF = rho_U-mu_H-mu_F,
```

(R4) is exactly the following rooted-rank inequality:

```text
(i_H-k_H)+(i_F-k_F) <= rho_U-4.                        (2)
```

This is a useful simplification, but not a proof.  It says that the two
simultaneous ranks with which the outer cycle joins components of the inner
`H`- and `F`-forests must leave four units of the weighted inner-boundary
`U` count.  Notice that an inner `F` component participates in both forests,
so the two ranks cannot be bounded independently and then added.

## 3. Why the tempting cyclic proof is false

If one contracts components of `H[C]` and `F[C]`, rather than components of
the full inner graphs, a clean cyclic identity appears.  Let

```text
p_H = c(H[C]),                 p_F = c(G[C cap F]),
z   = number of U-labelled corners of C.
```

The cycle `H[C]` must have a deleted `UU` edge.  For a mixed cyclic word on
`C`, the number of `H[C]` components is the number of `UU` edges, and the
number of `F[C]` components is the number of `F` runs.  Therefore

```text
p_H+p_F = |U cap C|.
```

The same identity holds when all of `C` is `U`, with `p_F=0`.  Because inner
corners have two spokes,

```text
rho_U = |U cap C|+z.                                      (3)
```

If `j_X` boundary-cycle components are incident with radial edges and `ell_X`
is the number of nontrivial components of the corresponding cycle-incidence
forest, its merger rank is `j_X-ell_X`.  Equations (3) then turn the apparent
reserve into

```text
z + (p_H-j_H) + (p_F-j_F) + ell_H + ell_F.             (4)
```

Here `p_X-j_X` counts unattached inner-cycle components.  Formula (4) explains
why a four-corner proof looks plausible: one tries to assign each inner corner
to its `U` label, an unattached component, or an incidence component.

That assignment does not exist in general, even when the annular `H` graph is
a forest.  For every `n>=5`, label all of `B` by `U`; on `C`, label only the
top-left corner `(1,1)` and its right neighbor `(1,2)` by `U`.  Ignore the
strictly enclosed vertices.  Then:

* all outer-cycle edges are deleted from `H`;
* exactly one inner-cycle edge, `(1,1)(1,2)`, is deleted, so `H[C]` is a path;
* every spoke ending at an inner `F` is an isolated leaf attached to that
  path; and
* every spoke ending at either of the two inner `U` vertices is deleted.

Thus the annular `H` graph is a forest.  The inner `U` corner contributes two
spokes and `(1,2)` contributes one, so

```text
r_UU=3,   r_UF=4n-11,   r_FU=r_FF=0,
a_H=4n-11,   a_F=0.
```

Consequently its radial margin is exactly

```text
a_H+a_F+r_UU-r_UF-2r_FF = 3.                           (5)
```

This disproves every proof that uses only the two labelled cycles, the spokes,
and forestness of the annular subgraph.  In particular, the four doubled
spokes do not by themselves provide four units.

It is not a counterexample to (R4).  The prescribed annulus has no completion
to a full forest in the tested cases.  For `n=5`, the center is joined in `H`
to at least three vertices of the existing inner path, immediately creating a
cycle.  The checker exhausts all labels of the strictly enclosed square and
finds no completion for `5<=n<=8` (respectively `2`, `16`, `512`, and `65536`
completions tested).  This computation is finite evidence only; the structural
reason is that the interior disk must attach to the inner-boundary path in too
many places.

## 4. Euler and contraction attempts

Euler's formula for the two incidence forests gives exactly (1).  Applying
Euler first to the annular graph gives (4), but then the interior can merge
components of `H[C]` and `F[C]`.  Let `q_H` be the number of components of
`H[I]` that meet `C`, and define `q_F` similarly.  The ranks of the two
interior boundary-merger forests are exactly

```text
lambda_H = p_H-q_H,            lambda_F = p_F-q_F.
```

Indeed, contract each full inner component that meets `C`; if it contains `s`
components of the boundary restriction, it contributes `s-1`, and summing
gives `p_X-q_X`.  Components disjoint from `C` contribute zero.  Performing
these contractions before the radial contractions yields the full incidence
forests of Section 2 and hence reproduces (2).  There is no sign with which
either `lambda` can be discarded: an interior `F` path is simultaneously an
`H` path, while paths through inner `U` vertices belong only to `H`.

Contracting the full inner components avoids that bookkeeping, but it erases
their cyclic order on `C`.  Contracting only their boundary traces preserves
the order, but introduces exactly the two uncontrolled interior merger ranks.
Thus the two natural contraction orders are equivalent and neither yields an
extra inequality.

A planar-dual restatement has the same obstruction.  The deleted `UU` edges
form a connected dual subgraph spanning all cell faces.  In the annulus-only
example above, the deleted edges connect the annular faces correctly only
relative to the unmodelled inner face.  Replacing that inner face by the full
disk forces additional dual connectivity, but converting that requirement
into the simultaneous primal ranks in (2) is precisely the missing lemma.

## 5. Unit-cell attempt

Every ordinary annular cell has a `UU` edge on its four-edge boundary, since
otherwise that unit cycle survives in `H`.  At a corner cell whose inner
corner is `F`, neither spoke can be `UU`; therefore its outer corner is `U`
and at least one of the two neighboring outer vertices is `U`.  This is the
correct local consequence of the doubled-spoke geometry.

The margin-three annulus satisfies all of these local conditions.  Hence a
sum of independent cell inequalities cannot prove (R4).  A valid unit-cell
proof would have to use global connectivity of the deleted-edge dual inside
`C`, not merely one deleted edge per cell.  Once that connectivity is retained,
the required global rank statement is again (2).

## 6. Exact blocker and weaker conclusion

The exact unresolved statement is:

**Boundary-rooted two-forest rank lemma.**  Let `U` label an `m x m` grid,
let `H=G-E(G[U])` be a forest, and attach the next outer grid cycle.  If the
larger `H` is still a forest, then the sum of the ranks with which that outer
cycle joins components of `H` and of `G[F]` is at most the weighted number of
boundary `U` vertices minus four.

With `m=n-2`, this lemma is exactly (2), hence exactly (R4); it is not a weaker
assumption disguised as progress.  The annular-only replacement of the lemma
is false by (5).

No new nontrivial weaker inequality is proved here.  The rigorously
established statement is the exact identity

```text
rho_U-mu_H-mu_F
  = a_H+a_F+r_UU-r_UF-2r_FF,                           (6)
```

together with complete verification of `rho_U-mu_H-mu_F>=4` through `n=5`
from the existing exhaustive checkers.  Formula (6) helps isolate the needed
rank theorem but supplies no new lower bound and does not advance the main
induction by itself.  Thus there is no weaker theorem here that helps the
induction.  Even (R4) would only give `mu_H+mu_F<=rho_U-4`; the inherited term
`Q_U^o=rho_U` is still subtracted, so the component-resolved inherited-potential
problem remains.

## 7. Reproduction

The independent checker verifies the cycle sizes, the four doubled spokes,
the annular margin-three construction, and nonextendability through `n=8`:

```text
python3 -m analysis.bounds.check_radial_backbone_inequality
```

It does not claim to verify (R4) for arbitrary size.
