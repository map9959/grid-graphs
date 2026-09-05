# Checkerboard boundary-run inequality: refutation and local mechanism

This note records finite computational evidence, not a proof or a Lean theorem.
The candidate below is false.  A targeted search beyond the original census
found a `7x7` forced-acyclic counterexample; see the next section.

## Candidate

Let `F` be a forced set in the `n x n` grid whose complete forced-edge graph is
acyclic. For `c` black or white, let:

- `C_c` be the ambient component count of the forest containing every edge
  incident to an `F`-vertex of color `c`; vertices outside its support remain
  isolated;
- `R_c` be the number of cyclic runs in the component-label word obtained by
  reading `C_c` around the grid boundary;
- `d_c` be boundary deficiency on the `F`-vertices of color `c`;
- `U_c` be the number of unforced vertices of color `c`; and
- `Q_c = d_c + U_c + 2 - C_c`.

The census supports the following pair:

```text
2 Q_B + R_B <= 2 A_B + R_W,
2 Q_W + R_W <= 2 A_W + R_B,
```

where

```text
n even: A_B = A_W = 3n/2,
n odd:  A_B = (3n+3)/2, A_W = (3n-3)/2.
```

Black is the larger checkerboard class when `n` is odd. Adding the two
inequalities cancels the run terms and uses `A_B+A_W=3n`, giving exactly twice
`CheckerboardBoundaryBound`:

```text
d_B+d_W + U_B+U_W + 4 <= 3n + C_B+C_W.
```

Thus the pair is sufficient and is not merely the checkerboard bound assigned
color by color. Each half contains the genuinely extra signed term
`(R_other-R_c)/2`.

The pair is not an algebraic restatement of its sum. The `4x4` row masks
`(13,13,9,1)` have `Q_B+Q_W=12=3n`, so the summed checkerboard inequality holds,
but the two candidate margins are `(2,-2)`. Its complete forced graph is cyclic,
as it must be given the exhaustive acyclic census; this negative control also
shows where the acyclicity and path-nonalternation argument has real content.

## Forced-acyclic counterexample

The little-endian `7x7` row masks

```text
79,64,84,65,17,1,125
```

encode

```text
FFFF..F
......F
..F.F.F
F.....F
F...F..
F......
F.FFFFF
```

The complete forced-edge graph has one component on 47 vertices, the two
isolates `(3,3)` and `(4,2)`, and 46 edges.  Its nontrivial component is
therefore a tree, which gives a short forest certificate independent of the
run calculation.  The direct edge-insertion checker verifies the same
certificate.  The color profiles are

```text
(|F_B|,|F_W|) = (12,8),
(R_B,R_W)     = (6,8),
(Q_B,Q_W)     = (14,1).
```

Since `(A_B,A_W)=(12,9)`, the two proposed margins are

```text
(2 A_B + R_W - 2 Q_B - R_B,
 2 A_W + R_B - 2 Q_W - R_W) = (-2,14).
```

Thus the black half says `34 <= 32`.  In the simplified cardinality form it
says

```text
6|F_B| + R_B <= n^2+3n-2 + R_W,
78 <= 76.
```

The white odd-grid target has constant `n^2+3n-6`; these constants follow in
general from `2A_c+2|V_opposite|-4`.  The summed checkerboard inequality still
has slack six on this example.  Hence the failure is genuinely in the proposed
run split, not in its sum.

No counterexample occurs in the exhaustive census through `n=5`.  This search
did not exhaust all `6x6` sets, so `7` is the smallest currently known side,
not a proved minimum.

The opposite color also fails.  The forced-acyclic `9x9` row masks

```text
509,1,137,1,297,257,257,341,273
```

have

```text
(|F_B|,|F_W|,R_B,R_W) = (13,16,6,14),
(Q_B,Q_W)             = (1,9),
(M_B,M_W)             = (36,-2).
```

Here the complete forced graph consists of a 72-vertex, 71-edge tree and nine
isolates.

Thus the simplified white target says `110 <= 108`.  These two examples also
rule out repairing the pair by changing only the odd allowance split while
keeping its sum `3n`.  If the odd bias is `b`, in place of `3`, the black
margin changes by `b-3` and the white margin by `3-b`.  The `7x7` example
requires `b >= 5`, whereas the `9x9` example requires `b <= 1`.

## Exact one-center change

There is nevertheless a useful local lemma.  Start with a color-`c` star
forest `K` and add a previously unforced color-`c` center `x`.  Let `M` be the
set of old components containing `x` and its grid neighbors.  If the enlarged
star graph is acyclic, the neighbor components are pairwise distinct; the
component of `x` is also distinct because `x` was isolated.  Conversely, two
neighbors in one old component, together with the two new star edges, produce
a cycle.

Let `t` be the number of perimeter edges whose endpoint components are two
distinct members of `M`.  Adding the center quotients precisely the labels in
`M`, so

```text
R_c(new) = R_c(old)-t,
R_opposite(new) = R_opposite(old).
```

This statement does not require a global nonalternation argument.  For every
adjacent pair in the cyclic word, its change indicator disappears exactly when
its two distinct old labels both lie in `M`; all other indicators are
unchanged.  Removing the center reverses the equations and increases `R_c` by
exactly `t`.

Write the proposed margins as

```text
M_B = 2A_B+R_W-2Q_B-R_B,
M_W = 2A_W+R_B-2Q_W-R_W.
```

Adding a black center increases `Q_B` by three and therefore changes

```text
(M_B,M_W) by (-6+t,-t).
```

Adding a white center changes them by `(-t,-6+t)`.  In either case their sum
drops by exactly six.  Acyclicity proves the distinct-component premise but
does not force `t` to be assigned to the margin that needs it.

The `7x7` counterexample makes the failed induction explicit.  Removing any
one of its centers gives nonnegative proposed margins.  For each black center,
`t` is zero or two and the removed black margin is respectively four or two;
restoration costs `6-t`, leaving margin `-2`.  For each white center, `t=2`,
the removed black margin is zero, and restoration costs that margin two,
again leaving `-2`.  Thus no choice of the last forced center lets an induction
using only the two asserted inequalities close.

Lean-suitable local statements should be separated as follows:

```lean
-- `mergeLabel s` identifies exactly the labels in `s`.
lemma cyclicChanges_map_mergeLabel
    (w : Fin L -> Alpha) (s : Finset Alpha) :
    cyclicChanges (fun i => mergeLabel s (w i)) +
        cyclicAdjacentDistinctInside w s = cyclicChanges w

lemma add_center_neighbor_components_pairwise_ne
    (hnew : (K ⊔ centerStar G x).IsAcyclic)
    {y z : V} (hy : G.Adj x y) (hz : G.Adj x z) (hyz : y ≠ z) :
    K.connectedComponentMk y ≠ K.connectedComponentMk z

lemma colorRunCount_add_center
    (hxc : color x = c) (hx : x \u2209 centers)
    (hnew : (colorStarGraph (insert x centers)).IsAcyclic) :
    colorRunCount (insert x centers) + centerBoundaryMergeCharge K x =
      colorRunCount centers

lemma runMargins_add_black_center
    (ht : colorRunCount new + t = colorRunCount old) :
    newBlackMargin + 6 = oldBlackMargin + t /\
    newWhiteMargin + t = oldWhiteMargin
```

The signatures deliberately use additive equalities and avoid truncated
natural subtraction.  The graph-union notation above is schematic; the useful
conclusion is the fully explicit statement that distinct neighbors of `x` are
in distinct `K` connected components.  Prove its contrapositive by
concatenating an old path with the two new edges.

For checking arithmetic, acyclicity gives the exact color identity

```text
C_c = n^2 - 4|F_c| + d_c,
Q_B = 3|F_B| - |V_W| + 2,
Q_W = 3|F_W| - |V_B| + 2.
```

The deficiency and component terms nevertheless remain useful geometrically:
they identify the local boundary objects that a proof must charge.

## Why runs are plausible

Every boundary edge belongs to the color-`c` star forest exactly when its
color-`c` endpoint is forced. Hence a forced color-`c` boundary center joins
its two neighboring boundary positions by a length-two path. A change in the
color-`c` component word can occur only across a missing such local path.

Moreover, the labels of any grid subgraph around the boundary cannot occur as
`A,B,A,B`: two paths joining the alternating pairs would intersect. This is
the nonalternation theorem already formalized in
`GridBoundaryNonalternation.lean`. The coefficient `1/2` is consistent with
pairing the two ends of each nonalternating boundary interval.  The
counterexamples show that no global injection with the proposed budgets can
exist, despite this valid nonalternation constraint.

## Exact contraction and Kreweras theorems

Two general theorems make the contraction/noncrossing mechanism precise. They
also explain why it cannot rescue the refuted candidate without an additional
interior statistic.

### Component-incidence forest

Let `H=(V,E)` be a finite forest and suppose `E=E_B union E_W`; the two edge
sets may overlap. Contract every component of
`I=(V,E_B intersect E_W)`. Write `X` for the resulting vertex set and
`bar E_B,bar E_W` for the images of the noncommon edges. There are no loops: a
noncommon edge whose ends were joined by `I` would close a cycle in `H`. Thus
the two image edge sets are disjoint and their union is again a forest.

Let `P_B,P_W` be their component partitions of `X`, including isolates. Form
the bipartite multigraph `M` whose vertices are the blocks of `P_B` and `P_W`
and which has, for each `x in X`, one edge joining the two blocks containing
`x`.

**Theorem 1 (component-incidence forest).** `M` is a forest. Its connected
components are naturally the components of the contracted union forest. If
`b_B,b_W,b_H` are the component counts of the two subforests and their union,
then

```text
|X| = b_B+b_W-b_H.                              (1)
```

**Proof.** Chains of intersecting component blocks are exactly paths in
`(X,bar E_B union bar E_W)`, so `M` and the union have the same `b_H`
components. Since the two edge sets are disjoint forests,

```text
|bar E_B|=|X|-b_B,  |bar E_W|=|X|-b_W,
|bar E_B|+|bar E_W|=|X|-b_H.
```

Eliminating the edge counts gives (1). Now `M` has `|X|` edges, `b_B+b_W`
vertices, and `b_H` components. Equation (1) is the forest cardinality
identity for `M`, so `M` is a forest. QED.

For comparison, any two partitions `pi,sigma` of an `m`-element set satisfy

```text
blocks(pi)+blocks(sigma) <= m+blocks(pi join sigma).   (2)
```

Indeed, their block-incidence multigraph has `m` edges and one connected
component per join block. Equality holds exactly when that incidence graph is
a forest. Theorem 1 says that the full component partitions after common-edge
contraction attain equality. With one join block, (2) becomes the familiar
`blocks(pi)+blocks(sigma)<=m+1`, with equality for a Kreweras-complement pair.

### Runs as complement-side leaves

Let `pi` be a noncrossing partition of `m>=2` cyclically ordered positions and
let `R(pi)` count cyclic adjacencies in different blocks. Use the right
Kreweras complement with permutation convention

```text
p_K = p_pi^{-1} (1 2 ... m),
```

where `p_pi` sends each element to the next element of its block. Write
`sing(tau)` for the number of singleton blocks of `tau`.

**Theorem 2 (run/singleton identity).**

```text
R(pi) = m-sing(K(pi)).                           (3)
```

Hence, for two noncrossing boundary partitions,

```text
R(pi_B)-R(pi_W)
  = sing(K(pi_W))-sing(K(pi_B)).                 (4)
```

**Proof.** A position `i` is fixed by `p_K` exactly when
`p_pi(i)=i+1` cyclically. This holds exactly when the adjacent positions
`i,i+1` are in the same block of `pi`. Fixed points of a partition permutation
are its singleton blocks, and there are `m-R(pi)` same-block adjacencies. This
proves (3), and subtraction proves (4). QED.

The usual bipartite incidence graph of the blocks of `pi` and `K(pi)` is a
tree: it has one edge per position and the block identity gives `m+1`
vertices. A block vertex has degree equal to its block size. Thus
`sing(K(pi))` is literally the number of leaves on the complement side.

The grid component words define noncrossing partitions by boundary
nonalternation. If `L_c=sing(K(pi_c))`, then

```text
R_B-R_W = L_W-L_B.                              (5)
```

The proposed pair was therefore equivalent to

```text
2(Q_B-A_B) <= L_B-L_W,
2(Q_W-A_W) <= L_W-L_B.                          (6)
```

This rigorously identifies the signed run term as a signed leaf statistic.
The `7x7` example disproves the assertion that this leaf imbalance pays the
whole colorwise interior surplus.

### Boundary information is insufficient

The two boundary partitions are not generally Kreweras complements of one
another. With no selected centers both are discrete, while the Kreweras
complement of the discrete partition has one block. Theorem 1 concerns all
contracted vertices; restriction to the boundary can delete incidence edges
and entire blocks.

Moreover, the boundary partitions do not determine `Q_B,Q_W`. In the `5x5`
grid, the empty mask and

```text
0,0,0,4,0
```

have the same two completely discrete boundary partitions. The latter selects
one interior white center, its full forced graph is just a star, and `Q_W` is
larger by three. Thus no theorem involving only the two boundary partitions,
their block counts, or their run counts can control the color charges.

The contraction route does produce the full incidence forest of Theorem 1,
and the Kreweras route produces the exact leaf identity (5). A valid stronger
inequality would additionally need an interior pruning/weight statistic. The
counterexample shows that the unweighted leaf difference in (6) is not that
statistic.

## Coverage and equality

`checkerboard_boundary_runs.py` computes the F/U boundary word, both normalized
component-label words, all three run counts, both ambient star-forest component
counts, and colorwise boundary deficiency. The exact frontier grammar was used
for:

| size | coverage | sets | failures | simultaneous equalities |
|---:|:---|---:|---:|---:|
| 2 | all acyclic sets | 9 | 0 | 4 |
| 3 | all acyclic sets | 100 | 0 | 0 |
| 4 | all acyclic sets | 2,278 | 0 | 14 |
| 5 | all acyclic sets | 116,252 | 0 | 0 |
| 6 | all maximum sets | 96 | 0 | 0 |

The original targeted pass additionally checked 10, 105, and 50 maximum sets at
sizes 7, 8, and 9, respectively, with no failures.  The counterexample above
is not maximum, showing that maximum-only sampling was not a valid gate for
this colorwise strengthening. Searching primitive integer
scales `1 <= s <= 6`, run coefficients `0 <= k <= s`, and odd biases of absolute
value at most seven left the unique triple `(s,k,bias)=(2,1,3)`.

The 14 simultaneous `4x4` equalities are exactly all maximum sets and form
three dihedral orbits, represented by little-endian row masks

```text
9,9,0,15
9,9,1,13
9,9,9,9
```

Targeted maximum witnesses through `9x9` also had no failure. The sampled
`7x7` equality profile has

```text
(|F_B|,|F_W|,R_B,R_W) = (12,10,4,8),
```

and both color inequalities are equalities. This agrees with the exact maximum
`P(7)=22` and equality in the summed checkerboard bound.

## Counterexamples to nearby forms

Runs cannot simply be omitted. At `5x5`, the acyclic maximum

```text
17,17,21,1,25
```

has `(|F_B|,|F_W|,R_B,R_W)=(7,4,4,8)`. With the stated allowances, its black
inequality forces the run coefficient to be at least `1/2`. It also disproves
the symmetric odd-grid allowance split `(8,7)` at coefficient `1/2`.

The coefficient cannot be increased. At `6x6`, the acyclic maximum

```text
37,33,41,33,0,63
```

has `(|F_B|,|F_W|,R_B,R_W)=(8,8,4,6)` and forces the coefficient to be at most
`1/2`. Therefore the coefficient `1/2` is pinned by explicit `5x5` and `6x6`
counterexamples within this cancellation family.

Run:

```bash
PYTHONPATH=analysis python3 analysis/checkerboard_boundary_runs.py
python3 -m unittest discover -s analysis -p 'test_checkerboard_boundary_runs.py'
```
