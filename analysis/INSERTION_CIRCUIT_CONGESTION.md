# Canonical insertion-circuit congestion

This is finite computational evidence, not a proof for uncomputed grids.

**Current status:** the selected-turn and even per-owner minimum-turn
inequalities are false.  The exact minimum-reflex gate found the `9 x 9`
counterexample recorded below.  The earlier small census remains useful for
describing why the candidate survived the initial search, not as positive
evidence for the inequality.

## Circuit set and canonical circuit

Let `F` be inclusion-maximal subject to its forced graph `H` being a forest,
and put `U=V-F`. Inserting `u in U` adds exactly the `U-U` edges incident with
`u`. Maximality guarantees that `H` plus these edges contains a circuit.

For each owner `u`, the checker now enumerates every possible simple insertion
circuit from the unique paths in the forest `H`:

* one inserted edge `uv` plus the `H`-path from `v` back to `u`; or
* two inserted edges `uv,uw` plus the `H-u` path from `v` to `w`.

Circuits are deduplicated by their undirected edge sets. The **canonical**
selector minimizes `(number of edges, sorted undirected edge list)`. It does
not minimize turns. This gives one deterministic shortest circuit for every
omitted vertex, without depending on DFS order or a planar embedding
convention. Every owner has at most four `U` neighbours, so this direct
enumeration has at most ten path candidates before deduplication.

There are four distinct meanings one might assign to `T`:

* `T_sel`: sum of turns in the selected shortest-lex circuit for each owner;
* `T_min`: sum of the per-owner minimum number of turns;
* `T_max`: sum of the per-owner maximum number of turns, equivalently the
  worst choice when one circuit per owner may be selected arbitrarily;
* `T_all`: sum of turns over every owner-labelled insertion circuit.

The previously stated `T(F)` meant `T_sel`. It did **not** mean `T_min`,
`T_max`, or `T_all`. The distinction is real: sampled sets at `n=13` and
`n=17` have `T_sel=T_min+2`.

## Measured resources

The simultaneous family, with one owner-labelled circuit per `u`, records:

* direct multiplicity on `H` edges and inserted `U-U` edges;
* unit cells whose centers are strictly inside each circuit;
* vertex rows met by each circuit;
* unit perimeter edges used by each circuit;
* components of `G[U]` containing vertices of each circuit;
* circuit length and number of direction changes.

The exact maximal-set census gives these worst observed loads:

| `n` | sets | max length | `H` edge | `U-U` edge | cell | row | boundary unit | `U` component |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 2 | 4 | 4 | 2 | 2 | 2 | 2 | 2 | 2 |
| 3 | 26 | 8 | 5 | 2 | 4 | 6 | 4 | 5 |
| 4 | 138 | 12 | 6 | 2 | 4 | 11 | 4 | 11 |
| 5 | 2,164 | 16 | 10 | 2 | 6 | 16 | 6 | 18 |

Thus only the `U-U` edge load has a universal bound visible directly from the
definition: it is at most two because such an edge can be inserted only by its
two endpoints. Unit-capacity charging to `H` edges, cells, rows, boundary
units, or `U` components is already false. Adversarial maximal samples through
`n=15` raise the observed row and component loads to `34` and `160`.

## Weighted law: two readings are false

For any explicitly specified `T`, consider

```text
T(F) + 7|F| + c(G[U]) + 3 <= 5n^2 + 3n.                (TURN)
```

The universal-choice interpretation `T=T_max` is false already at `n=3`.
One counterexample, with rows written left-to-right, is

```text
FUU
UUF
FUF
```

Its `T_sel` and `T_min` margins are `2`, but its `T_max` margin is `-2`.
The literal `T=T_all` interpretation is even more strongly false on the same
set, with margin `-30`; indeed it fails on all 26 maximal `3x3` sets. Thus no
claim quantifying over arbitrary owner-circuit choices survives.

The initial experiment left `T_sel` and `T_min` unresolved.  The expanded
minimum-reflex search below refutes both; `T_min` fails, and therefore every
one-circuit-per-owner selection fails on the same set.

This is not an algebraic restatement of the target. If

```text
S = n^2 + 3n - 3 - 3|F| - c(G[U]),
```

then the independently checked `(TURN)` margin is

```text
S - (T(F)-4|U|).
```

Every simple rectilinear circuit has at least four direction changes, so
`T(F)>=4|U|`. Consequently `(TURN)` implies `S>=0`, exactly

```text
3|F| + c(G[U]) + 3 <= n^2 + 3n.
```

The exact row-grammar census of every inclusion-maximal set gives:

| `n` | sets | `T_sel` min/eq/fail | `T_min` min/eq/fail | `T_max` min/eq/fail | `T_all` min/eq/fail |
|---:|---:|---:|---:|---:|---:|
| 2 | 4 | 0/4/0 | 0/4/0 | 0/4/0 | 0/4/0 |
| 3 | 26 | 2/0/0 | 2/0/0 | -2/8/8 | -30/0/26 |
| 4 | 138 | 0/14/0 | 0/14/0 | -12/18/36 | -110/0/138 |
| 5 | 2,164 | 3/0/0 | 3/0/0 | -22/82/1,564 | -208/0/2,160 |

The original mutation search scored the turning margin itself. It starts from the
older component-margin adversary, repeatedly deletes forced vertices, and
maximalizes with randomized row-grammar-checked insertion orders. In a
64-attempt campaign through `n=18`, the best observed `T_sel` margins were
`2,0,3,2,0,3,2,0,3,1,0,6,1` for `n=6..18`; `T_min` had the same minima.
These are sampled minima, not certified minima. Equality recurs in the sampled
period-three family at `n=7,10,13,16`; the exact `n=4` census has 14 equality
sets. Outside equality, the surviving margins are small rather than growing,
so that campaign should be read as an account of the missed counterexample,
not as current support for the inequality.

The search still exercises circuits longer than unit cells and circuits with
more than four turns. The canonical and minimum-turn totals agree on every
maximal set through `n=5`, but not on all larger samples, so both columns are
computed independently.

Before the counterexample, the proposed planar proof target was the
selected-circuit excess bound

```text
sum_(u in U) (turns(C_u)-4) <=
  n^2 + 3n - 3 - 3|F| - c(G[U]).
```

Unlike raw path length, turning localizes at corners and can be assigned to
row/column cut transitions. A proof still has to control repeated ownership of
the same corner or cell; the measured cell and row congestion shows that an
injection is unavailable. The JSON also reports, for both path and turn excess,
the least integer `k` observed in `excess <= k*S`. The combined sample needs
`k=17` for path excess but only `k=1` for turn excess, which is why `(TURN)` is
the candidate then selected for further falsification.

The JSON includes complete exact margin distributions, first minimum witnesses,
selector-disagreement counts, and all four quantifiers. Run:

```bash
python3 -m unittest discover -s analysis -p 'test_insertion_circuit_congestion.py'
python3 analysis/insertion_circuit_congestion.py --adversarial-through 18
python3 analysis/insertion_circuit_congestion.py --maximal-n 3 \
  --adversarial-through 3 --require-choice maximum_turns  # exits 1
```

## Ordered-sector charging is false

There is no constant-capacity charge of all turns to ordered vertex-angle
sectors, even with the canonical shortest-circuit rule above.  The following
family gives a direct obstruction.

Let `n=4k+1`, with `k>=1`, and number rows and columns from `0` to `n-1`.
Define

```text
F_k = {(r,4j) : 0<=r<n, 0<=j<=k}
      union {(n-1,4j+2) : 0<=j<k}.
```

Thus `F_k` consists of vertical rails four columns apart and one bridge vertex
in the middle of each four-column interval on the bottom row.  Its forced graph
is a forest.  More precisely, all rails and bottom bridges belong to one tree;
the other incident forced edges are leaves, and the vertices `(r,4j+2)` with
`r<n-2` are isolated.  This description proves acyclicity by successively
attaching a new rail through one bottom path and then attaching leaves.

The set is inclusion-maximal.  A `U` vertex next to a rail has a vertical
`U` neighbor in the same nontrivial component of `H`, so inserting it creates
a one-edge circuit.  A middle vertex `(r,4j+2)` has the two horizontal
neighbors `(r,4j+1)` and `(r,4j+3)` in that component, so inserting both
horizontal edges creates a circuit.  These cases include the two rows adjacent
to a bottom bridge; there one of the available circuits can only become
shorter.

Consider the first interval, between columns `0` and `4`.  For every

```text
u_r=(r,2),  0<=r<n-3,
```

the only pair of inserted edges whose other endpoints are joined in `H-u_r`
is the horizontal pair.  The unique `H`-path between those endpoints descends
the column-zero rail, traverses the bottom bridge, and ascends the column-four
rail.  Hence the canonical circuit contains at the vertex `(n-1,0)` the
ordered turn

```text
(incoming direction, outgoing direction) = (down,right).
```

For `r=n-3`, the lower middle neighbor is also in the main component and gives
a shorter candidate.  Its path still descends column zero and traverses the
same ordered sector; the left candidate wins the lexicographic tie.  For
`r=n-2`, the owner itself is in the main component and the shortest one-edge
candidate through the left horizontal neighbor has the same property.  Thus
already the `n-1` owners `(r,2)`, `0<=r<n-1`, use one identical ordered sector.
In fact `(n-1,1)` is one further owner using it, so its load is `n`.

The loads for `n=5,9,13,17` are respectively `5,9,13,17`.  This computation is
only a check of the formulas above; the path description is a proof for every
`k`.  Notice also that every circuit in this family has exactly four turns:

```text
|F_k|=(k+1)n+k,
c(G[U])=k,
T=4|U|.
```

Consequently this family does not refute `(TURN)`.  It refutes the proposed
intermediate lemma that turns can be charged to ordered geometric sectors with
a universal bounded multiplicity.  The failure concerns precisely the four
unavoidable turns of each circuit.

## Curvature reduction that survives

For an oriented simple rectilinear circuit `C`, let `conv(C)` and `refl(C)` be
its numbers of convex and reflex quarter-turns.  The rectilinear turning
identity is

```text
conv(C)-refl(C)=4,
turns(C)=conv(C)+refl(C),
turns(C)-4=2*refl(C).
```

Reversing the orientation does not change either geometric count.  Summing
over owners gives the exact, subtraction-free form

```text
T = 4|U| + 2R,       R = sum_(u in U) refl(C_u).
```

After substituting `|U|=n^2-|F|`, `(TURN)` is therefore equivalent over the
integers to

```text
2R + 3|F| + c(G[U]) + 3 <= n^2 + 3n.                  (REFL)
```

This identifies what the attempted aggregate-curvature proof needed to do.  The baseline
four turns must be charged to the owner itself, not to a geometric corner.
Only reflex corners may be sent to face/corner incidences or angle sectors.
Unique paths in `H` prove that each individual circuit is simple and make its
reflex corners well-defined, but they do not control overlap between circuits.
The aggregate reflex bound itself is false, as follows.

## Exact minimum-reflex counterexample

`minimum_reflex_gate.py` computes the minimum independently for every owner.
It roots the forced forest once, enumerates the at most ten one-edge/two-edge
path candidates per owner, and sums the owner minima.  There is no global
selection coupling, so this optimization is exact.

The row-grammar adversary found this inclusion-maximal `9 x 9` forced forest:

```text
FFFFFFFFU
UUUUUUUUU
UUFUUFUUF
FUFUUFUUF
FUUUUFUUF
FUUFUFUUF
FUUUUUUUF
UUUUUUUUF
FFFFFFFUF
```

Its little-endian row masks are
`(255,0,292,293,289,297,257,256,383)`.  The exact profile is

```text
|F|=33,  |U|=48,  c(G[U])=1,
R_min=4, positive-reflex owners=3,
owner-minimum distribution={0:45, 1:2, 2:1}.
```

The three positive owners are `(0,8)`, `(6,3)`, and `(6,5)`, with minima
`1,2,1`.  The older full circuit enumerator independently returns the same
minimum and a minimum-turn margin of `-3`.  Thus

```text
2R_min+3|F|+c(G[U])+3-(n^2+3n)
  = 8+99+1+3-108 = 3 > 0.
```

This is stronger than a canonical-choice counterexample: even the best circuit
choice for every owner violates `(REFL)`, hence also `(TURN)`.

The reproducible 32-attempt campaign exhausts all maximal sets through `n=5`
and uses exact-row-grammar maximalization through `n=21`.  Its best objective
by width was

```text
n:    2  3  4  5  6  7  8  9 10 11 12 13 14 15 16 17 18 19 20 21
max:  0 -2  0 -3 -2  0 -3  3  0 -2 -2  0 -3 -2  0 -6 -1  0 -6 -2
```

The zeros at `n=2,4,7,10,13,16,19` all have `R_min=0` in this campaign.
Positive `R_min` occurs already in 200 of the 2,164 exact maximal `5 x 5`
sets, but none is equality there; their best objective is `-4`.

Run:

```bash
python3 -m unittest discover -s analysis -p 'test_minimum_reflex_gate.py'
python3 analysis/minimum_reflex_gate.py --adversarial-through 21 --attempts 32
```

The gate exits nonzero because the retained `n=9` counterexample is found.

The still-valid algebraic decomposition can avoid signed turning numbers and use the
following two lemmas:

```lean
theorem rectilinear_cycle_turns_eq
    (C : SimpleRectilinearCycle) :
    C.turns = 4 + 2 * C.reflexCorners

theorem turn_inequality_iff_reflex_inequality
    (hpartition : F.card + U.card = n * n)
    (hturn : T = 4 * U.card + 2 * R) :
    T + 7 * F.card + cU + 3 <= 5 * n * n + 3 * n <->
      2 * R + 3 * F.card + cU + 3 <= n * n + 3 * n
```

The second statement is Presburger arithmetic after replacing
`F.card + U.card` by `n*n`; `omega` should close it.  The first follows by
partitioning turns into convex and reflex turns and formalizing
`convexCorners = reflexCorners + 4`.  These lemmas remain valid, but the global
bound `(REFL)` they were intended to support is false.
