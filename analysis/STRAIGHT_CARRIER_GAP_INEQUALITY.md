# Straight-carrier gap inequality census

This note records finite computational evidence, not a proof for arbitrary
width.

## Definitions

Let `F` be a vertex set in the `n x n` grid and let `H` contain every grid edge
with at least one endpoint in `F`. Assume `H` is acyclic. Let `U=V\F`.

Every non-singleton component of `G[F]` is a horizontal or vertical interval.
Call these components **carriers**. Singleton components are not assigned an
axis. For each carrier the checker records:

* interval length and orientation;
* incidences with the four sides of the square;
* attachment degree after contracting every `F` component in `H`;
* leaf and branching attachments, according as the adjacent `U` vertex has
  contracted degree one or at least two; and
* rows and columns occupied.

It independently verifies the local identity

```text
attachment_degree(K) = 2 length(K) + 2 - side_contacts(K).
```

An **internal axial U gap** is a maximal nonempty interval consisting entirely
of `U` vertices whose two ends meet distinct horizontal carriers in one row, or
distinct vertical carriers in one column. Perpendicular carriers and singleton
components break a gap rather than being silently included in it. Write `g(F)`
for the number of these gaps. The checker also records their total length and
the analogous gaps between an extreme carrier and the grid boundary.

Use the exact boundary-charge notation from
`BOUNDARY_CHARGE_REDUCTION.md`:

```text
X(F) = B_F - U0 - R - 2C,
3|F| = n^2 + X(F).
```

Here `U0` counts isolated `U` vertices of `H`, `R` is the branching credit, and
`C` is the number of nonisolated components of `H`.

## Local definition suitable for Lean

The carrier extraction above is useful geometrically but is not needed in the
definition.  On a finite binary line, list its maximal nonempty `F`-runs in
order.  A **line gap** is a pair of consecutive runs whose two lengths are at
least two.  A singleton run between two long runs therefore prevents those
long runs from being paired.  Define

```text
g(F) = sum_rows lineGaps(F on row) + sum_columns lineGaps(F on column).
```

For forced-acyclic `F`, every run of length at least two is exactly a straight
carrier and no perpendicular carrier can meet it.  Hence this local definition
equals the internal axial `U`-gap definition above.  The checker verifies the
equality independently by global component extraction.

This formulation is directly finite and Lean-friendly.  One possible local
predicate has endpoints `a<=b<c<=d`: `[a,b]` and `[c,d]` are maximal all-`F`
intervals, `a<b`, `c<d`, and every index strictly between `b` and `c` is `U`.
The cardinality of these endpoint quadruples is `lineGaps`; maximality makes
the representation unique.  This avoids connected components and arbitrary
orientation choices in the definition of `g`.

## Counterexample

The strengthened inequality previously proposed here is false.  Exact weighted
row-grammar optimization at `n=10` found the little-endian row masks

```text
957, 1, 585, 585, 585, 585, 585, 585, 512, 631.
```

The direct forced-edge checker confirms acyclicity and inclusion maximality.
Both the local run definition and independent global carrier extraction give
`g(F)=2`; `|F|=41`.  Therefore

```text
3|F|+2g(F) = 127 > 126 = 10^2+3*10-4.
```

The original unstrengthened target is not refuted: `3|F|=123<=126`.

## Earlier candidate

The small-coefficient search found

```text
X(F) + 2 g(F) <= 3n - 4.                              (G2)
```

Since `g(F)>=0`, `(G2)` implies the target `X(F)<=3n-4`. It is not algebraically
equivalent to the target: the acyclic `5x5` row masks

```text
0, 0, 0, 0, 27
```

have two horizontal length-two carriers separated by one `U` vertex, so
`g(F)=1`. Thus `(G2)` has a genuinely larger left side on a valid input.

The coefficient is pinned by a certified maximum `12x12` witness:

```text
4093, 1, 513, 2301, 2049, 2817, 2169, 2049, 2957, 2081, 1, 4093
```

It has target margin `3n-4-X(F)=2`, one internal axial gap, and gap length
three. Hence coefficient two is tight, coefficient three fails, and replacing
gap count by total gap length also fails. The certified maximum `15x15`
canonical witness independently has the same `(margin,gaps,length)=(2,1,3)`.

No positive branching-attachment coefficient survives. The acyclic `4x4` row
masks

```text
1, 9, 8, 11
```

have target margin three and four branching attachments.

## Expanded coverage

The exact max-plus row grammar, including a suffix-safe dominance quotient,
maximized the strengthened left side over every forced-acyclic set through
`n=10`:

| `n` | exact max `3|F|+2g` | bound | margin | extremal `(|F|,g)` |
|---:|---:|---:|---:|:---|
| 2 | 6 | 6 | 0 | `(2,0)` |
| 3 | 12 | 14 | 2 | `(4,0)` |
| 4 | 24 | 24 | 0 | `(8,0)` |
| 5 | 34 | 36 | 2 | `(10,2)` |
| 6 | 49 | 50 | 1 | `(15,2)` |
| 7 | 66 | 66 | 0 | `(22,0)` |
| 8 | 83 | 84 | 1 | `(25,4)` |
| 9 | 104 | 104 | 0 | `(32,4)` |
| 10 | **127** | **126** | **-1** | `(41,2)` |

The dominance quotient is exact: for equal forced-forest frontiers, it removes
a vertical line-state vector only when its accumulated score dominates the
other for every binary suffix of the remaining height.  Rust tests replay the
known exact scores through `n=6`; Python tests compare the grammar with direct
exhaustion through `n=4`.

An attempted enumeration of all inclusion-maximal sets at `n=6` did not finish
in ten minutes with the path-enumerating Python reference, so no completeness
claim is made for that requested census.  The existing complete facts remain:
all acyclic sets through `n=5`, and all 96 maximum-cardinality sets at `n=6`.

Score-directed remove/regrow mutations (500 attempts per size) independently
checked inclusion-maximal witnesses through `n=20`.  They rediscovered or
retained negative margins at `n=10,17,18`; the best observed margins for
`n=11..20` were respectively

```text
3, 0, 0, 3, 0, 0, -1, -2, 0, 5.
```

The `n=18` winner has `(|F|,g)=(124,2)`, score `376`, bound `374`, and margin
`-2`.  These mutation values are adversarial lower bounds on the maximum score,
not exact maxima.

## Prior coverage

The exact frontier grammar checked every acyclic set through `n=5`:

| `n` | sets checked | minimum `(3n-4-X)-2g` |
|---:|---:|---:|
| 2 | 9 | 0 |
| 3 | 100 | 2 |
| 4 | 2,278 | 0 |
| 5 | 116,252 | 3 |

All 96 maximum `6x6` witnesses were checked, followed by dihedral images and
cardinality-preserving exchanges of known target-count witnesses through
`n=15`. Every larger witness was independently checked to be inclusion-maximal.
The larger sample counts for `n=7..15` were respectively
`10,37,41,10,19,17,10,11,10`; the minimum candidate margins were
`0,3,2,0,3,0,0,3,0`. The `n=13` witnesses attain the recorded target count but
that width is still marked only as a lower bound in `data/diagonal.csv`.

The searched feature vector was

```text
(internal gap count, internal gap length, branching attachments),
```

with each coefficient in `{0,1,2,3}`. Over the full census the only nonzero
survivors were `(1,0,0)` and `(2,0,0)`. Thus `(G2)` is the strongest member of
this declared nonnegative family.

Run:

```bash
PYTHONPATH=analysis python3 -m unittest analysis/tests/bounds/test_gap_inequality_falsification.py
cargo test --release --bin gap_inequality_falsification
cargo run --release --bin gap_inequality_falsification -- 10
PYTHONPATH=analysis python3 -m analysis.bounds.gap_inequality_falsification \
  --exact-through 7 --maximal-n 0 --mutation-through 20 --attempts 500
PYTHONPATH=analysis python3 -m analysis.bounds.straight_carrier_inequality \
  --exhaustive-n 5 --maximum-n 6 --targeted-n 15 --random-count 30
python3 -m unittest discover -s analysis -p 'test_straight_carrier_inequality.py'
```
