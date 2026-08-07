# Incidence-waste equality and the residue-two defect

This note investigates equality in the incidence-waste bound using the existing
canonical patterns, exact frontier corridors, component reductions, and
committed `n=17` census.  It proves algebraic reductions and reports finite
census results; it does **not** prove the missing arbitrary-width lower bound.

## 1. Exact algebra

Let `D` be a dual spanning tree and `U=supp(D)`.  The full dual graph induced
by all primal U-U edges contains `D`, so it is connected and has graphic rank
`rho=(n-1)^2`.  Let `R` and `beta` be the sum of row and column U-run counts
and the cycle rank of that full induced dual graph.  The standard run count
gives

```text
E = 2|U|-R,                 beta=E-rho,
W = 3|U|-2rho = 2R+2beta-|U|.
```

Put

```text
K = W-n = 3|U|-2(n-1)^2-n.
```

Then `W=n+2` is exactly `K=2`, and `W=n+5` is exactly `K=5`.  Adding one U
vertex changes `K` by three.  Also

```text
K == (n-1)^2-n (mod 3),
```

so the admissible residue classes of `K` are

```text
n mod 3       0       1       2
K mod 3       1       2       2.
```

Consequently a width-independent sharp three-phase theorem would be

```text
K >= 4, 2, 5       for n == 0, 1, 2 (mod 3), respectively.       (T3)
```

These constants give exactly the old three formulas for the minimum support:

```text
n=3k:     |U| >= 6k^2-3k+2,
n=3k+1:   |U| >= 6k^2+k+1,
n=3k+2:   |U| >= 6k^2+5k+3.
```

Thus the universal target `W>=n+2`, together with congruence, would already
give the first two phases of `(T3)`.  Residue two is the only phase where it
leaves an additional three-unit gap: it permits `K=2`, whereas `(T3)` requires
`K>=5`.

For `n=3k+2`, the `K=5` case reduces without approximation to

```text
3|U| = 2(n-1)^2+n+5,
|U|  = 6k^2+5k+3,
R    = (|U|+n+5-2beta)/2.                                  (1)
```

The revised residue-two tail is the still stronger statement

```text
k>=5  implies K>=8, equivalently |U|>=6k^2+5k+4.            (R2+)
```

The exact `n=17` search proves `(R2+)` only at its first width.

## 2. Exact component form

Let `F=V-U`, let `H=G-E(G[U])` be the forced forest, let `c_F` be the number
of components of `G[F]`, and let `c_H` be the number of components of `H`.
Let `b(U)` count boundary U incidences, with a corner counted twice.  The
existing forest-component reduction gives

```text
K = b(U)+c_F+c_H-n-2.                                      (2)
```

Therefore

```text
K=2  iff b(U)+c_F+c_H=n+4,
K=5  iff b(U)+c_F+c_H=n+7,
K=8  iff b(U)+c_F+c_H=n+10.                                (3)
```

This is the cleanest exact meaning of a defect of three.  A structural tail
theorem cannot merely find a defect; it must show that every residue-two
`K=5` candidate with `n>=17` incurs three additional units in this component
charge.  On the canonical controls the three summands are

```text
n       b(U)   c_F   c_H   total
5          7     4     1      12 = n+7
8          6     8     1      15 = n+7
11         5    11     2      18 = n+7
14         5    14     2      21 = n+7
17         5    20     2      27 = n+10
```

The `n=17` excess is carried here by `c_F`: the old-baseline target would need
total charge 24, while the 179-U witness has 27.  This observation is not a
proof that every hypothetical 178-U pattern has the same boundary or component
profile.  Equation `(2)` also shows why scalar component counting alone is
circular: proving total charge `n+7` or `n+10` is exactly the desired bound.

## 3. Exact row form and the three-phase attempt

For one accepted row transition, let `u_i` be the new row's U count, `h_i` its
U-run count, `v_i` its vertical U-U overlap with the previous row, and
`gamma_i` the increase in dual cycle rank.  Assigning charge one per row gives

```text
w_i = u_i+2h_i-2v_i+2gamma_i-1,
sum_i w_i = K.                                               (4)
```

Thus `(T3)` is precisely a lower bound on the total weight of every accepting
row path, with terminal constants `4,2,5` by width phase.  This is a genuine
width-independent formulation, but not yet a theorem: the exact pooled
frontier potential with these constants is known only through small widths,
and the old pooled quotient develops a negative constraint cycle when width
seven is added.

The residue-one canonical family illustrates the cancellation a proof would
need to capture.  Its dual is a tree (`beta=0`), and for `n=3k+1` it has

```text
row runs = 3k,
column runs = 3k^2-k+2,
|U| = 6k^2+k+1,
K = 2.
```

Its sparse/dense/dense production blocks have large positive and negative row
weights which cancel.  For example:

```text
n=7:  2, 5,-5, 0, 5,-4,-1       total 2
n=10: 2, 8,-8, 0, 8,-8, 0,8,-7,-1   total 2.
```

For the residue-two canonical controls the exact row weights and fixed
top-aligned three-row sums are:

```text
n=5:   2,4,0,-1,0                              triples  6,-1
n=8:  -1,9,-2,0,0,0,-2,1                      triples  6,0,-1
n=11:  2,9,-5,0,3,0,-3,0,4,-5,0               triples  6,3,1,-5
n=14:  2,12,-3,1,0,-2,1,0,-2,0,0,0,-5,1       triples 11,-1,-1,0,-4
n=17:  2,15,-3,1,0,0,0,0,0,0,0,-2,0,0,0,-6,1 triples 14,1,0,-2,0,-5
```

The totals are `5,5,5,5,8`.  Charge is transported between caps and the bulk;
it is not supplied independently by each three-row block.  In particular, a
nonnegative fixed-band theorem is false.

Two weaker observations survived the available controls but are not promoted
to conjectures:

* The minimum prefix weight is at least `-1` on every complete `n=5,8`
  equality-corridor path and on every D4 image of the fixed `n=5,8,11,14,17`
  controls.
* This does not localize the terminal constant.  Among complete equality paths,
  a three-row interval can have weight `-2` at `n=5` and `-3` at `n=8`; fixed
  controls reach `-3,-5,-6` at `n=11,14,17` respectively.

The growing negative band values show that any useful three-phase theorem must
carry an attachment potential across bands.  A scalar per-band charge is not
width independent in the required sense.

## 4. Actual equality invariants in the available examples

The run/cycle data are exact consequences of `(1)`, but they also expose a
change of topology:

```text
n       |U|    R    beta    K
5        14    12      0    5
8        37    25      0    5
11       72    43      1    5
14      119    68      1    5
17      179   101      1    8
```

Hence neither `beta=0` nor `beta=1` characterizes residue-two equality.
Complete centered-layer censuses at `n=5,8` give the following real, but
finite-width, attachment invariants:

```text
width   repeated port components   cyclic runs/component   compressed runs
5                    <=4                    <=1                  <=5
8                    <=4                    <=2                  <=6
```

All 242 `n=5` and 704 `n=8` equality patterns satisfy those maxima.  In the
reduced annulus metric, all `n=5` equality patterns have branch cost zero;
`n=8` has branch cost zero for 576 patterns and one for 128.  The fixed
`n=11` (including the silent-carrier witness) and `n=14` controls also have
maximum branch cost one.

This does not yield a topological bound.  The valid affine controls have branch
cost `2,3,4,...` at `n=17,20,23,...`, while their curvature grows
`8,11,14,...`.  The defensible candidate is conditional: `K=5` may force
branch cost at most one.  It is complete only at `n=5,8`, path-tested at
`n=11,14`, and unproved in arbitrary width.

The exact frontier data identify one further invariant that matters at the
tail: whether live components are already rooted in `OUT`, not merely their
current row mask.  At the final `n=17` hinge, all 20 old-baseline survivors
have rooted attachment debt two.  Eighteen have only one remaining independent
merge and two have none.  The 179-U positive control has debt one and capacity
one.  Thus

```text
unpayable debt = max(rooted debt - remaining independent merge capacity,0)
```

is positive (`1` or `2`) on every 178-U survivor and zero on the 179-U witness.
This is the only currently certified mechanism that explains the extra three
units at `n=17`.

## 5. Falsified defect statements

The complete `n=5,8` corridor does have a striking defect-three gap: support
holes, concurrent packet carriers, face-cut width greater than one, forbidden
local motifs `010` and `121`, and their combined grammar rejection all first
occur on complete paths with at least `K=8`.  That statement is exact at those
two widths.

It is not the desired theorem:

* At `n=11`, an exact `K=5` witness has a carrier occupying packet groups 1 and
  3 with group 2 silent at row 8; the next row repairs the hole.  This falsifies
  contiguous carrier support and “every support hole costs three.”
* The stronger face-cut occurrence-hull defect survives the `n=11` exact
  two-channel search: every `K=5` path has width at most one, and the first
  width-two path has `K=8`.  This is fixed-width evidence, not an induction.
* A first two-carrier defect does not force lost suffix capacity.  Exact `n=8`
  and `n=11` witnesses can discharge all current debt in their suffixes.
* Nonnegative three-row production is false, as the row table above shows.
* A bounded `4/3/9` centered-port signature is not topological; affine `A23`
  has signature `5/3/12`.
* Fixed or moving literal three-row slab renewal is absent in the complete
  `5 -> 8` transport graph.  Its decorated interior graph is acyclic, despite
  many visible alignments.
* Row-local packet/cycle profiles are not stable across widths: the complete
  `n=5` and `n=8` equality corridors have no common rule after cycle/curvature
  data are included.

These counterexamples force a silent-hull language with persistent rooted debt;
the earlier contiguous-carrier grammar is too narrow.

## 6. What is proved and what remains

Proved or exactly certified:

1. Equations `(1)` through `(4)`, including the exact component and row
   reductions.
2. The congruence reduction of the universal equality question to phase
   constants `4,2,5`.
3. Complete minimum `K=5` and equality corridors at `n=5,8`.
4. Exact fixed-width face-cut defect gap three at `n=11`.
5. Exact `n=17` UNSAT at 178 U and a valid 179-U witness, hence minimum
   `K=8` there.
6. Positive terminal unpayable debt on all 20 committed 178-U survivors and
   zero on the 179-U control.

Not proved:

1. `W>=n+2` in arbitrary width.
2. The three-phase theorem `(T3)` in arbitrary width.
3. Baseline `K>=5` for every residue-two width.
4. The tail theorem `(R2+)` for every `k>=5`.
5. Coverage of all `K<=5` paths by a bounded silent-hull transition language.

The exact bottleneck is therefore a coverage-and-persistence lemma, not more
terminal arithmetic:

> Every accepting residue-two path with `K<=5` admits an OUT-rooted silent-hull
> attachment description whose transitions are covered by a width-independent
> symbolic language; once `k>=5`, every such path accumulates persistent
> unpayable debt before the bottom cap.

The existing symbolic certificates prove arbitrary packet-length correctness
for 19 transitions of one affine family, but not coverage of all low-curvature
paths.  Conversely, the complete small corridors prove coverage only at fixed
width.  At `n=17`, the terminal dump has no predecessor IDs, so the positive
unpayable-debt flag cannot currently be telescoped back through all 178-U
histories.  This missing arbitrary-width coverage plus history propagation is
the narrow obstruction to a rigorous defect-three tail theorem.

## 7. Reproducibility

Focused checks run for this note:

```text
python3 -B analysis/analyze_residue_constructions.py ...
python3 -B analysis/residue_two_universal_bound_ledger.py ...
PYTHONPATH=analysis python3 -m unittest \
  test_residue_two_structural_defect_gap \
  test_residue_two_obligation5_components \
  test_proof_oriented_identities
PYTHONPATH=analysis python3 -m unittest \
  test_residue_two_first_defect_certificate \
  test_residue_two_persistent_debt_certificate \
  test_residue_two_landmark_census
```

The two test runs completed with 41 tests passing and three slow regenerations
skipped.  Additional exact corridor calculations enumerated all equality
states/edges at `n=5,8`; D4 row checks covered the fixed
`n=5,8,11,14,17` controls.  No expensive `n=17` search was rerun; this note
uses the committed unpruned UNSAT artifact with 30,053,510,406 generated
transitions and the independently replayed 179-U witness.
