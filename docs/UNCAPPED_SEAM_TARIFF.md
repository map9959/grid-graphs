# Deficit charged to an ordered cut, with no traffic cap

The subsequent [coupled full-mask proof](UNCAPPED_ONE_GAP_623.md)
excludes the one-gap case at 623 after imposing consistency across cuts.

**The bound does not exclude one-gap equality at 623.** It takes an
arbitrary list of actual row positions and hop types as input. It does
exclude some whole families of lists, including the earlier
[absolute-row fan](ABSOLUTE_PORTS_623.md), without any restriction on
the number of hops elsewhere.

### A local formula

On cut `i` (east of tile column `i`), encode crossing marks at each
physical row by `0`, direct, skip-west or skip-east. Group triples of
physical rows into symbols `s_j` for tile rows `0..k-1`; the position
within the triple is part of the symbol. A two-site hop skips an
unmarked site. Checking the certified one-gap catalogue union gives:

* There is at most one hop per tile row on this cut. This is a property
  of the tiles; the list can have length up to `k`, not a fixed cutoff.
* The loss `c_j=6-popcount(left mask)-popcount(right mask)` is at
  least `b(s_j)`, with `b=1` on skips, zero otherwise.
* For two successive symbols let `gamma(s,t)` be the least loss of
  the four tiles on an allowed plaquette emitting `s,t`. An absent
  transition is impossible. Put `delta=gamma-b(s)-b(t)`.

Write `S` for the number of skips. For **every** actual cut word,

```
d_i + d_{i+1} >= S + max_M sum_{j in M} delta(s_j,s_{j+1}).
```

`M` ranges over disjoint pairs of successive tile rows. After paying
the `S` units, each disjoint pair still owes its `delta`; the maximum
is the usual path matching recurrence. In particular, if `A` counts
direct hops immediately preceded by an empty tile row, then
`d_i+d_{i+1} >= S+2A`. These start pairs are disjoint and every
such plaquette costs at least two. The sum of the full matching bills
over all cuts is bounded by `2D-d_0-d_{k-1}`.

It is not sound to replace this bill by a positive uniform price per
hop. For example, in the local two-column forest test west of the
isolate, the successive mask pairs

```
(292,292), (258,292), (16,16), then (73,73) for k-3 rows
```

cost **five** and carry **k-1 direct hops**. A middle `(73,73)` is a
zero-price self-transition of the *actual* six-site rooted frontier
on either axis, emitting one direct hop each time. This is a local
strip, not a rooted square.

### Whole-board price for a specified list

The stronger price charges a cut using strips that extend all the way
from west to east. Let `P_j` denote the physical mask pair across the
cut in row `j`, and `R_j` the deficit of that whole tile row. For each
pair of successive tile rows, price a physical strip **two tile rows
high and k tile columns long**:

```
G_j(P,Q) = minimum of a_j R_j + b_j R_{j+1}
           with P_j=P and P_{j+1}=Q.
```

Here `a_j=1+[j=0]`, `b_j=1+[j=k-2]`. The strip uses the correct
axis, the same north-isolate position throughout, the catalogue
plaquettes and an actual forced-edge partition. Cycles, components
with two teeth, and finished toothless components with no possible
exit through an open strip side are rejected. A toothless tree may
reach an open side; it need not have a tooth *in this strip*.
Min-cost prefix and suffix vectors on the same partition at the
central plaquette compute `G`. Infeasibility gives infinite price.
Prescribed rim masks may be imposed when testing that particular rim.

For an ordered list `w` define

```
B_i(w) = ceil( min_{P emits w} sum_j G_j(P_j,P_{j+1}) / 2 ).
```

Here `P` must itself pass a north-to-south, two-column physical-forest
test. Both strips at each intersection use the very same four masks.
Then **`D >= B_i(w)`**: an actual candidate supplies feasible strips,
and the endpoint weights count every physical row deficit exactly
twice. A stronger implementation keeps each individual inequality
`G_j <= a_j R_j + b_j R_{j+1}` as well as the exact losses of both
seam columns. Neither test discards high traffic. `OrderedSeamTariff.lean`
checks the disjoint-charge and overlap arithmetic; the mask and forest
transitions are checked by finite enumeration.

### A uniform exclusion from infinite price

For `k>=39`, `1<=q<=k-2` in the north-isolate chart (rim distance
`2+3q`), consider `max(0,q-5)<=i<q`. A **nonempty word consisting
solely of east-skipping hops** is impossible on these cuts except
possibly at

```
(q,i) = (3,0), (5,0), (5,1), (7,2).
```

This is not a bound on the number of east skips in a *mixed* word.
The empty word was not declared illegal by this argument. In
particular the known axis-1 fan has two east skips and nothing else at
`q-5`, with `q=19+4t`; this cut alone rules it out at **every size**.
Also, the last cut `k-2` must include a west skip. The four surviving
last-cut type sets in the relaxation were `{W}`, `{direct,W}`,
`{W,E}`, `{direct,W,E}` on both axes.

For this exclusion prices and rim words are dropped. On the base
39-chart, enumerate all base isolates `1..37`. Close the row-strip
automaton under arbitrary repetitions of a *homogeneous transition*
at column 8 if the base isolate is at least 19, and at 28 if it is
at most 19. The outer masks and partitions may change on each added
step. Before-and-after reachability gives the possible central
plaquettes, not just one continuation. These closures cover larger
boards: for a western isolate use the same base `q` and extend east;
for an eastern isolate keep its distance to the east end and extend
west; otherwise use base `q=19` and extend both sides. The tested
halo cuts stay at the same offset from the isolate. Close the
vertical seam in the homogeneous interior at row 18 in the same
way. Different strips may take *different* extension lengths; this
only enlarges the feasible set. The final three bits record which
types occurred, without bounding their multiplicities.

### Side 623: test all the cut inequalities against one budget

Use `k=207`, `D=1062` and a single `q=83`. Fix the same north and
south rim words in every strip. The test chooses integer row totals
`R_j` summing to 1,062, and joins **all 206** vertical cut tests on
exact shared column totals `d_i` also summing to 1,062. At each cut
it extracts a complete vertical mask-pair sequence. It checks the
local matching bill, the two actual column losses, and all 206
horizontal price inequalities against the common `R_j`. The curves
are not replaced by intervals. A search bound of 18 on a column's
*deficit* is used only to find these affirmative numerical controls.

| axis | exact budget in control? | cut 78 traffic | loss of columns 78,79 | sum of `G` there (limit 2,124) | all-cut matching bill |
|---|---|---:|---|---:|---:|
| 1 | yes | 6 | 7, 15 | 1,876 | 298 |
| 2 | yes | 6 | 7, 15 | 1,876 | 547 |

On this cut the west skip is at row 594; east skips occur at rows
601, 604, 607, 610 and 613. Axis 1 was additionally required to
have at least six hops on cuts 12,22,...,72. The total excess hops
beyond the first per cut were 88 and 133, respectively, enough for
the [previous necessary traffic bound](NONPERIODIC_COMPONENT_DEBT.md).
A separate exact min-plus count histogram at cut 78, with its rim
fixed, still allows a word with **200 hops** under the whole-board
price test considered just at that cut. This does not assert a
200-hop solution to all the tests simultaneously.

The all-cut control enforces equality of column **losses**, not
equality of every shared tile between two independently priced cuts.
The recovered neighboring cut pairs disagree at 13,816 shared tile
masks on axis 1 and 4,035 on axis 2. Horizontal strip minima also
need not choose the same complete row. Independent physical graph
traversal replays sample strip minima (including a strip at the
six-hop crossing). No assembled spanning tree is claimed. Thus this
is a negative test of the *deficit inequality as an exclusion*, not
evidence that one-gap equality is feasible or that the unrestricted
bounds coincide.

```
export PYTHONPATH=target/pb-python
python3 -B -m analysis.research_program.seam_budget_control 1
python3 -B -m analysis.research_program.seam_budget_control 2
python3 -B -m analysis.research_program.seam_curve_audit
python3 -B -m analysis.research_program.seam_direction
(cd lean && lake env lean GridGraphs/Geometry/OrderedSeamTariff.lean)
```
