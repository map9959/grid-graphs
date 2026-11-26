# Charging marks against both pitch directions

The [physical junction-rank refinement](SKELETON_CROSS_RANK.md) strengthens
the no-pitch floor below to `F-j≥43` at side 103.

In side `n=3k+1` put `m=k+1`, `k≥1`. The skeleton is the union of
the rows and columns indexed `0 mod 3`. Let `F` count marks outside
this union (both coordinates nonzero mod three). The exact maximum
number of skeleton marks is

```
3k²+5k.
```

This bounds skeleton marks even with arbitrary marks elsewhere.
Equality is physical: mark the first row, leave the second empty,
and use full vertical pitch rows below. Every rail has one connection
to the first row; the remaining edges attach leaves. The score is
`n+(n-2)m`. In particular the residue-one question is how much *net*
gain the doubly off-phase marks can buy.

**Joint count.** Regard the skeleton as an `m×m` grid of junctions
with two midpoints on each coarse edge, one owned by each end. Assign
each junction an axis H or V containing all its owned marked
midpoints: perpendicular ones would be diagonal in a unit square.
If neither axis is prescribed, either assignment works. Let `r` count
rows of junctions with some H, `c` columns with some V. Let `R`
count the horizontal runs of H and vertical runs of V, singletons
included. Each junction predicts the two midpoint slots on its chosen
axis. Let `E` count outward (off-board) slots, `l` the unfilled
predicted on-board slots, and `v` vacant junctions. Then

```
M = 3m² + F - E - l - v.
```

A predicted coarse edge has at least one predicted slot. A realized
edge has all three unit bonds forced along it. These realized edges
form a forest by subdivision; let `C` count its components, including
isolated junctions. A boundary between unlike axes has exactly one
predicted slot. If `W` is the number of such boundaries, `W+E=2R`
by counting run ends. The predicted edge count is
`(2m²-E+W)/2=m²+R-E`, the realized count `m²-C`. Thus `R-E+C`
predicted edges fail.

A failed edge missing a predicted midpoint can be charged to that
unfilled slot. For any other failure the two axes must differ, the
unique predicted midpoint is marked, and the opposite junction must
be vacant (otherwise all three bonds are forced). Charge this hit to
the opposite junction. Hits there arrive on the axis perpendicular
to its choice, at most two. A double hit is a distinct length-one gap
between two horizontal H runs or two vertical V runs. The number of
all such internal gaps, of any length, is `R-r-c`. Consequently

```
R-E+C ≤ l + hits ≤ l+v+doubles ≤ l+v+R-r-c,
M ≤ 3m² + F - r - c - C.
```

These three inequalities give three separately nonnegative slacks;
subtracting their sum from the last right side gives **exactly** `M`.
At least one of `r,c` is `m`: a row with no H meets every column
at a V. In a mixed assignment `r+c≥m+1`, and `C≥1`. In a constant
assignment no coarse edges run on the other axis, so `C≥m`.
Either way `r+c+C≥m+2`, proving the claimed optimum.

**No-pitch maximum.** Write `b=min(r,c)`. In a global maximum without
a complete pitch row or column,

```
F ≥ m-b.
```

Orient the board so the `b` exceptional coarse lines are rows
containing H. In each interval of physical rows strictly between
two such rows, every mark in a column not divisible by three counts
toward `F`: a horizontal midpoint in the interval would give its
owner axis H. Exceptional rows `3i,3j` enclose `L=3(j-i)-1` rows.
The [mixed-block exchange](SINGLE_CROSS_MINOR.md) forces `3e≥L-4`
for the off-phase count `e` there, hence `e≥j-i-1` by integrality.
For `j-i=1` just use zero.

At an outer end with `L=3i>0` rows before the first exceptional row,
retain the last row as a gate, deleting its off-phase marks. Put
complete pitch rows in the other `L-1` rows. Their rails attach to
the retained forest only once each. Maximal score implies the holes
filled were no more numerous than all off-phase marks in the interval.
Every old nongate row had a hole or an off-phase mark, so `2e≥L-1`,
in particular `e≥i`. The far end is identical. With no exceptional
lines, replace the entire board by parallel rails, giving `2F≥n`.
The disjoint interval requirements sum to at least `m-b`. Both axes
are essential: transposition lets us use the smaller of `r,c`.

At 103, `m=35`. For a no-pitch score of 3647 the joint count requires
`F≥7+b+C` before the three slacks, so `F≥8+b`. The mixed-block bound
gives `F≥35-b`; together these require **`F≥22`**. In the first
remaining stratum `F=22`, `b` is 13 or 14, and `C` plus the three
slacks is at most two. More generally any no-pitch global maximum
has `M≤3m²-2m-1+2F`. These are necessary conditions, not an upper
on `F` or a proof of a loss-78 cut.

There is also a local lower bound on the rank price `C`. Call an
off-skeleton mark anchored if one of the two midpoints between it
and its nearest junction is marked. In the skeleton-only forest
the off-skeleton **vertex** then already belongs to a junction's
component. Each adjacent pair of anchored off-skeleton marks supplies
a distinct additional forced edge between such components. Contract
the skeleton forest: the additional edges are acyclic even jointly.
The number of components touched is at most `C` since each realized
coarse path survives in the skeleton forest. Therefore `P` such pairs
require `C≥1+P`. For example the `F=22` stratum permits at most one
anchored pair anywhere in the square.

```
python3 -B -m analysis.research_program.pitch_skeleton_ledger
```

The replay physically attains 3638 on the side-103 skeleton. On the
3646 comb the exact inventory is `F=40, r=3, c=35, C=15`, slacks
`6,7,3`. In the no-pitch scattered control a deficient interval
replays an 89-mark improvement, not merely a count of potential moves.
