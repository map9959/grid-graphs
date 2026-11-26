# Exact residue-two progression `n=53+42t`

For every integer `t>=0`, set `n=53+42t`, `k=17+14t` and `T=3k²+7k`.
Then **`P(n,n)=T−1−2t`**. The lower construction is exactly
`analysis/research_program/repair_53.py:repaired`. The upper is the
[unrestricted period-three theorem](UNRESTRICTED_PERIOD_THREE_UPPER.md).
Here is the uniform acyclicity and connectivity argument.

### The repaired prefix

Put `F=8+7t`, `m=3+2t`, `M=3m`. Include rows `0..H`, `H=F+4`,
so the prefix ends on the second regular row with left tip `3F`.
It consists of the following straight marked rods; ranges are inclusive.

* `B`: the horizontal bar on row 0, columns `2..n−4`.
* `W_a`, `0<=a<k`: column `3a+2`, from row 2 through
  `2+min(a,k−1−a)−[a<m]`. An empty interval means no rod.
* `L_a`, `R_a`, `0<=a<=F`: columns `3a` and `n−1−3a`, both ending
  on row `H`. For `a=0` both start on row 0. For `a>0` the right
  start is `3+a`, the left start `3+a−[a<=m]`.

These intervals result by reading the advancing rows of `build`
columnwise. The left repair advances the first `m` nonboundary left
starts by one row, shortens `W_0,...,W_(m−1)` by one, fills the left
boundary gap, and removes `(0,1)`. Thus the unshortened `W_m` marks
the end of the repair.

The forced graph of one rod in isolation is a path with leaves. Two
such trees can meet only at marked Manhattan distance at most two.
The following is the **complete** contact list; every listed pair is
at axial distance two at exactly one endpoint pair, hence shares a
single unmarked vertex:

| Rods | Shared vertex `(row,column)` |
|---|---|
| `B`, `W_a`, `1<=a<k−1` | `(1,3a+2)` |
| `B`, `L_0` | `(0,1)` |
| `W_m`, `L_m` | `(m+2,M+1)` |
| `W_(k−1)`, `R_0` | `(2,n−2)` |

For example, `L_a` can approach `W_a` on its right or `W_(a−1)`
on its left. Advancing a left start and shortening a wedge end cancel
before `a=m`; at `a=m` the start advances but the right wedge end is
not shortened. This creates the single contact at column `M+1`.
`repaired_prefix_symbolic.py` checks the interval decomposition and
the table **for arbitrary `t`**: it asks for a position where the
row rule differs from the rod rule, or a pair of rod endpoints/sites
where Manhattan distance `<=2` differs from the table. The predicates
are linear integer arithmetic with constant divisors; all counterexample
queries are unsatisfiable. The script checks the converse inclusions too.

The contact graph is acyclic: the bar is the hub of a star, extended by
one edge from `W_m` to `L_m`; the right boundary contact is separate.
All other rods are disjoint. Gluing the rod trees at these distinct
vertices therefore gives a forest (remaining vertices are isolates).
On row `H` each rail is joined to its immediate horizontal neighbors.
The single site between these neighborhoods is isolated on the frontier:
the preceding regular row has the identical marks and sends vertical
edges only down the rails. **The only identification between different
rail neighborhoods is `L_0 ~ L_m`, i.e. columns `0 ~ M`.**

### Propagation and closure of the extra connection

Write `A(L)={0,3,...,L} ∪ {L+4,L+7,...,n−1}`. A canonical frontier
has one component for each marked rail and its neighboring sites, with
the uncovered site a singleton. From the second regular row of a band,
the usual seven-row transition takes the canonical `A(L)` frontier to
the canonical `A(L−3)` frontier without a cycle; see the
[local transition and padding argument](RESIDUE_TWO_ZIPPER.md#geometry-and-why-it-stays-acyclic).
There are `B=5+5t` full bands and two further regular rows:
`n−8−F=7B+2`. Thus this transition runs `B` times and ends at
`3F−3B=M`.

To transfer the calculation to the repaired case, first process a band
with the canonical input. Both rails 0 and `M` are marked in **every
row** of this transition, since `M<=L−3`. They are distinct components
at the output. Hence their input components were never joined during
the transition. Identifying those two components at the start cannot
create a cycle: it just glues two disjoint trees. At the output it
merges exactly those same two canonical classes. This proves the
repaired invariant by induction, including the final transition onto
the two extra regular rows.

The five cap rows now follow **directly** from the second regular row
at `M` (not after five more band rows). Before the full bottom row, the
first three cap rows have stationary rails `0,3,...,M−6` and
`M+4,M+7,...,n−1`, with extra offsets from `M` respectively `{2}`,
`{−4,−3,−2,−1}`, `{1}`; the fourth row is empty. Contract the input
frontier using the identification `0 ~ M`, add each forced edge once,
and project onto each new row. `repaired_cap_frontier.py` checks the
minimal interface `M=9, width=23`: there is no cycle and the empty
penultimate row has all singleton classes. Thus the bottom bar can
join its tips without closing a cycle.

For any larger interface insert whole three-column pitches on either
side. On the left insert between rails 0 and 3 (translating the
changing sites and the distinguished `M`, not column 0); on the right
insert between stationary right rails. In rows before the bottom bar
each inserted rail and its leaves are disjoint from the old graph:
there are two unmarked columns between successive marked rails, and
the inserted input triple is independent of the distinguished pair.
On the empty row it contributes one independent tip and two isolates.
These remain distinct, so widening the full bottom bar merely joins
additional singleton classes. The required increments `M−9` and
`(n−M)−(23−9)` are nonnegative multiples of three. This proves the
cap check for all `t`, without extrapolating from boards of bounded size.

### Score and reproduction

Count first in the unmodified layout. The top has `(n−2)+1+(k+1)`
marks, the advancing rows `Fk`, the full bands `B[7(k+1)+1]`, the
two regular rows `2(k+1)`, and the cap `3k+3+n`. The repair adds
one net mark: the two top-corner flips cancel; there are `m+1`
diagonal additions and `m` deletions. Substitution gives
`3k²+7k−1−2t`. This equals the certified upper because
`floor((23−2k)/14)=−1−2t`. Connectedness of the grid lets the forced
forest extend to a spanning tree.

```
# Symbolic checks require z3-solver (tested with 5.4.1.0).
PYTHONPATH=target/z3-python python3 -B -m analysis.research_program.repaired_prefix_symbolic
python3 -B -m analysis.research_program.zipper_frontier
python3 -B -m analysis.research_program.repaired_cap_frontier
python3 -B -m analysis.research_program.repair_53
```

This is a computer-assisted proof, not a Lean theorem. The SMT check
concerns the explicit rod formulas; the independent frontier and score
arguments connect those formulas to the grid optimum.

## Two waiting rows: the progression beginning at 47

For `n=47+42t`, `k=15+14t`, use `build(n,extra=2)` instead of
`build(n)`, and apply the upper-left repair with `m=3+2t`, `M=3m`.
At 47 this changes nine sites of the 778-site forest: remove `(0,1)`,
add `(1,0)`, add `(a+2,3a)` for `0<=a<=3`, and remove `(a+2,3a+2)`
for `0<=a<3`. The cap at the bottom remains unchanged.

Here `F=7+7t`. Up to row `F+4` the same rod table applies: those last
two rows are now the two waiting rows. The symbolic checker verifies
the prefix and contact list with these parameters. The following two
regular rows (the start of the first full band) preserve the partition:
the only edges across each row boundary are vertical edges on the rails.
Each new rail neighborhood thus attaches once, and the uncovered gap
site is a fresh singleton. In particular this step does not reconnect
the two input rails already joined through the prefix.

The remaining transition argument is exactly the one above: after
`B=4+5t` full bands, `3(F−B)=M=9+6t`; two final regular rows precede
the direct five-row cap. Equivalently `n−8−F=2+7B+2`. The local
checks still apply: every complete band starts at `L>=M+3>=12`, the
right margin is at least that of the width-23 representative, and the
cap starts with the same single identification between rails 0 and M.
The count in the previous section gains `2(k+1)` for the two waiting
rows, with the new `F,B,k,n`. Substitution gives `T(k)−1−2t`, exactly
the integer upper. Hence **`P(47+42t,47+42t)=T(15+14t)−1−2t`**.

```
PYTHONPATH=target/z3-python python3 -B -m analysis.research_program.repaired_prefix_symbolic 47
python3 -B -m analysis.research_program.repaired_cap_frontier
python3 -B -m analysis.research_program.replay_47
```

The final replay also checks the actual rail partition at every band
boundary and the degrees in completed trees at both 47 and 89.

## One waiting row: the progression beginning at 71

For `n=71+42t`, put `k=23+14t`. Use one extra regular row before the
first band and make the same upper-left repair, now with `m=4+2t`,
`M=3m=12+6t`. At 71, the one-waiting-row layout alone has 1745 marks.
Switch `(0,1)` off and `(1,0)` on; add `(a+2,3a)` for `0<=a<=4`
and remove `(a+2,3a+2)` for `0<=a<4`. The resulting 1746 marks force
5038 acyclic edges, and the three components complete to a spanning tree.

For the entire progression `F=11+7t` and `B=7+5t` satisfy
`n−8−F=1+7B+2` and `3(F−B)=M`. The symbolic prefix checker verifies
the same rod decomposition and complete contact table with these
parameters; in particular the sole extra frontier connection is `0~M`.
The prefix ends on the second regular row. With one waiting row, just
one further regular row is needed to reach the end of the first band's
two regular rows. Each rail neighborhood attaches only to itself in
that step. Thereafter the `B` verified band transitions finish with
the two regular rows at `M`. Width padding is valid: the final `M` is
at least 12, the starting left tip is `3F`, and even the smallest right
margin is `n−3F=38+21t`. The cap therefore has only singleton frontier
classes before the bottom row is added.

The marked-site count is

```
(n−2 + 1 + k+1) + Fk + (k+1) + B[7(k+1)+1] + 2(k+1) + (3k+3+n) + 1.
```

This equals `T(k)−2−2t`, exactly the unrestricted integer upper since
`floor((23−2k)/14)=−2−2t`. Thus **`P(71+42t,71+42t)=T(23+14t)−2−2t`**
for every integer `t>=0`, including 4362 at side 113.

```
PYTHONPATH=target/z3-python python3 -B -m analysis.research_program.repaired_prefix_symbolic 71
python3 -B -m analysis.research_program.repaired_cap_frontier
python3 -B -m analysis.research_program.replay_47 71 113
```
