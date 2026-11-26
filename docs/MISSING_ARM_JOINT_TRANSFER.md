# A spanning component is an interface variable, not two external roots

Continue the [missing-arm block](MISSING_ARM_BLOCKS.md) with
`k=39+14t`, `H=12+8t` and `M=k-2`. Its `H` north rods each have a
tooth. The other marked sites form **one** unrooted tree `U`: the middle
rods all join the same transverse rod near the south end. Both lateral
cuts expose `U`. Replacing the two exposed ends by independent roots
would change the problem.

The new transfer extends each side by a band of two, three or four
columns with every intermediate cut joined. It inserts each forced edge
once, tests every intervening physical plaquette, and keeps the frontier
partition plus two permanent vertices: `R` (the contracted perimeter)
and `U`. On the old cut an edge to a rooted site merges with `R`; an
edge to the exposed tree merges with `U`. A cycle rejects the transition.
A marked component that disappears without either vertex is rejected.
The output records two sets of **exact deficits**, for `R` and `U`
separate or connected. No open paths at the far edges of the new bands
are counted as roots. For independently chosen west and east widths,
the overall cost set consists of the sums `open_W + joined_E` and
`joined_W + open_E`; joining neither leaves a rootless tree, and
joining both makes a cycle.

At every tested width 2–4 the open sets are nonempty, but the joined
set is **empty on each side**, at any cost. The earlier one-column test
gives the same result. This rules out full rooting by any combination
of these caps, including at the exact budget `198+72t`. This is graph
exhaustion, not a SAT exclusion. For universality take the union over
additional homogeneous longitudinal steps until no states are added.
On the east the switch coordinate is `p=1+floor((H-1)/3)`. Check all
phases before `p=9`, then close the 7 and 56 runs independently; at
the west only the 56 length varies. Additional columns in this test
are in the bulk transverse chart (on the east at least four physical
fringe columns are still outside the cap).

There is also an obstruction to **any** completion of this fan, even
allowing the remaining marked components to find their teeth farther
away. Two consecutive 56 masks in a column force the corresponding
pair in the next bulk column, in either direction, to be one of
`(48,56),(56,56),(56,24)`. Therefore a run of length `L` leaves an
interior run of length at least `L-2` after one step. In transverse
types 2 and 10 no such pair is possible. Thus, at tile column `i`,
`3<=i<=k-4`, a 56 run confined to longitudinal bulk rows `6..k-7`
has length at most `2*min(i-3,k-4-i)+1`. No arm or cut partition
assumption is needed for this local bound. In the fan's last column
`i=k-9` it allows at most 11, whereas the actual bulk run has length
`k-6-max(6,p+1)`, already 27 at `t=0` and increasing thereafter.
So the specific exact-budget fan projection cannot occur in a complete
equality witness at **any** of these sizes.

## A width-independent test for recurrent cuts

Consider a bulk missing-arm block repeated side by side, with both cuts
glued to form a transverse cylinder. Require an acyclic forced graph
with at most one perimeter tooth per component. **Every longitudinal
slice incurs at least one deficit, irrespective of the period width.**
In particular the cost of one period is at least `k`. This is a theorem
about periodic closure, not a lower bound of `k` on an arbitrary open
block whose marked paths can exit laterally.

Proof: if one slice has zero deficit then all of its tiles have three
marks. Neighboring three-mark tiles have equal masks. The transverse
masks 73, 146, 292 already give a winding forced cycle, so the
common mask must be 7, 56 or 448. Each defines a family of three masks:
`{6,7,3}`, `{48,56,24}`, `{384,448,192}`, respectively. On an adjacent
slice, a plaquette `(a,b,c,d)` is an edge `(a,b) -> (c,d)` in the
transverse direction. A full period is a closed walk in this graph,
hence stays in one strongly connected component. Restrict both input
masks to the family. Enumeration in both longitudinal directions and
all 13 position types shows that the output masks are either in the
same family or all equal to a transverse winding mask. This also holds
with the union of all certified isolate phases at the north.

Induct to the ends. Within each family `(left,full,right)` the
catalogue never allows the old slice to contain `right` or the new one
to contain `left`. The end slices are forced to be `left` and `right`;
all internal slices are `full`. Each straight longitudinal rod then
connects two teeth. This contradiction proves the deficit bound. In
particular repeating one rooted, cyclically compatible period of `h`
tile columns `b` times would cost at least `bk`. At equality `b<=5`,
since `198+72t<6k`. A single block paying a bounded cost while growing
in length cannot close its two cuts by periodic identification. The
argument gives no such obstruction to a nonperiodic sequence with
different incoming and outgoing connections.

The [nonperiodic component ledger](NONPERIODIC_COMPONENT_DEBT.md)
prices births, carries their labels through mergers, and bounds the
aggregate excess traffic at arbitrary cuts of a candidate square.

```
export PYTHONPATH=target/pb-python
python3 -B -m analysis.research_program.missing_arm_joint_caps
python3 -B -m analysis.research_program.missing_arm_period_bound
```
