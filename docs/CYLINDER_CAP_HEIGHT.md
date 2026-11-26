# Finite height suffices when looking for a periodic wired cap

This is a reduction for the residue-one **construction** problem. Take
width `W=3r` with horizontal period `W` and a wired row of rail terminals.
If a periodically repeated cap of any height gains `b>0` marks over
`r` per free row, one with at least that gain has height at most
**`6(W-3b)+5`**. There is no bound on the original height. The
period restriction here is not an assumption about the optimum square.

The [run-join tariff](CAP_RUN_JOINS.md) also excludes the comb rate
at every period when the only horizontal runs of length at least two
are full bars.

Work in the cylinder quotient of the forced star graph, contracting
the exterior wired tree to a single vertex. The root component must
be a tree. Any other component is a tree or a unicyclic graph whose
unique cycle winds around the cylinder: a contractible cycle lifts
to a cycle, and a component of cycle rank at least two also has a
closed nonbacktracking walk of winding zero (take a commutator).
Conversely these conditions suffice for a periodic forest after
unrolling, with all top terminals still wired. In particular a fully
marked row is an essential cycle in its own unrooted component.

Let `M` be the mark count, `H` the height, `R` the number of straight
marked runs other than fully marked horizontal rows, and `s` the
number of unrooted tree components, including isolated vertices.
Diagonal mark pairs are impossible, so the number of marked-marked
edges is `M-R`. Write `T,D` for the number of marks on the first and
last free rows. When `H=1` both terms count that row. Counting edges
including the `r` compulsory top spokes gives

```
WH-s = 3M + R - T - D + r.
```

Thus `R ≤ W-3b`, since `T≤r`, `D≤W`. In the equivalent event budget,
the sum of bottom holes, starts *after* the first free row and tree
components is `2r-3b`. Every top mark starts a run for `W≥3` with
pitch-three terminals, so the top marks cancel exactly.

Choose a shortest witness of gain at least `b`. It has at most one
fully marked row. Indeed split at any two such bars, viewing the
upper prefix ending at each bar separately. Neither last bar has a
sink: orient its entire cycle around the cylinder, and every attached
tree toward it. Restrict an orientation of the longer prefix to the
shorter one: no arrow leaves the earlier full row downward, since
it too must orient around its cycle. The number of sinks and the
number of run starts in the longer prefix are at least those in
the shorter. Both end with `D=W`. The edge identity shows that the
longer prefix has no larger gain. Replace it by the shorter one:
the frontier in both cases is the identical full bar, disjoint from
the wired root, with exactly its own essential cycle. The same suffix
can attach to it. This strictly shortens the witness.

Now flag the full row, if present, and the rows containing endpoints
of the `R` other runs. There are at most `2R+1` flagged rows.
Consecutive unflagged rows have identical masks: every mark in
either must be an interior site of a vertical run (a finite horizontal
run flags its whole row). Three such rows cannot be consecutive.
Otherwise remove the middle one. The remaining two equal rows become
neighbors; their only forced crossing edges are the vertical edges at
the marked columns. This shortens those paths and removes unmarked
leaves and isolates in the deleted row. Distinct marked columns are
at least three apart: distance one forces a face cycle, and distance
two gives two joins between the runs. Thus at most `r` marks are
removed. The gain does not decrease. The at most `2R+2` gaps of
unflagged rows therefore have length at most two, giving the claimed
height bound. Padding by straight rail rows at the wired end preserves
gain, so a single bounded height can alternatively be used for an
existence test.

For period 9, `src/bin/cylinder_cap.rs` gives a stronger direct check:
even allowing a contractible cycle in a floating component, the full
normalized score vector is dominated at height 18; the maximum bonus
is zero. A bonus of one per nine columns cannot supply the missing
residue-one slope by simply making this periodic cap deeper.

## Sharper cutoff and period 18

In fact a shortest witness has no interior full row: cutting immediately
after such a bar can only increase the gain. In the prefix identity the
bottom count becomes `W`, the run-start count cannot increase, and the
sink count cannot increase (the bar orients around itself, so truncation
removes no outgoing arrow from a retained site).

Let `E=2r-3b`. In any triple of consecutive non-end rows, either a
run starts in the triple or the middle row has an isolate. Otherwise
each of its three masks consists solely of marks inherited from the
row above: a horizontal run with a first site would have a start
there by diagonal exclusion, and there is no full row. Write the masks
`A⊇B⊇C`. The marks of `A` have spacing at least three, since they
also occur above `A`. For the middle row to be covered the radius-one
horizontal neighborhoods of `A` must cover the circumference (all
three masks are subsets of `A`). Thus `A` is an exact pitch-three
profile. If `B` drops any of its centers, the adjacent lateral sites
in the middle row are uncovered. Hence `A=B`. Delete one of these
two identical profile rows: each pitch-three group in the pair is a
six-vertex tree with one vertical edge between its centers. The
replacement is a three-vertex tree with the same exterior attachment
class; it neither creates a cycle nor changes winding. It removes
exactly `r` marks, contradicting minimal height. Partitioning the
`H-2` non-end rows into triples gives **`H≤3E+4`**.

For a period of 18 columns a gain of two would therefore exist at
height 22 after padding. In each nine-column band retain one extra
halo column on either side. Charge half a unit at each horizontal
end of a new run (a vertical start gets a whole unit), one at a
central isolate, and one per central bottom hole, omitting top starts.
The two complementary bands together get at most six units. In
half-units each band costs at least four by all-height shortest path,
so its budget is at most eight. At height 22, project the forward and
backward minimum costs onto the physical row words. For every split
into complementary bands use the same 18-bit word. A complete forced
horizontal cycle on the bottom cannot belong to the wired component;
apply this once all remaining bottom words contain that cycle.

The support fixed point is nonempty. Replaying its row words with
**one** full circumference partition, allowing an arbitrary single
cycle in each floating component, gives maximum bonus **one**.
Thus even a period-18 cap of unrestricted depth cannot gain two per
period. This is a construction-class exclusion, not a square upper.

```
python3 -B -m analysis.research_program.cap_sync18_check
# full pseudoforest maximum on survivors 1 peak 12921
```
