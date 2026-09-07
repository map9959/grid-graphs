# L2: Terminal Rail Repair Research

Date: 2026-09-06.

## Result And Status

There is a concrete terminal-rail surgery whose original paper forest proof
is now backed by **uniform, strictly compiled Lean theorems**, with score

```text
G(s) = 3s^2 + 12s + 12 + floor(s/2),   s >= 2, n = 3s+5.
```

It improves the source staircase by one preserved vertex when s is even,
and is count-neutral when s is odd. It changes a rail, not merely the fixed
bottom pocket. The exact support intersections proving feasibility are below.
`Constructions/ResidueTwo/RailRepair/{Geometry,Forest,Score}.lean` now proves
the coordinates, physical attachments, unconditional forced acyclicity, and
exact score. The endpoint `GridGraphs.RailRepair.residueTwo_le_maxPreserved`
gives the current formal lower bound

```text
L(k) = 3k^2+6k+3+floor((k-1)/2) <= P(3k+2),   k>=3.
L(k) = T(k)-floor(k/2)+2,                     k>=5,
where T(k)=3k^2+7k.
```

Thus the gain is one at odd k and zero at even k, since k=s+1. The earlier
research-only pass did not change Lean; the later formal milestone does.

**It does not solve L2.** Its six-width difference is still `12s+37`, not
`12s+38`. One repair at the terminal end does not accumulate one extra vertex
per step. A precise attempted repetition and its component collision are
given below; there is no claim of general impossibility. In k notation the
checked step gains 12k+25, not 12k+26. The separate
[propagating-interface alternative](L2_PROPAGATING_INTERFACE.md) remains a
paper forest argument for an unsuccessful actual-gain candidate; it is not
the now-verified single terminal repair.

Separate finite exhaustive experiments ran only at n=11 and n=14. They
found a 49-center repair of the 48-center n=11 source seed. With the frame
and all earlier rows fixed, arbitrary repacking of the last four deep rows
has maximum 49 at n=11 and 76 at n=14. These are **finite, restricted-class
computations**, not uniform upper bounds or a global optimality result. They
remain historical finite evidence, separate from the later uniform Lean proof.

Current formal intervals (the global upper formula is unchanged):

| Side | Lower | Global upper |
|---:|---:|---:|
| 17 | 110 | 114 |
| 20 | 149 | 154 |
| 23 | 195 | 201 |
| 26 | 246 | 254 |
| 29 | 304 | 312 |

In particular the uniform 110 lower matches a prior finite witness, but does
not prove P(17) exact. All sharp global upper and target-pump obligations remain open.

## Source And Convention

Read together with `HANDOFF_U1_U3_L2.md` and `L2_FIXED_RAIL_POCKET.md`.
All coordinates are ambient, zero-based; intervals are inclusive. Put
`h=3s`, `n=h+5`, and `k=s+1`. The preserved source geometry is:

```text
Fouter = boundary minus
         {(0,1),(0,2),(1,h+4),(h+4,h+3),(h+3,0)};
z      = (2,2);
R_j    = {(3j+3,c): j+4 <= c <= h+2},  0 <= j <= s-1;
L_j    = {(3j+5,c): 2 <= c <= j+3},    0 <= j <= s-2;
B      = {(h+2,s+2-4t): t >= 0, s+2-4t >= 3};
P      = {(h+1,s-4t):   t >= 0, s-4t >= 3}.
```

Actual source inspected, paths relative to `lean/GridGraphs/`:

| Source | Relevant content |
| --- | --- |
| `Constructions/ResidueTwo/ResidueTwoStaircase.lean:43-57,152-180` | Coordinates and counts of z,R,L,B,P |
| `Constructions/ResidueTwo/ResidueTwoStaircaseForest.lean:14-63,104-166,269-305` | Interval trees, footprint inclusions, source feasibility and score |
| `Constructions/BoundaryFive/BoundaryFiveFrame.lean:19-35,198-217,363` | Actual holes, exact frame support, tree on that support |
| `Constructions/BoundaryFive/BoundaryFiveConstruction.lean:19-29,45-52` | Deep square and exact forced-graph union |
| `Constructions/ResidueTwo/Staircase/ComponentLedger.lean:118-182` | Actual seed profiles and insufficient source step |
| `Surgery/ForcedExchange.lean:199-239` | Exact insertion criterion, including the center |

Write H(F) for all grid edges incident to F, on **all n^2 vertices**.
An interval of centers `(r,a),...,(r,b)` has exact support

```text
row r:     [a-1,b+1];
rows r+-1: [a,b].
```

Its graph is a horizontal path with vertical pendant edges. The source
proves the support inclusion; equality follows because every listed vertex
is incident to an edge from a center. All intervals used here are nonempty
and interior, so there is no clipping or degenerate empty-interval issue.

For a forest H(F) and u outside F, insertion is legal exactly when the
vertices of `{u} union (N(u) minus F)` lie in pairwise distinct components
of H(F). This is not a test on all four neighbors regardless of preserved
status. In particular, a center already in support need not be isolated.
No global rootedness assumption is used.

## The Successful Single Repair

Remove all source B and P. Shorten the last right rail by deleting its
first three centers, keeping all other z,R,L centers and the frame:

```text
delete from R_(s-1): (h,s+3), (h,s+4), (h,s+5);
R' = {(h,c): s+6 <= c <= h+2}.
```

Call this fixed set K. R' has length `2s-3 >= 1`, retaining its original
right-frame attachment. Add these three pieces:

```text
U = {(h-1,s+4)};
V = {(h+1,c): s+1 <= c <= s+3};
W = {(h+2,s+5)}.
```

Finally fill the reduced left pocket with alternating singletons:

```text
X_t = {(h+2-(t mod 2), s-1-2t)},
t >= 0, s-1-2t >= 3.
```

There are `q=floor((s-2)/2)` such singletons. This definition includes
the empty pocket at s=2 and s=3. The repaired set is K union U,V,W,all X_t.

### Checkable Support Invariant

H(K) consists of one tree on support M_K and isolated vertices elsewhere.
This is a conclusion about K, not an assumption about arbitrary forests.
The frame support is the outer two rings minus `(1,2)`. The exact interval
supports of z,R,L are mutually disjoint. Shortening R preserves that
disjointness and leaves its attachment `(h,h+3)` present. Every other
interval retains its one frame attachment as in the fixed-pocket note.
Thus each interval tree glues once to the frame tree.

The new pieces have the following **exact** intersections with M_K:

| Piece | Its entire intersection with M_K | Source of attachment |
| --- | --- | --- |
| U | `{(h-2,s+4)}` | Lower leaf of R_(s-2), whose row is h-3 |
| V | `{(h,s+1)}` | Lower leaf of L_(s-2), whose rightmost center is (h-1,s+1) |
| W | `{(h+3,s+5)}` | Bottom next ring |
| X_t on row h+2, column c | `{(h+3,c)}` | Bottom next ring |
| X_t on row h+1, column c | `{(h,c)}` | Lower leaf of L_(s-2) |

These attachments exist even at s=2. In particular R_(s-2)=R_0 exists,
and its lower leaf at column s+4 is in range. The attachment of V is an
unpreserved leaf, not a preserved center.

Here are the coordinate inequalities needed to check both uniqueness and
mutual disjointness of the **new supports**:

1. U occupies row h-1, columns `[s+3,s+5]`, and column s+4 on rows h-2,h.
   L_(s-2)'s same-row support ends at s+2. R' has upper leaves starting
   at s+6 and same-row support starting at s+5. Thus neither meets U.
   Only the previous right rail reaches U at `(h-2,s+4)`.
2. V occupies row h+1, columns `[s,s+4]`, and columns `[s+1,s+3]` on
   rows h,h+2. The last left rail's lower leaves end at s+1, giving
   precisely its listed attachment. R' begins too far right to meet V.
   U's lower leaf has column s+4, outside V's row-h support.
3. W occupies row h+2, columns `[s+4,s+6]`, and column s+5 on rows
   h+1,h+3. These are disjoint from V's corresponding slices, and from
   R', whose row-(h+1) leaves start at s+6. Only its bottom leaf meets
   the frame. The inequality `s+6 <= h+2` holds for s>=2.
4. Bottom X columns are at most s-1; upper X columns are at most s-3.
   Their supports therefore miss U,V,W and R'. Each has exactly the
   table's one old attachment. Successive X columns differ by two and
   alternate rows, giving Manhattan distance three. Same-row centers
   differ by four. Hence all X supports are pairwise disjoint.

The table and these inequalities give a uniform gluing invariant:
**each new interval/star is a tree; its support meets M_K exactly once;
the new supports are pairwise disjoint.** Their union with H(K) is a tree
on its support, with all remaining ambient vertices isolated. This accounts
for every forced edge, not the induced grid graph on the support.
The argument was a uniform paper proof, not an extrapolation from two boards;
its coordinate/support and acyclicity claims now have the uniform Lean backing
listed above. This includes nonempty X pockets, unlike the finite seed replays.

### Count And Component Ledger

K has `3s^2-3` deep centers. U,V,W contribute `1+3+1=5`; the frame has
`12s+11` centers. Consequently

```text
G(s) = 3s^2 + 12s + 13 + floor((s-2)/2)
     = 3s^2 + 12s + 12 + floor(s/2).
G(s) - source_score(s) = 1 if s is even, 0 if s is odd.
```

As additional paper consequences, there are four induced boundary carriers,
2s retained z/R/L carriers, three new U/V/W carriers, and q X carriers.
No new center is adjacent to an old preserved center outside its piece.
Thus the usual exact forest ledger gives

```text
r = 2s+7+q = 2s+6+floor(s/2);
b = 5;
c = 4s-2-4floor(s/2).
```

These separate r,c,b formulas remain paper consequences for this repaired
family, not new Lean component-count theorems. The formal milestone checks
the score and acyclicity, not every consequence in this note. Its nonisolated
support is one tree; c-1 counts actual isolates in the paper argument.
Under s -> s+2, r increases by five and c by four. The combined cost still
increases by nine, instead of the target six.

## Actual Rootless Attachment Experiment

A different, tempting surgery is to delete the **rightmost** terminal
center `e=(h,h+2)`, instead of its first three centers. Start from F0 in
the fixed-pocket note, with no B or P, and delete e. Its remaining rail

```text
D = {(h,c): s+3 <= c <= h+1}
```

is a rootless forced tree. Its exact support is disjoint from the tree M
containing the frame and all other rails. D's support has `6s-1` vertices.
All vertices outside these two supports are isolates. Deleting e does
not delete the edge from e to its still-preserved left neighbor; e is now
the right endpoint leaf of D. The old spoke to `(h,h+3)` is gone.

For any `s+3 <= c <= h+1`, the bottom center u=(h+2,c) has insertion
components

```text
u: singleton;
(h+1,c): D;
(h+3,c): M;
(h+2,c-1): singleton;
(h+2,c+1): singleton.
```

These are **five different components**. Inserting u is legal, joins D to
M, and decreases the full-vertex component count by four. Disallowing a
star that touches two nontrivial components would wrongly reject this move.

But a second such bottom center is illegal: its upper and lower neighbors
are now in the same component. The old left-pocket allowable centers and
spacing still give at most ceil(s/2) centers. No other pocket positions
become legal: p_(s+2) has two neighbors in D; p_c above a retained rail
center closes a unit square; p_(h+2) has both its upper and left neighbors
in D; b_(h+2) has its lower and right neighbors in M. The left-edge
exclusions remain unchanged.

Thus this exact endpoint-deleted, otherwise fixed geometry permits at most
`ceil(s/2)+1` pocket centers. The bound is attained by keeping source B,P
and adding `(h+2,h+1)`: its star is disjoint from their stars since the
closest same-row column gap is `2s-1 >= 3`. Paying one deleted center for
one extra insertion is **count-neutral**, not a missing-vertex recovery.
This is an obstruction for this specific cut-and-pocket candidate only.

## Why The Repair Is Not A Pump

For the successful first-three-centers repair,

```text
G(s+2)-G(s) = 12s+37;
T(s+1)-G(s) = ceil(s/2)-2,   where T(k)=3k^2+7k.
```

The gap identity is over integers; it equals -1 at s=2. At s=4 it is
zero, so the original s=2 seed followed by one repaired terminal pattern
has the desired first even-s score step, now supported by the formal lower
theorem. There is no all-step
closure. The odd-s seed branch gains nothing from this repair.

A precise attempted repetition is to translate U,V,W three columns right,
delete the next three R' centers `(h,s+6..s+8)`, and insert

```text
U2 = {(h-1,s+7)};
V2 = {(h+1,c): s+4 <= c <= s+6};
W2 = {(h+2,s+8)}.
```

For s>=4 those next three rail centers exist and a nonempty tail remains.
Even allowing deletion of W to remove its immediate conflicts, this fails:
before inserting `v=(h+1,s+4)`, v is already V's right endpoint leaf in
the main component. Its upper neighbor `(h,s+4)` is U's lower leaf in
that **same** component. Both are unpreserved. Their edge is genuinely
new, so the insertion criterion fails. Their old path runs through V,
the last left rail, the frame, the previous right rail, and U. Deleting
the next three terminal-rail centers or W does not break that path.
Adding U2 earlier cannot repair a repeated component.

This identifies an actual attachment to change for further work: detach
either U from the previous right rail or V from the last left rail, or
relayout the intervening geometry. Merely adding another translated motif
cannot accumulate the gain. This is not an exclusion of other repetitions,
other rail translations, multiple attachment edits, or boundary changes.

## Current Verification

The latest recorded full strict build on Lean/mathlib 4.33.1 passed with
8,939 jobs, exit 0, zero warnings/errors. It includes the five new modules
OneExcessSeparated, CoveredBoundary, and RailRepair Geometry, Forest, Score
through root and Regression. Regressions cover both upper fronts, the symbolic
lower/upper interval, and lower bounds at sides 17, 20, 23, 29.
The inventory is 232 modules / 83,811 lines under GridGraphs, plus the
177-line root: 233 library files / 83,988 lines. All five new modules are
below 1,000 lines; the 11 pre-existing oversized modules were untouched.

All 147 public axiom audits (previous 72+31 rerun plus new 44) passed with
dependencies only in `{propext, Classical.choice, Quot.sound}`, with no
`sorryAx` or native proof axiom. This is snapshot coverage, not a whole-library
audit. The new driver is `/tmp/opencode/U1U3L2RailRepairAudit.lean`; logs:

- `/tmp/opencode/u1-u3-l2-rail-repair-full-build.log`
- `/tmp/opencode/u1-u3-l2-rail-repair-previous72-axioms.log`
- `/tmp/opencode/u1-u3-l2-rail-repair-previous31-axioms.log`
- `/tmp/opencode/u1-u3-l2-rail-repair-new44-axioms.log`
- `/tmp/opencode/u1-u3-l2-rail-repair-source-lengths.log`

See [handoff](HANDOFF_U1_U3_L2.md) and [Lean EVIDENCE](../lean/EVIDENCE.md)
for exact commands and audit scope. The latest main-agent Python test run
passed all 13 tests (three terminal, three propagating, seven layout), with
no searches:

```bash
env -u GRID_GRAPHS_SLOW -u GRID_GRAPHS_RUN_SLOW_TESTS python3 -m unittest \
  analysis.tests.searches.test_l2_rail_repair_research \
  analysis.tests.searches.test_l2_propagating_interface \
  analysis.tests.test_package_layout
```

These are recorded results, not a Lean build or test rerun in this docs-only
update. The upper checkpoint also includes root-separated hole charges
without saturation and actual pure-mass budgets. Conditional missing-side
sharpness needs p+|S|>=7, with no guaranteed S; covered-boundary budgets use
the same resources and are not independently addable. Neither changes the
unconditional upper formula. See the handoff for the exact hypotheses.

## Historical Bounded Verification

The original research pass added `analysis/searches/l2_rail_repair_research.py`.

```bash
python3 -m analysis.searches.l2_rail_repair_research
```

It has no dependencies beyond the standard library, writes no result files,
and materializes only s=2,3 (n=11,14). Constructors reject larger boards.
No Lean build, full build, solver installation, or search above 15 occurred
in that original finite-research pass.
The initial `python` invocation failed because only `python3` is available;
the complete `python3` run passed.

The module's exhaustive experiments run only through its guarded `main()`,
not on import. Focused tests in
`analysis/tests/searches/test_l2_rail_repair_research.py` replay the two fixed
seed repairs and rootless bridges, checking scores, insertion component
identities and sizes, support intersections, and rejection of a second
bridge. They also check the constructors' size bounds, without searching.
Run these and the existing package-layout tests from the repository root:

```bash
env -u GRID_GRAPHS_SLOW -u GRID_GRAPHS_RUN_SLOW_TESTS python3 -m unittest \
  analysis.tests.searches.test_l2_rail_repair_research \
  analysis.tests.test_package_layout
```

Packaging-pass result: all 10 tests passed (three focused repair tests and
seven package-layout tests). Only the fixed 11x11 and 14x14 witnesses were
materialized; the exhaustive searches were not rerun in this pass.

The packaging pass rechecked the paper support slices, the s=2 endpoint
bounds, the X_t spacing, and the repeated-component obstruction. It found
no change needed to that argument. At that historical point it was not a
uniform formal theorem: the finite tests have q=0 and do not check a nonempty
X_t pocket. No Lean proof or build was attempted in that packaging pass;
the subsequent formal milestone supplies the uniform proof separately.

The finite search fixes source centers outside
`Q4=[h-1,h+2] x [2,h+2]` and allows **every subset of Q4**, not just
horizontal interval layouts. Its second variant also deletes the boundary
center `(h,h+4)` and holds that deletion fixed. This variant changes b to
six; it is different from deleting the rail endpoint e above.

Search uses exact insertion-component partitions and a cardinality upper
bound for pruning. Illegal insertions remain illegal under further
insertions, so discarding them loses no feasible superset. Increasing
coordinate order enumerates each remaining subset once; a branch is cut
only when its number of remaining choices cannot beat the best count.
There is no heuristic cutoff. Reported maxima are ordinary Python
computations, not kernel-checked certificates.

| Finite class | n=11 maximum f / visited nodes | n=14 maximum f / visited nodes |
| --- | --- | --- |
| Q4, original frame | 49 / 1,996 | 76 / 118,446 |
| Q4, boundary attachment center deleted | 48 / 2,612 | 76 / 94,351 |
| Bottom two rows, rail endpoint deleted | 48 / 8 | 76 / 23 |

The uniform motif itself checks as `(f,r,c,b)=(49,11,2,5)` at n=11
and `(76,13,6,5)` at n=14. The first n=11 maximizing witness is exactly
the motif:

```text
delete: (6,5), (6,6), (6,7), (8,4);
insert: (5,6), (7,3), (7,4), (7,5), (8,7).
```

At n=14 the uniform motif is:

```text
delete: (9,6), (9,7), (9,8), (10,3), (11,5);
insert: (8,7), (10,4), (10,5), (10,6), (11,8).
```

The script reconstructs the complete forced graph after motif insertion,
compares every pair's connectivity with the incremental partition, and
checks `3f+r+c+b=n^2+4n`. It asserts the finite maxima and seed profiles,
and directly checks the motif's support-intersection table and pairwise
support disjointness. Both tested seeds have q=0; the nonempty reduced
left pocket was covered by the paper inequalities, not a finite experiment,
and is now also covered by the uniform Lean proof.
It also prints the component sizes for each
actual insertion. For the n=11 motif these are, in insertion order:

```text
(5,6): [1,102,1,1,1]
(7,3): [1,106,1,1,1]
(7,4): [110,1,1,1]
(7,5): [113,1,1,1]
(8,7): [1,1,116,1,1]
```

The two extensions inside V start in the existing main component and add
only three new edges each. The center was not omitted from the test.
For the rootless bridge before adding any pocket stars, component sizes
are `[1,11,98,1,1]` at n=11 and `[1,17,163,1,1]` at n=14. Distinctness
is tested by component identity, not by these sizes.

Remaining deliverable for L2: an accumulating rail/attachment invariant
with gain `12s+38`, compatible with both seed branches. The single-repair
support proof and its Lean formalization supply a concrete local construction,
but not that invariant. The separate paper propagating sweep does not recover
the lost center or meet the required gain; future work must change that actual
attachment/count geometry, not merely relabel components.
