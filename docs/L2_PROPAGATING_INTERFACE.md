# L2: Propagating Attachment Interface

Date: 2026-09-06.

## Outcome And Scope

**No target pump was found.** This note tests a new attachment edit, not the
single terminal repair now formally verified separately: cut the **preceding**
right rail's frame-side endpoint and transfer its attachment through a lowered
terminal rail. The concrete whole-rail sweep below has a uniform paper forest
argument, including a genuinely unattached intermediate component. Its score is

```text
J(s) = 3s^2 + 12s + 11 + floor(s/2),   s >= 2, n = 3s+5.
J(s+2)-J(s) = 12s+37 = 12k+25,        k=s+1.
```

Thus this exact candidate is refuted **as a target-gain pump**, not as a
forest construction. It misses the required gain by one, and its n=14 instance
has only 75 centers, so it does not provide the required odd-branch seed.
The shorter, two-extension version also has an explicit next-insertion cycle.
Neither conclusion is a general obstruction to changing rail attachments.

Two restricted exhaustive searches, only at n=11 and n=14, fix the same
preceding-rail cut but allow arbitrary last-four-row repacking. Their maxima
are 48 and 76. These finite maxima are not uniform bounds or global optima.
No n=17 or n=20 instance, and hence no actual six-width seed transition, was
materialized in this historical research pass. No Lean build or formalization
of this propagating alternative was attempted; that status remains unchanged.

The later formal milestone proves the different single-terminal score
`L(k)=3k^2+6k+3+floor((k-1)/2)`, k>=3, via
`GridGraphs.RailRepair.residueTwo_le_maxPreserved`. With the upper notes'
`T(k)=3k^2+7k`, it is `T(k)-floor(k/2)+2` for k>=5.
It gains one at odd k, agrees with the staircase at even k, and still gains
only 12k+25 per six-width step, not 12k+26. Do not transfer its formal status
to J(s), or mistake either family for an accumulating target pump.

The current lower/global-upper intervals are [110,114] at n=17, [149,154]
at n=20, [195,201] at n=23, [246,254] at n=26, and [304,312] at n=29.
In particular P(17) is not proved exact. The global upper formula is unchanged;
both upper branches and the target pump remain open.

Read first: [handoff](HANDOFF_U1_U3_L2.md),
[fixed-pocket argument](L2_FIXED_RAIL_POCKET.md), and
[terminal repair](L2_RAIL_REPAIR_RESEARCH.md). In the original research pass,
existing files were left alone; the accompanying script imports the existing
exact graph/search engine.

## Required Interface

Use the notes' ambient zero-based coordinates and inclusive intervals. Put
`h=3s`, `n=h+5`. Write `H(F)` for the graph of all grid edges incident to
preserved centers F, on **every ambient vertex**, including isolates.

An interface must carry the actual equivalence relation induced by components
on all vertices touched by a proposed insertion, not just frame-root labels.
For `u notin F`, the exact test is pairwise distinct component identities on

```text
{u} union (N(u) minus F).
```

The center is mandatory even when it is an unpreserved leaf of an existing
tree. Neighbors already preserved are omitted because their incident edges
already exist. Two nontrivial components can legally be joined; two different
attachment vertices in the same component cannot. Singleton components are
separate identities, not one common "unattached" label. Deletions require
recomputing connectivity, rather than simply deleting a component label.

The exact ledger `3f+r+c+b=n^2+4n` gives a useful necessary closure check.
Under `n -> n+6`, the right side grows by `12n+60=36s+120`. Target gain
`12s+38=12k+26` therefore requires

```text
Delta(r+c+b) = 6.
```

Only if b is retained may this be simplified to `Delta(r+c)=6`. This is
necessary accounting, not a geometric existence criterion. No fixed c,
connectedness, rootedness, or boundary-five hypothesis is imposed on a future
pump. Boundary five is a property of the particular candidates below.

## A Preceding-Rail Cut

Use the source F0 (frame, z, all R and L, without B,P). The preceding rail is

```text
R_(s-2) = {(h-3,c): s+2 <= c <= h+2}.
e       = (h-3,h+2).
D       = {(h-3,c): s+2 <= c <= h+1}.
```

Deleting e removes this rail's frame spoke, not the terminal rail's spoke.
The deleted center remains an endpoint leaf through its preserved left
neighbor. D is a nonempty interval of length `2s`, with support size `6s+2`.
Its support is disjoint from the frame component and from all other retained
rail supports. This follows directly from the source disjoint footprints and
the new maximum same-row support column `h+2`, before the frame at `h+3`.
Every vertex outside the nontrivial supports is its own isolated component.

This changes exactly the old path responsible for the U-to-V collision:
the previous right rail and U can now be separate from the last left rail
and V. It is not the endpoint-deleted *terminal* rail experiment in the
previous note.

## Concrete Continuation

Start with the previous note's repaired set K,U,V,W,X. In addition to e,
delete

```text
d = (h,s+6),        the first center of the repaired terminal tail;
w = (h+2,s+5),      its W singleton.
```

Both exist for all s>=2. Insert, in order,

```text
v1 = (h+1,s+4);
v2 = (h+1,s+5).
```

Before v1, its center is V's right endpoint leaf in the frame component M.
Its upper neighbor is U's lower leaf in the detached component consisting
of D and U. The lower and right neighbors are distinct isolates after the
deletions; its left neighbor is preserved and omitted. Thus v1 joins four
distinct components, including two nontrivial ones. D plus U has `6s+6`
vertices. After this join, v2 starts in the merged component and has three
new isolated neighbors. Each insertion decreases c by three, not four.

The finite replay reports sizes in center/up/down/right order:

| n | v1 component sizes | v2 component sizes | Final (f,r,c,b) |
| --- | --- | --- | --- |
| 11 | 92,18,1,1 | 112,1,1,1 | (48,9,7,5) |
| 14 | 158,24,1,1 | 184,1,1,1 | (75,12,10,5) |

Legality is checked by identities, not equality or inequality of these sizes.

### Exact Next Failure

The proposed third extension is `v3=(h+1,s+6)`.

- At s=2, the terminal tail was a singleton and is now empty. v3 is already
  the enlarged V's endpoint leaf in M; its right neighbor `(h+1,h+3)` is in
  the frame component M. Both are unpreserved, so their new edge closes a
  cycle. In coordinates these are `(7,8)` and `(7,9)`.
- For every s>=3, the retained terminal tail starts at `(h,s+7)`. v3's upper
  and right neighbors are the left and lower leaves of this center. Inserting
  v3 completes the unit square on rows `h,h+1`, columns `s+6,s+7`.
  Detaching that tail from the frame alone cannot remove this local square.
  The n=14 square has rows 9,10 and columns 9,10.

This refutes the exact next extension **with the remaining tail and frame
unchanged**. It does not refute a continuation deleting further tail centers.
Indeed that alternative leads to the following valid sweep.

## Whole-Rail Sweep

Define Kstar from F0 by removing e and **all** of `R_(s-1)`. Keep the frame
and every other source center. Add

```text
U     = {(h-1,s+4)};
Vstar = {(h+1,c): s+1 <= c <= h+1};
X_t   = {(h+2-(t mod 2),s-1-2t)},  t>=0, s-1-2t>=3.
```

There is no W. This specifies a set directly; it does not rely on an
unproved sequence of legal sliding moves. Geometrically the terminal
horizontal interval is lowered by one row, its right-frame attachment is
removed, and the preceding right rail is reattached through U,Vstar and the
last left rail. The old endpoint collision is paid for by actual deletions.

### Paper Forest Argument

Kstar has two nontrivial trees: M containing the frame and the other retained
rails, and the detached D tree. All remaining vertices are isolates. This is
a conclusion for Kstar using the source exact interval supports, not a
condition imposed on arbitrary feasible sets.

For any interior interval `(r,[a,b])`, its exact support has slices
`(r,[a-1,b+1])` and `(r+-1,[a,b])`. Applying this formula gives:

| New piece | Intersection with support(Kstar) | Intersection with other new pieces |
| --- | --- | --- |
| U | `(h-2,s+4)`, in D | Vstar only, at `(h,s+4)` |
| Vstar | `(h,s+1)`, in M | U only, at `(h,s+4)` |
| X_t, bottom row at c | `(h+3,c)`, in M | None |
| X_t, upper row at c | `(h,c)`, in M | None |

Here are the needed bounds, including the short s=2 case:

1. D's lower leaves occupy row h-2, columns `[s+2,h+1]`; `s+4<=h+1`
   for s>=2, so U's listed attachment exists after e is deleted. U's
   same-row support `[s+3,s+5]` misses the last left rail support ending
   at s+2. With the terminal rail removed, U has no other old intersection.
2. Vstar's support is row h+1 on `[s,h+2]` and rows h,h+2 on `[s+1,h+1]`.
   It stays before the right next ring h+3, above the bottom next ring h+3,
   and right of the left next ring. Its only old intersection is the last
   left rail's lower leaf `(h,s+1)`. Earlier right rails end vertically at
   row h-2. U reaches Vstar only by its lower leaf `(h,s+4)`.
3. Bottom X columns are at most s-1 and upper X columns at most s-3.
   Their support slices miss U and Vstar: in particular bottom same-row
   support ends at s, before Vstar's row-h+2 slice starting at s+1; upper
   same-row support ends at s-2, before its row-h+1 slice starting at s.
   Each upper X attaches to a lower leaf of the last left rail, and each
   bottom X to the bottom next ring. Alternating rows and column gaps two
   give pairwise Manhattan distances at least three, hence disjoint stars.

Glue U once to D. Vstar then meets **two different trees**, M and D union U,
once each, so it joins them without a cycle. This is not the false rule that
a new piece must have only one old attachment in total. Finally glue the
disjoint X stars at their respective single attachments. The resulting
support is a tree; all other ambient vertices remain isolates. Every forced
edge belongs to one of these pieces or Kstar. Adjacent unpreserved support
vertices do not contribute extra edges.

This is a uniform coordinate argument at paper level, not a deduction from
the two finite checks. It has not been formalized.

### Count Refutation

F0 has `3s^2` deep centers. The removed terminal rail has `2s` centers and e
costs one. U and Vstar contribute `1+(2s+1)`. The X count is
`q=floor((s-2)/2)`. The frame has `12s+11` centers. Thus

```text
J(s) = (3s^2-2s-1) + 1 + (2s+1) + q + (12s+11)
     = 3s^2+12s+11+floor(s/2).
```

This is exactly one below the single-repair score G(s), equal to the source
score for even s, and one below the source for odd s. The induced preserved
pieces remain separate: four boundary carriers, `2s-1` retained z/R/L
carriers, U, Vstar, and q X carriers. The paper ledger consequently gives

```text
r = 2s+5+q = 2s+4+floor(s/2);
b = 5;
c = 4s+3-4floor(s/2).
```

Under s -> s+2, r grows by five and c by four, giving cost nine rather than
six. The finite profiles are `(48,9,7,5)` at n=11 and `(75,11,11,5)` at
n=14. The gap from the target polynomial is
`T(s+1)-J(s)=ceil(s/2)-1`; in particular the odd seed already fails.
This valid endpoint transfer has no accumulating extra center.

## Restricted Search

For each s=2,3, define

```text
Q4 = [h-1,h+2] x [2,h+2];
fixed = source_staircase(s) minus Q4 minus {e};
variable = Q4.
```

The original frame is fixed. The preceding endpoint e lies **outside** Q4
and is forced absent. Every subset of Q4 is permitted, without interval,
rootedness, or connectivity constraints. This differs from both original
Q4 searches, whose outside right-rail geometry was not cut at e.

| n | Maximum f in this class | Visited nodes | Maximizer (f,r,c,b) |
| --- | --- | --- | --- |
| 11 | 48 | 4,312 | (48,10,6,5) |
| 14 | 76 | 162,162 | (76,14,5,5) |

The deterministic maximizing witnesses, relative to the source seeds, are:

```text
n=11 delete: (3,8), (6,5), (6,6), (6,8), (8,4)
     insert: (5,4), (5,7), (7,3), (7,7), (8,5)

n=14 delete: (6,11), (9,6), (9,7), (9,9), (9,10), (9,11), (11,5)
     insert: (8,5), (8,8), (8,11), (10,6), (10,10), (11,6), (11,10)
```

The reused `maximize` engine reconstructs all ambient components, uses the
exact insertion test, enumerates increasing-coordinate subsets, and prunes
only by remaining cardinality. Insertion illegality is monotone under adding
centers because an existing forced cycle cannot disappear. Thus its search
is exhaustive in this declared finite class, without a heuristic cutoff.
Reported maxima are ordinary Python results, not kernel-checked certificates.
They do not bound a larger board, alternate cuts, boundary edits, or a pump
whose interface does not occur on these two boards.

## Current Checkpoint

The separate formal milestone strictly compiled five new modules:
`CarrierLayers/OneExcessSeparated.lean`, `CarrierLayers/CoveredBoundary.lean`,
and `Constructions/ResidueTwo/RailRepair/{Geometry,Forest,Score}.lean`.
Root and Regression cover both upper fronts and the repaired lower theorem,
including the symbolic interval and lower regressions at sides 17, 20, 23, 29.
Full strict verification on Lean/mathlib 4.33.1 passed with 8,939 jobs,
exit 0, zero warnings/errors. All 147 public axiom audits (72+31+44, with
both previous groups rerun) use only subsets of `propext`, `Classical.choice`,
and `Quot.sound`, with no `sorryAx` or native proof axiom. This is not a
whole-library axiom audit or a formalization of the alternative in this note.

There are 232 modules / 83,811 lines under GridGraphs, plus the 177-line
root: 233 library files / 83,988 lines. The five new modules are below
1,000 lines; the 11 pre-existing oversized modules were untouched.
The new audit driver is `/tmp/opencode/U1U3L2RailRepairAudit.lean`; logs:

- `/tmp/opencode/u1-u3-l2-rail-repair-full-build.log`
- `/tmp/opencode/u1-u3-l2-rail-repair-previous72-axioms.log`
- `/tmp/opencode/u1-u3-l2-rail-repair-previous31-axioms.log`
- `/tmp/opencode/u1-u3-l2-rail-repair-new44-axioms.log`
- `/tmp/opencode/u1-u3-l2-rail-repair-source-lengths.log`

On the upper side, root-separated hole middles S now charge
`q+p+|S|+1<=r+c` without saturation. Intervening roots prevent shared inward
carriers; witnesses in a root-free gap may reuse a horizontal carrier.
For a missing side, k>=5 and p+|S|>=7 imply f<=T, but no sufficient S is
guaranteed. The earlier exact three-unit one-excess slack remains valid.
Actual pure boundary mass P gives `B<=P+2(r-p)` since a nonpure carrier has
at most two boundary contacts; for n>=7, `4n-4<=P+2b` and
`4n-4<=P+b+2(r-p)`. These charge the SAME resources, not independent budgets
to add. There is no new unconditional upper bound from either front.

The latest main-agent Python run passed all 13 tests (three terminal, three
propagating, seven layout), without searches:

```bash
env -u GRID_GRAPHS_SLOW -u GRID_GRAPHS_RUN_SLOW_TESTS python3 -m unittest \
  analysis.tests.searches.test_l2_rail_repair_research \
  analysis.tests.searches.test_l2_propagating_interface \
  analysis.tests.test_package_layout
```

These are recorded results, not reruns in this docs-only update. The earlier
research searches were only n=11/14; the formal build ran no search. See
[handoff](HANDOFF_U1_U3_L2.md) and [Lean EVIDENCE](../lean/EVIDENCE.md)
for verification commands and exact theorem scope.

## Historical Verification

The original research pass added only:

- `docs/L2_PROPAGATING_INTERFACE.md`
- `analysis/searches/l2_propagating_interface.py`
- `analysis/tests/searches/test_l2_propagating_interface.py`

Commands run from the repository root:

```bash
python3 -m analysis.searches.l2_propagating_interface
env -u GRID_GRAPHS_SLOW -u GRID_GRAPHS_RUN_SLOW_TESTS python3 -m unittest \
  analysis.tests.searches.test_l2_propagating_interface \
  analysis.tests.test_package_layout
```

The full experiment command passed after adding the sweep replay; an earlier
run had already checked the same two restricted searches and continuation.
All 10 tests passed: three new focused tests and seven existing layout tests.
Focused tests do not search. They check the successful component merger,
the exact blocked third extension, swept support intersections and attachment
identities, detached component sizes, full-vertex profiles, and size guards.
The reused insertion auditor independently rebuilds every forced edge and
compares the resulting connectivity relation with the incremental partition.
Constructors reject s outside {2,3} before graph construction. Importing the
new module runs neither experiments nor searches. No result files are written.

Both small seeds have an empty X pocket; no finite check covers nonempty X or
any six-width transition. Those support claims rest on the paper inequalities,
not finite validity extrapolated into a uniform theorem. In that original
pass, existing Lean source, the repair script/tests, handoff, and concurrent
worktree changes were untouched. The later Lean single-terminal proof does
not formalize the nonempty-pocket claims for this different propagating family.

The useful remaining interface question is narrower than "detach a rail":
can an attachment be transferred while **recovering the cut's lost center**
and preserving another independent attachment for the next six-width step?
Here the first join consumes the sole separation of M and D; further local
extension hits either a retained-tail square or the frame. Sweeping the tail
removes that geometric blockage but not its count cost. A future candidate
must change this exact geometry or recover the cost elsewhere; the present
results do not say that doing so is impossible. L2 remains open.
