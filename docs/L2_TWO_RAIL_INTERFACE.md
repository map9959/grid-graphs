# L2: Two-Rail Attachment Interface

Date: 2026-09-06. Ambient coordinates are zero-based, intervals inclusive.
Put `h=3s`, `n=3s+5`, `k=s+1`.

## Outcome

**No accumulating target pump is established.** This pass supplies:

- An explicit two-rootless-rail construction that retains one independent
  rail after the other is bridged to the frame. Its uniform paper invariant
  is valid but its count is insufficient.
- A local square obstruction to using that remaining independence by inserting
  directly between the intact rails. This obstruction survives arbitrary
  boundary changes retaining the two specified terminal centers.
- Four completed exhaustive endpoint/pocket searches at n=11/14, including
  alternate right-frame geometry. Their restricted maxima are 48/76.
- A follow-up jointly freeing the proposed notch and joining centers: six
  completed exhaustive searches, joined rootless outputs of sizes 47/75,
  and a count-neutral extension retaining independence. See Notch Follow-Up.

These results exclude the specified candidates, not two-rail pumps in general.
In particular the original endpoint search fixes the rail heads. A useful next geometry
must jointly change rail-head/notch occupancy and the attachment partition;
merely increasing the number of rootless components is not enough here.

Read alongside [the propagating interface](L2_PROPAGATING_INTERFACE.md) and
[terminal repair research](L2_RAIL_REPAIR_RESEARCH.md). Inspected formal sources:

| RailRepair module | Relevant facts |
| --- | --- |
| `Geometry.lean:16-39,91-138` | Actual shortened rail and U,V,W,X coordinates; disjoint new footprints and unique possible attachment locations |
| `Forest.lean:33-38,57-94` | Base acyclicity by deletion; arbitrary subsets of new pieces glue by singleton support intersections; full ambient forced acyclicity |
| `Score.lean:93-112,126-143` | Exact cardinality, uniform lower bound, explicit step `12s+37`, and k conversion |

Paths are under `lean/GridGraphs/Constructions/ResidueTwo/RailRepair/`.
The formal gluing proof is sufficient for its particular construction; its
singleton-intersection hypothesis is not a necessary condition for general
forest gluing. None of the new results below is Lean-formalized.

## Exact Interface

Let `H(F)` contain every grid edge with at least one endpoint in F, on all
`n^2` ambient vertices. For an absent center u, the insertion ports are

```text
{u} union (N(u) minus F).
```

Insertion is legal precisely when these vertices occupy distinct components
of H(F). The center must be retained in the test. Each isolate has its own
identity. A component without a frame vertex is allowed, and two or more
nontrivial components may be merged. Component sizes alone do not encode this
test. Deleting a center requires rebuilding the forced graph: edges incident
to its still-preserved neighbors survive.

For a fixed variable set Q, an exact finite state is the occupancy of the
fixed centers together with the component equivalence relation restricted to
`Q union N(Q)`. The inherited edges to preserved neighbors are already present;
all other insertion edges use these ports. Components not meeting the ports
cannot affect insertion legality, but must still be counted in c. For a moving
interface, occupancy and the incoming/outgoing port identification must also
be specified; a bare partition does not define a geometric transition.

The script keeps the full ambient partition throughout. Its reporting helper
returns actual blocks on named coordinates, independent of union-find root
names. It neither merges all rootless trees nor collapses isolates.

## Two Detached Rails

Let F0 be the source frame, z, and all R,L rails, without B,P, as defined in
the terminal repair note. Delete both centers

```text
eA = (h-3,h+2),   eD = (h,h+2).
A  = {(h-3,c): s+2 <= c <= h+1},
D  = {(h,c):   s+3 <= c <= h+1}.
```

For every s>=2, the resulting forced graph has three nontrivial trees:
the frame tree M with the other rails, A, and D. Their supports are disjoint;
all remaining vertices are separate isolates. For an interior interval of
length l the support has `3l+2` vertices. Consequently A has `6s+2` vertices
and D has `6s-1`. The deleted centers remain endpoint leaves of their rails,
but no longer force their rightward frame spokes. This uses the source's
disjoint interval footprints, not a global rootedness assumption.

Insert the explicit bottom bridge

```text
w = (h+2,h+1).
```

Its center/up/down/left/right ports have components
`singleton,D,M,singleton,singleton`, all distinct. It joins D to M and leaves
A untouched. The full-vertex component count decreases by four. Exact finite
replays, before restoring the old pocket:

| n | Port component sizes | Result (f,r,c,b) |
| --- | --- | --- |
| 11 | 1,11,82,1,1 | (46,9,13,5) |
| 14 | 1,17,141,1,1 | (73,11,17,5) |

After insertion, the actual partition on ports
`a=(h-3,h+1), d=(h,h+1), m=(h+3,h+1)` is
`{{a},{d,m}}`, not `{{a,d,m}}`. Thus a second independent rail really survives.
A second bottom bridge at `(h+2,s+3)` fails: its upper and lower neighbors
are now in the same merged tree. This does not consume or exploit A.

Restore all original B,P pocket stars. They retain their source single
attachments, are disjoint from A, and miss w's star. The closest possible
bottom pocket column is s+2, at distance `2s-1>=3` from w; upper pocket
columns are at most s, giving still larger Manhattan distance. Thus the
following is an explicit uniform paper forest construction:

```text
C(s) = source_staircase(s) minus {eA,eD} union {w},  s>=2.
```

Its nontrivial components remain A and the enlarged frame tree, plus ambient
isolates. This invariant follows from the exact support intersections above,
not extrapolation from the two tests. Its cardinality is

```text
|C(s)| = 3s^2+12s+10+ceil(s/2) = source_score(s)-1,
|C(s+2)|-|C(s)| = 12s+37 = 12k+25.
```

The tested profiles after pocket restoration are `(47,10,9,5)` at n=11 and
`(75,13,9,5)` at n=14. Keeping an unused rootless rail costs a center and
does not recover the missing unit of recurring gain. This count identity
is not a six-width geometric transition or a target-pump claim.

## Local Obstruction

Before or after the bottom bridge, consider

```text
u = (h-1,c),  s+4 <= c <= h.
```

Its upper neighbor belongs to A, whereas u is already an upper leaf of D.
These components are genuinely different before any attempted merger with A.
Nevertheless insertion is illegal. Both `(h,c)` and `(h,c-1)` are retained
terminal centers, giving the old path

```text
u -- (h,c) -- (h,c-1) -- (h-1,c-1).
```

Both endpoints are unpreserved. Inserting u adds the missing fourth edge of
this unit square. Equivalently, u and its unpreserved left neighbor have the
same insertion-component identity. The right-hand square gives a symmetric
obstruction while `(h,c+1)` is retained. The column range is nonempty even
at s=2. Tests replay every column in this range for s=2,3.

This is a uniform local obstruction for these retained centers, regardless
of frame shape or remote root partitions. It is **not** a no-go for a notched,
translated, or removed terminal rail. To keep `(h,c)` while inserting u,
both neighboring terminal centers `(h,c-1)` and `(h,c+1)` must be removed
to eliminate these two squares. Alternatively remove `(h,c)` itself; that
removes these squares but does not establish legality, since other attachment
collisions may remain. Any such deletions need a count and connectivity ledger.

## Alternate Frame Search

The variable set is precisely

```text
Q = ([h-3,h+2] x [h+2,h+4])
    union ({h+1,h+2} x [2,h+2]).
fixed = source_staircase(s) minus Q.
```

Every subset of Q is allowed. This jointly frees both right-rail endpoints,
the next-ring column h+3, six right-boundary centers, and the complete bottom
two-row deep pocket. Contiguous boundary cuts and next-ring insertions are
allowed; neither b=5 nor a connected frame is required. The bottom outer
boundary, the remaining side boundary, and the inner rail heads are fixed.

The control fixes the six boundary centers in their source occupancy and
frees the rest of Q. This class is different from, **not a superset of**, the
previous Q4 searches: it adds endpoint/side freedom but fixes the rail heads
and most of rows h-1,h. Hence 48 at n=11 is consistent with the known 49-center
single repair, which deletes centers outside this Q.

| n | Frame mode | Free vertices | Maximum f | Search nodes | Maximizer (f,r,c,b) |
| --- | --- | --- | --- | --- | --- |
| 11 | Fixed | 24 | 48 | 18 | (48,9,7,5) |
| 11 | Free in Q | 30 | 48 | 843 | (48,9,7,5) |
| 14 | Fixed | 30 | 76 | 47 | (76,12,7,5) |
| 14 | Free in Q | 36 | 76 | 2700 | (76,12,7,5) |

The deterministic maximizers in both modes are the n=11 source with
`(8,4)` deleted and `(7,3)` inserted, and the unchanged n=14 source.
Their b=5 is an output property, not a free-frame search restriction.

The reused exact engine enumerates subsets in increasing coordinate order,
prunes by remaining cardinality, and rejects insertions by actual component
identity. A forced cycle cannot disappear on adding centers, so legality
pruning is safe. There is no heuristic or time cutoff. These are completed
finite restricted maxima, not global optima, formal certificates, or bounds
on larger sides. In particular equality of the control and free-frame maxima
does not show that alternate boundaries are uniformly unhelpful.

## Next Geometry

The useful next experiment is a **joint rail-head/notch and side-boundary
window**, not another endpoint-only cut. Retain two named independent rail
ports, but stagger the ends so a joining center does not have two adjacent
terminal centers forming the squares above. In coordinates the first new
freedom to include is `(h,s+3..s+5)` together with `(h-1,s+4)` and the lower
row extension near `(h+1,s+4)`. These are exactly outside or mostly outside
the endpoint window, and involve the U-to-V attachment collision in the
earlier work. This was the first pass's proposed domain. The follow-up below
now tests these extra freedoms, without establishing a uniform motif.

A credible accumulating invariant must specify which output rail remains
independent after that join and how the next six-width cell recreates the
same port occupancy/partition. It must pay for notches and boundary cuts,
not only exhibit distinct root labels before one insertion. More generally
multiple tree pieces can be glued when their actual attachment incidence
graph is acyclic; two attachments to the same old tree can instead close a
cycle. Repeated attachment coordinates and shared pre-existing edges require
explicit accounting, not a naive count of roots touched.

With `3f+r+c+b=n^2+4n`, target gain `12k+26=12s+38` requires
`Delta(r+c+b)=6`; the current uniform repair has cost nine. Boundary changes
must retain Delta b in this equation. This is only a necessary ledger check.
Both parity branches need actual geometric closure and valid seeds. Small
scores, including the n=11 repair's surplus over T(3), cannot certify that
surplus recurs. No n=17/20 board or six-width transition was constructed here.

## Verification

Added only this document, `analysis/searches/l2_two_rail_interface.py`, and
`analysis/tests/searches/test_l2_two_rail_interface.py`. Existing files and
concurrent worktree changes were not edited. No Lean build was run.

Executed from the repository root:

```bash
python3 -m analysis.searches.l2_two_rail_interface
env -u GRID_GRAPHS_SLOW -u GRID_GRAPHS_RUN_SLOW_TESTS python3 -m unittest \
  analysis.tests.searches.test_l2_two_rail_interface \
  analysis.tests.searches.test_l2_rail_repair_research \
  analysis.tests.searches.test_l2_propagating_interface \
  analysis.tests.test_package_layout
```

In the first pass all four searches completed; all 17 tests passed.
The four new tests perform no optimization: they check window membership,
size rejection, independent rootless rail ports, distinct isolate ports,
insertion connectivity against a rebuilt full forced graph, pocket restoration,
the local squares, and maximizing witness profiles. Importing the module runs
no experiment; its constructors reject s outside {2,3}. Only boards 11 and 14
were materialized, and no result files or external dependencies were added.

## Notch Follow-Up

Only the same three owned files were extended. Define precisely

```text
Qplus = Q union {(h,s+3), (h,s+4), (h,s+5),
                (h-1,s+4), (h+1,s+4)}.
fixed = source_staircase(s) minus Qplus.
a = (h-3,s+2), u = (h-1,s+4), e = (h+1,s+4).
```

The lower extension e already belongs to Q, so Qplus has 34 vertices at
n=11 and 40 at n=14. All previous side-boundary and next-ring freedoms are
retained. No other centers may change. Three modes were searched:

- **Unrestricted:** only forced acyclicity is required.
- **Rootless:** the component of a contains no ambient boundary vertex,
  whether preserved or unpreserved. The fixed preceding rail contains a,
  so this is a nontrivial tree, not an isolate.
- **Joined-rootless:** the rootless condition plus mandatory preserved u,e.
  Their stars meet at `(h,s+4)`; u meets the preceding rail at
  `(h-2,s+4)`. Thus a,u,e are in the same rootless component.

The output condition is stronger than separation from one chosen frame root.
It allows the frame to split but disallows calling a boundary-attached
fragment rootless. It is narrower than every useful possible invariant:
future candidates could use another rail or independent boundary attachments.

### Exhaustive Results

Each search had a hard budget of 100,000 visited recursive nodes. **All six
finished exhaustively before that budget.** These are actual maxima within
their respective finite restrictions, not merely lower bounds.

| n | Mode | Nodes | Maximum f | First maximizer (f,r,c,b) |
| --- | --- | --- | --- | --- |
| 11 | Unrestricted | 10,178 | 49 | (49,11,2,5) |
| 11 | Rootless | 9,177 | 48 | (48,12,3,6) |
| 11 | Joined-rootless | 782 | 47 | (47,11,7,6) |
| 14 | Unrestricted | 29,438 | 76 | (76,14,5,5) |
| 14 | Rootless | 27,067 | 75 | (75,15,6,6) |
| 14 | Joined-rootless | 1,261 | 75 | (75,14,7,6) |

The search uses increasing-coordinate subset enumeration and the exact
insertion criterion. Rootless failure is monotone under adding centers:
a connection to a boundary vertex cannot be undone. Thus this additional
pruning is sound. Every accepted partial set already satisfies the required
occupancy and rootless predicate and is a valid incumbent. Cardinality
pruning compares only against such incumbents. Stopping before an unexplored
subtree because of the budget sets `exhaustive=False`; the returned score
is then only a feasible lower bound. A one-node regression tests this status.

The first unrestricted maximizers are the known n=11 terminal repair and,
at n=14, the source with `(9,6..8),(11,5)` deleted and
`(8,7),(10,5),(10,6),(11,8)` inserted. The first rootless maximizers are
exactly those sets with the extra boundary deletion `(h-3,h+4)`. They keep
u rootless but **not e**: the existing vertex e belongs to the frame tree.
Their larger counts therefore do not answer the joined-output question.

### First Joined Witness

The first maximizing joined-rootless witnesses have these exact edits:

```text
n=11 delete: (3,10), (6,5), (6,6), (6,7), (8,4)
     insert: (5,6), (7,4), (7,5), (7,6)

n=14 delete: (6,13), (9,6), (9,7), (9,8), (10,3), (11,5)
     insert: (8,7), (10,5), (10,6), (10,7), (11,3)
```

The preceding rail endpoint is retained. Instead its boundary spoke is
removed by deleting `(h-3,h+4)`. That deleted boundary vertex still belongs
to the frame through its preserved vertical neighbors; the next-ring leaf
`(h-3,h+3)` belongs to the detached rail. This is a real edge deletion,
not a reassignment of a root label. These witnesses have b=6, not b=5.

Let `d=(h,h+1)` and `m=(h+3,h+1)`. Actual output partitions are

```text
n=11: {{(3,4),(5,6),(7,6)}, {(6,7),(9,7)}}
n=14: {{(6,5),(8,7),(10,7)}, {(9,10),(12,10)}}
       {       a, u, e     }  {     d, m       }
```

The first block belongs to a nontrivial component with no boundary vertex.
Its full size is 31 at n=11 and 37 at n=14. The second block belongs to the
frame component. At n=11, d is **not** a preserved terminal center: it is
the left leaf of `(6,8)`. Actual connectivity, not port occupancy, determines
its block.

This is a successful finite improvement in output geometry: unlike C(s),
the independent component now reaches the lower extension e. It is **not a
score improvement** over C(s), whose finite sizes are also 47/75. Relative
to the best rootless-only result in Qplus, demanding the join costs one
center at n=11 and zero at n=14. These are not six-width comparisons.

### First Refuted Extension

Attempt `v=(h+1,s+5)` in the joined witness. Its preserved left neighbor e
is omitted from the insertion test. The exact port partitions are

```text
n=11 v=(7,7):  {{(6,7),(7,8)}, {(7,7)}, {(8,7)}}
n=14 v=(10,8): {{(9,8),(10,9)}, {(10,8)}, {(11,8)}}.
```

Singleton blocks here mean singleton **blocks on the listed ports**, not
necessarily singleton ambient components: v is already an endpoint leaf of
the rootless output. Its upper and right neighbors are the left and lower
leaves of the frame-attached terminal center `(h,s+6)`. Inserting v closes
the square on rows h,h+1 and columns s+5,s+6. The first unchanged continuation
is therefore refuted at both seeds, despite the independent output.

### Paid Extension

Delete `(h,s+6)` before adding v. Both insertions are then legal, with
center/up/down/right component sizes `[31,1,1,1]` and `[37,1,1,1]`. All four
identities are distinct; the three new ports are separate ambient isolates.
The extended tree remains disjoint from **every** ambient boundary vertex.
Its size grows to 34/40, while f stays 47/75 because one deleted center pays
for one inserted center. Profiles are `(47,10,8,6)` and `(75,14,7,6)`.

This is a concrete successful continuation retaining an independent output,
not merely a high score. At n=11 the deletion is already in Qplus; at n=14
`(9,9)` lies outside Qplus. The n=14 replay is a separate explicit surgery,
**not** a witness in the table's class or a search over an enlarged window.

The following center `t=(h+1,s+6)` then behaves differently:

- At n=11, t=(7,8) is legal, but its right neighbor `(7,9)` is in the frame.
  Its four insertion ports are distinct, so it merges the rootless output
  into the frame. It fails the output invariant, not acyclicity. The
  regression checks this actual merger.
- At n=14, t=(10,9) is illegal: `(9,9)` and `(10,10)` are the left and lower
  leaves of the retained center `(9,10)`. The next unit square remains.

Thus the paid continuation advances the independent attachment one column
without count gain. The next unchanged step either consumes that independence
or hits the next tail square. No repeated accumulation or uniform closure
follows from these two finite patterns.

### Next Restriction

The remaining bottleneck is explicit: one-for-one tail deletion advances
the rootless lower interval without recovering a center, and the interval
ultimately faces the right next-ring frame contact. A useful next domain
would jointly free the remaining tail beginning at `(h,s+6)` and the right
endpoint continuation at `(h+1,h+2..h+4)`, while requiring an independent
output after the last join. Most of the right contact is already free in
Qplus; the retained inner tail is not. Boundary relocation must actually
remove the output's frame contact and account for Delta b.

Alternatively change the left end of the lower interval: its start at
s+2 avoids the last left rail's frame leaf at `(h,s+1)`. Recovering that
one-column separation without merging the output would require changing
the last left rail's attachment, outside this window. Neither suggestion
is a verified gain mechanism. The exact restrictions and tested failures
above are the result, not a general two-rail no-go theorem.

### Follow-Up Verification

Executed the full module and the focused `notch_experiments()` entry point.
The same four-module unittest command above now passes **19 tests**. The
two new tests replay maximizing joined witnesses against rebuilt full forced
connectivity, check rootless component sizes, exact output partitions and
the paid continuation, and test budget-status and size guards. The only
search in these tests is a deliberately one-node run. No graph construction
above n=14, no Lean build, and no edits outside the three owned paths occurred.
