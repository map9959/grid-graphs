# Distributed Lower Repair

Date: 2026-09-07. Paper proofs and strictly bounded Python checks.

## Outcome

**No universal `F >= T-C` candidate was obtained.** This pass gives a
precisely scoped failure of a distributed, count-balanced endpoint-shift
family. It is not another optimization of a fixed cap. Every paired left/right
rod may exchange length along the entire staircase, preserving both total
center count and total GOOD FF count. Descending seams expose genuinely
isolated potential star centers. Nevertheless every such promotion has two
actual attachment vertices in the same old tree, so it is illegal.

The missing connection is through **four rods**, rather than just the two
nearest rods bounding the empty row. Explicit coordinates and the complete
five-port partition are below. With arbitrary bottom-pocket repacking as well,
the specified family has exactly the old staircase maximum, not the repaired
score and not the target six-width gain. Boundary attachment changes, different
rod rows, and more general distributed exchanges are outside this conclusion.

No requirement `c=1`, `b=5`, or rootless output is imposed on the unrestricted
problem. The fixed five-hole frame is a restriction of this failed candidate.

## Input Audit

Read `PAPER_CONSTANT_GAP_LOWER.md`, `PAPER_MOVING_PHASE_CAP.md`, all five
`L2_*` notes, and the relevant GOOD-edge definitions and packing ledger.
Read the actual formal modules under
`lean/GridGraphs/Constructions/ResidueTwo/RailRepair/`:

- `Geometry.lean:16-39`: shortened last right rod and U,V,W,X coordinates.
- `Geometry.lean:91-138`: disjoint new footprints and possible attachments.
- `Forest.lean:33-38,57-94`: deletion and singleton-support gluing proofs.
- `Score.lean:93-112,126-143`: score, forest lower bound, and insufficient step.

Use zero-based `(row,column)` coordinates, inclusive intervals, and

```text
s = k-1 >= 2, h = 3s, n = h+5 = 3k+2,
T(k) = 3k^2+7k = 3s^2+13s+10.
```

`H(F)` has every ambient vertex, including isolates, and every grid edge
with at least one endpoint in F. Only its acyclicity is required. A legal
insertion at absent v tests pairwise distinct component identities on
`{v} union (N(v) minus F)`, including v itself.

The existing RailRepair score is

```text
L(k) = T(k)-floor(k/2)+2,
L(k+2)-L(k) = 12k+25,
T(k+2)-T(k) = 12k+26.
```

Here is a direct symbolic audit of the existing family's GOOD ledger. Before
the terminal repair, z and all R,L rods have `3s^2` centers in `2s`
nonempty horizontal pieces, hence `3s^2-2s` FF edges. Shortening the last
rod by three loses three FF edges, including when its remainder is a
singleton. U,W,X are singletons; V contributes two FF edges. Thus RailRepair
has `GOOD=3s^2-2s-1`. All these edges are good: neither extreme deep row
contains a horizontal FF edge, and no deep FF edge is vertical. Since
`Q(N-1)=3s^2`,

```text
Lambda = 2s+1 = 2k-1,
c = 4floor(k/2)-2,
4(L-T)+c+Lambda = 2k+5.
```

These are paper counts from the formal coordinates, not new Lean theorems.
For the same boundary geometry and only good deep FF edges, a net gain g
and GOOD loss ell obey `Delta c = -4g-ell`. In particular, if ell=g,
the old component reserve permits only `5g <= c_old-1`; this cannot fund
`g=floor(k/2)-O(1)` from `c_old=4floor(k/2)-2`. Boundary changes require
their own ledger; this calculation is not a restriction on them.

## Balanced Seam Coordinates

Take the original boundary frame M_F, the perimeter minus

```text
{(0,1),(0,2),(1,h+4),(h+4,h+3),(h+3,0)}.
```

Choose integers `a_0,...,a_(s-1)` satisfying

```text
a_0 = 2,
2 <= a_j <= h,
a_(j+1) <= a_j+1.
```

Define two rods per pair, with **no original pocket or terminal repair**:

```text
E_j = {3j+2} x [2,a_j],
D_j = {3j+3} x [a_j+2,h+2],       0 <= j <= s-1,
B(a) = M_F union all E_j union all D_j.
```

The original staircase without its pocket is `a_j=j+2`. The first E rod
is z. Changing any a_j increases one rod's length and decreases the other's
by the same amount. Unlike an individual rigid-rod translation, this allows
arbitrarily large head shifts and a linear number of distributed changes.

For each pair, lengths sum to h and FF edges sum to h-2. There are no
FF edges between different rods. All deep FF edges are GOOD, because E_0
is a singleton and every other rod row is strictly between the extreme
deep rows. Consequently, for every allowed phase sequence,

```text
|B(a)| = 3s^2+12s+11,
GOOD(B(a)) = 3s^2-2s,
Lambda(B(a)) = 2s.
```

This preserves GOOD exactly relative to the unmodified staircase and has
one more GOOD edge than RailRepair. It does not merely preserve bulk density.

### Forest Invariant

The support of an interior horizontal interval `(r,[u,v])` is exactly
`(r,[u-1,v+1]) union ({r-1,r+1} x [u,v])`, a tree.

All rod supports are pairwise disjoint. Same-family row distances are at
least three. Within pair j the minimum center distance is three, from the
one-row difference and two-column gap. The only other cross-family case
with row distance below three is D_j against E_(j+1). Its row distance is
two, and `a_(j+1)<=a_j+1` gives column distance at least one. Every other
cross-family row distance is at least four. Thus all distinct rod centers
in different pieces have distance at least three, which makes their closed
radius-one supports disjoint.

Each E_j meets the frame support once at `(3j+2,1)`; each D_j meets it
once at `(3j+3,h+3)`. The exceptional upper leaf `(1,2)` of E_0 is absent
from the frame support. Also `a_j<=j+2<=s+1`, so E rods do not reach the
right frame. The frame is a tree on its support. Gluing every rod once to
it proves that `H(B(a))` has one nontrivial tree M and individual ambient
isolates elsewhere. Connectivity to M is a proved geometric fact here.

The phase inequality has actual content: if instead
`a_(j+1)>=a_j+2`, D_j and E_(j+1) have overlapping column intervals. They
share a middle-row leaf and each attaches to the frame. Those three trees
already form a cycle. Thus such a rise cannot be admitted while keeping
these rods and frame unchanged.

## Four-Rod Collision

For a descending seam with `a_j-a_(j+1)>=2`, consider every center

```text
v = (3j+4,c),  a_(j+1)+2 <= c <= a_j,  0 <= j <= s-2.
```

Its row lies between D_j and E_(j+1). Their nearest centers have distance
at least three from v. Therefore those two pieces alone seem to leave room
for its star. In the complete geometry, however, the other two rods supply

```text
u = (3j+3,c), a lower leaf of E_j at row 3j+2,
w = (3j+5,c), an upper leaf of D_(j+1) at row 3j+6.
```

Both coordinates exist and are distinct. Both are unpreserved and lie in
M. Meanwhile v and its left/right neighbors are three distinct ambient
isolates. Indeed the old support on row `3j+4`, away from the frame,
occupies columns at most a_(j+1) or at least a_j+2. The candidate and its
horizontal neighbors lie strictly between these ranges. Their columns are
also away from the frame; `c>=4` and `c<=s+1` suffice.

Thus v is genuinely isolated before insertion, and its **exact** insertion
partition is

```text
{{u,w}, {v}, {(3j+4,c-1)}, {(3j+4,c+1)}}.
```

The first block is the restriction of M to the ports. The other three
blocks are different singleton ambient components, not a common unattached
label. All four neighbors are absent centers, so none is omitted as an
already forced edge. The new path `u--v--w` closes the existing M path
between u and w. Therefore **every one of these exposed centers is illegal**.
Adding several at once cannot help: any such superset retains this cycle.

This is not the repeated terminal U-to-V obstruction, nor an FF-count
deficit: the distributed shift has preserved FF exactly and exposed actual
isolates, but failed to separate their attachment components.

## Exact Restricted Score

For clarity, the failed family allows all phase sequences above, any subset
of the displayed descending-seam centers, and arbitrary occupancy in the
bottom deep pocket `{h+1,h+2} x [2,h+2]`. Everything else is B(a).
It does not allow other interior additions or boundary deletions.

No descending-seam center can occur in a feasible member. Write
`A=a_(s-1)`. The bottom support slices are the fixed-pocket note's slices
with last-left endpoint A and last-right starting column A+2. The only
individually legal pocket centers are

```text
(h+1,c), 3 <= c <= A,
(h+2,c), 3 <= c <= A+1.
```

Each has exactly one old attachment, respectively `(h,c)` or `(h+3,c)`;
its other four star vertices are isolates. Outside these ranges the same
two-frame-attachment or adjacent-rod square obstruction applies. The last
right rod has length at least `h+1-(s+1)=2s`, so its square argument has
no short-rod exception.

Within one pocket row, column gaps must be at least three; between rows,
at least two. Otherwise the two stars connect their distinct M attachments,
or force a unit square. These inequalities are also sufficient: star
supports are then disjoint and each glues once to M. Selected columns lie
in `[3,A+1]` with successive gaps at least two, giving at most `floor(A/2)`
centers. This is attained by columns `A+1,A-1,A-3,...>=3`, alternating
bottom and upper rows. Since `A<=s+1`, the exact maximum over this family is

```text
3s^2+12s+11+floor((s+1)/2),
six-width gain = 12s+37 = 12k+25.
```

The original increasing phase attains it. Thus distributed count-balanced
seam shifts plus all the proposed exposed stars and arbitrary pocket
repacking do not improve even the source score. This is a uniform proof
for this declared class, not a global optimality statement.

## Bounded Verification

New module: `analysis/searches/distributed_lower_repair.py`; mirrored tests:
`analysis/tests/searches/test_distributed_lower_repair.py`. Existing graph
reconstruction and exact insertion helpers are imported read-only. No
existing unbounded optimizer is called; imports run no experiment.

Phase enumeration counts every visited prefix as a node and stops before
exceeding its explicit cap. Caps outside `[1,1000]` are rejected. A cutoff
returns `exhaustive=False`; completed-layout counts then are not maxima.
Constructors reject s outside `{2,3}` before materialization.

| s | n | Node Cap | Nodes | Complete Layouts | Exhaustive | Exposed Candidates |
| --- | --- | --- | --- | --- | --- | --- |
| 2 | 11 | 1000 | 3 | 2 | Yes | 0 |
| 3 | 14 | 1000 | 8 | 5 | Yes | 0 |

Each completed layout checks its full forced forest, center count and FF
count. These small boards have no descending gap of width sufficient to
expose a candidate. They therefore do **not** test the nonempty uniform
collision, and are not evidence for a six-width transition.

A separate four-rod motif on n=11 tests the collision without pretending
to be a whole-family seed. Keep the same frame and take only rods

```text
row 3: [2,5], row 4: [7,8], row 6: [2,2], row 7: [4,8].
```

The full graph is a forest with `(f,r,c,b)=(47,8,11,5)`. At v=(5,4),
the independently reconstructed actual port partition is

```text
{{(4,4),(6,4)}, {(5,3)}, {(5,4)}, {(5,5)}}.
```

The center's ambient component has size one, and insertion is rejected.
The motif is one fixed replay, not an optimization. Tests additionally
check the one-node cutoff (`nodes=1`, zero complete layouts, nonexhaustive),
size rejection, phase rejection, and cap rejection.

Commands run from the repository root:

```bash
python3 -B -m analysis.searches.distributed_lower_repair
python3 -B -m unittest analysis.tests.searches.test_distributed_lower_repair analysis.tests.test_package_layout
```

Both passed; the test command ran 10 tests. Only sides 11 and 14 were
materialized. No Lean build, large search, external solver, or stored
result file was used. Only the three new owned files were added; unrelated
worktree changes were left untouched.

## Remaining Gap

The exact failed interface identifies what must change: separate the old
components containing the E_j lower leaf and D_(j+1) upper leaf, while
recovering the cost of that separation and preventing later promotions
from reconnecting the same pair. Merely exposing the isolated center, or
conserving FF under endpoint motion, is insufficient.

This pass supplies no count-balanced boundary redesign with `b=Theta(k)`,
and no changed moving-phase interior with separately closable port blocks.
Permuting the old moving-phase contact matching against one cap tree still
leaves rank k+1; the preceding cap note's two-row replacement bound also
remains applicable only to its fixed lower geometry. Neither result excludes
changing the contact set, number of interior components, and boundary jointly.

The universal constant-gap lower bound and an actual all-k gain `12k+26`
remain unresolved. The deliverable here is the coordinate-level, FF-balanced
distributed-seam failure and its exact attachment invariant, not a successful
candidate inferred from small seed scores.
