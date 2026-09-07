# Paper Constant-Gap Lower Research

Date: 2026-09-07. Paper research only; no new formal theorem or experiment.

## Outcome

No construction with lower bound `T(k)-O(1)` is established here. The new
result is instead an **exact optimization theorem for a distinct coordinate
class**: concentric square frames at spacing three, with arbitrary deletions
on every frame. Alternating the orientation of the cuts is allowed. Its
optimal six-width gain is `12k+23`, not `12k+26`. A bounded total number of
off-frame additions cannot repair its linear deficit.

The obstruction is not a repeated rail-end collision or a rootless-output
requirement. Every large square frame independently needs four corner repairs
and one further deletion to break its perimeter cycle. Explicit five-hole
coordinates attain that cost, and their full forced supports are disjoint
between layers. Thus both the upper obstruction within this class and the
matching forest construction have paper proofs.

The continuation below gives a genuinely different moving-phase strip with
explicit six-row cells. Its interior is a forest and its count has the target
gain, but its specified cap fails by an exactly computed attachment cycle
rank. This is a concrete open strip, not a constant-gap lower construction.
No global impossibility follows from either calculation.

## Baseline And Scope

Use zero-based coordinates on `V_n={0,...,n-1}^2`. For centers `F`, let
`H(F)` have all ambient vertices and exactly the grid edges with at least
one endpoint in `F`. Feasibility means that `H(F)` is a forest. Write

```text
n = 3k+2,
T(k) = 3k^2+7k,
L(k) = 3k^2+6k+3+floor((k-1)/2)
     = T(k)-floor(k/2)+2.
```

The source theorem `RailRepair.residueTwo_le_maxPreserved` supplies `L`
for `k>=3`. Its coordinates and proof were read in:

- `lean/GridGraphs/Constructions/ResidueTwo/RailRepair/Geometry.lean:16-39,91-138`.
- `lean/GridGraphs/Constructions/ResidueTwo/RailRepair/Forest.lean:33-38,57-94`.
- `lean/GridGraphs/Constructions/ResidueTwo/RailRepair/Score.lean:93-112,126-143`.

In particular `score_step_two` states the insufficient gain, rather than
leaving it as a conjectural interpretation of the geometry. The companion
notes read were [terminal repair](L2_RAIL_REPAIR_RESEARCH.md),
[terminal tail](L2_TERMINAL_TAIL_INTERFACE.md),
[two rail](L2_TWO_RAIL_INTERFACE.md), and
[propagating interface](L2_PROPAGATING_INTERFACE.md).

The source/polynomial seed scores 48/76 must not be conflated with the early
optimized 49/77 witnesses mentioned in the research brief. No seed search or
witness replay was executed here, and no claim of optimality is made for
either pair. Neither comparison crosses a six-width step.

The exact forest ledger, with its existing meanings of `r,c,b`, is

```text
3f+r+c+b = n^2+4n.
f = T(k)-C  implies  r+c+b = 3k+12+3C.
T(k+2)-T(k) = 12k+26.
L(k+2)-L(k) = 12k+25.
```

A target-count step therefore requires defect increase six. A single
count-neutral endpoint transfer is not such a step. We impose no fixed
component count, boundary deficiency, frame connectedness, or rootless
output on the unrestricted lower problem. Upper-bound improvements,
including an audited paper half-bound, supply no lower witness automatically.

## Nested-Frame Class

For `a=3j`, put `d=n-1-a` and define the square perimeter

```text
Q_j = ({a,d} x [a,d]) union ([a,d] x {a,d}),
ell_j = n-6j,
R_n = union Q_j over j>=0 with ell_j>=2.
```

The class in the theorem is **all** subsets `F` of `R_n` whose full ambient
forced graph is acyclic. It does not prescribe which centers are deleted,
how many components remain, or which way a frame is opened. The spacing is
fixed at three; relocated, staggered, or thick frames are outside the class.

Centers on different `Q_j` have Manhattan distance at least three. Their
closed radius-one neighborhoods are consequently disjoint. Since every
forced edge belongs to the star of a center, forced supports on different
frames are disjoint too. Ambient edges between unpreserved vertices are not
forced. Hence feasibility and center count separate by frame, with all unused
ambient vertices retained as individual isolates.

This is a whole-component invariant, not an identification of all unattached
pieces with a common root: each frame support remains its own component in
the construction below, independently of every other frame.

## Five-Deletions Lemma

**Working paper lemma.** On a square perimeter of side `ell>=5`, the maximum
number of retained perimeter centers inducing an ambient forced forest is
`4ell-9`. The square may be the outer boundary or embedded in a larger board.

Translate its coordinates to `[0,ell-1]^2`. At the top-left corner consider
the unit square with vertices

```text
(0,0), (0,1), (1,0), (1,1).
```

The first three belong to the perimeter. If all three are centers, its four
edges are forced, a cycle. Deleting just `(0,0)` does not help: the other two
are opposite vertices and still force all four edges. Thus if exactly one of
these three perimeter vertices is deleted, it must be an arm neighbor,
`(0,1)` or `(1,0)`. Apply the same argument at all four corners.

For `ell>=5` the four corner triples are disjoint, so at least four perimeter
centers must be deleted. Suppose exactly four are deleted. There must be
exactly one arm-neighbor deletion at each corner. No two of these deletions
are adjacent along the perimeter: even on a side of length five the nearest
choices are at positions one and three. Every perimeter edge therefore has
a retained endpoint. The entire perimeter cycle is still forced.

This proves that at least **five**, not just four, deletions are necessary.
The argument is local to edges on or inside the square and cannot be
invalidated by cuts, root labels, or added centers elsewhere.

For sufficiency, delete exactly

```text
D_ell = {(0,1), (0,2), (1,ell-1),
         (ell-1,ell-2), (ell-2,0)}.
```

Exactly one perimeter edge is now unforced, the edge between `(0,1)` and
`(0,2)`. All other perimeter edges remain, so they form a spanning path on
the perimeter vertices. Edges pointing inward are pendant edges except for
the possible shared inward neighbor at each corner. Each such neighbor has
at most one retained perimeter neighbor because of the specified deletions.
For `ell>=5` these are the only possible coincidences of inward neighbors.
Thus all actual inward edges are pendant edges. If the square is embedded,
outward edges also end at distinct pendant vertices. At a corner the two
outward neighbors are distinct as well.

The complete forced support is therefore a tree: a perimeter path with
pendant vertices attached. Vertices outside this support are isolates. This
proves feasibility with `4ell-4-5=4ell-9` centers, attaining the upper bound.
Rotating or reflecting `D_ell` does not change the proof.

For the exceptional innermost square of side two, the maximum is two
adjacent centers. Three centers force its four-cycle; two opposite centers
do too. Two adjacent centers force a three-edge path on the square, with
any exterior edges pendant. Its maximum is thus exactly two.

## Exact Score

For every layer of side at least five take

```text
F_j = Q_j minus ((3j,3j) + rho_j(D_ell_j)),
```

where `rho_j` is any chosen square symmetry in local coordinates. For example,
alternate the identity and a quarter-turn. For an innermost side-two layer
with `a=3j`, take `{(a,a),(a,a+1)}`. Let `F` be their union.

The five-deletions lemma and disjoint-support invariant prove both its
acyclicity and its optimality among **all** feasible subsets of `R_n`.
Let this class maximum be `M(n)`.

For `k=2m`, so `n=6m+2`, there are `m` large frames of sides
`8,14,...,6m+2` and one side-two square. Therefore

```text
M(6m+2) = 2 + sum_{t=1}^m (4(6t+2)-9)
         = 12m^2+11m+2,
T(2m)-M(6m+2) = 3m-2.
```

For `k=2m+1`, so `n=6m+5`, all `m+1` frames have sides at least five:

```text
M(6m+5) = sum_{t=0}^m (4(6t+5)-9)
         = 12m^2+23m+11,
T(2m+1)-M(6m+5) = 3m-1.
```

Small negative values of these differences do not affect the asymptotic
claim; `T` is the research target polynomial, not an assumed universal upper
bound at small `k`. In both parity branches the exact symbolic difference is

```text
M(3(k+2)+2)-M(3k+2) = 12k+23.
```

Each added outer frame has side `n+6`; its optimum contributes
`4(n+6)-9=4n+15`, while the target step is `4n+18`. The recurring shortfall
is **three centers per new frame**. Alternating cuts changes neither the
four independent corner constraints nor the surviving perimeter-cycle
constraint. This architecture is weaker even than the existing rail repair.

**Bounded-addition extension.** Suppose a feasible set is allowed arbitrary
deletions from `R_n` and at most `A` centers outside `R_n`, where `A` is
independent of `n`. Its restriction to `R_n` is feasible by edge deletion,
so its score is at most `M(n)+A`. The displayed linear gaps still diverge.
Consequently this entire enlarged class cannot provide `T-O(1)`.

This does not exclude a boundary strip of fixed width with a linear number
of additions, nor a redesign near every frame corner. A bounded-width strip
and a bounded total number of edits are different restrictions. To escape
this counting obstruction, off-frame centers must number at least
`T(k)-M(3k+2)-C` in any proposed `T(k)-C` construction. Their legality and any
additional deletions still have to be paid for; that necessary number is not
a sufficient construction recipe.

## Dual Periodic Alternative

There is an exact, architecture-independent way to formulate the remaining
periodic-fill task without adding a rootless or fixed-`c` requirement.

Let `U=V_n minus F`. Embed the grid in the plane. Define `D(U)` on all
`(n-1)^2` unit faces and the exterior face: include the dual edge crossing
each grid edge whose **two** endpoints lie in `U`. Keep parallel dual edges,
in particular at the exterior face. These are exactly the edges missing
from `H(F)`.

**Working paper lemma (planar forest-dual connectivity).**

```text
H(F) is a forest  if and only if  D(U) is connected.
```

This is the usual cycle-cut duality for a connected plane graph. A forced
cycle separates faces with no missing primal edge crossing it, disconnecting
the retained dual. Conversely a disconnection of the retained dual gives a
nonempty dual cut all of whose crossing primal edges are forced; that primal
edge set contains a cycle. The ambient grid, not `H(F)`, is the connected
plane graph to which this argument applies.

If `H(F)` is a forest with `c` components on all vertices, then

```text
|E(D(U))| = 2n(n-1) - (n^2-c)
          = (n-1)^2+c-1,
cycle_rank(D(U)) = c-1.
```

Thus demanding that `D(U)` itself be a tree would unnecessarily force `c=1`.
It is enough to exhibit a spanning tree inside `D(U)`; additional dual edges
are harmless. This preserves the freedom to use several forced components
and ambient isolates. It also explains why mere coverage of every unit face
by some U-U edge is insufficient: dual connectivity to the exterior is the
global invariant still needed.

**Proposed construction lemma, unresolved.** Give explicit coordinates for
`U_k` with

```text
|U_k| <= 6k^2+5k+4+C,
D(U_k) connected,
```

for one absolute `C` and all sufficiently large `k` in both parity branches.
Their complements would immediately prove `P(3k+2)>=T(k)-C`. This is an
equivalent useful construction target, not a proof that such sets exist.

A width-six periodic wavefront may address it, but must specify occupancy
and the complete equivalence relation of all live dual ports, including
which block contains the exterior. When a block loses its last live port,
it must already be joined to the exterior block or the final connectivity
goal becomes impossible. Distinct live blocks must not be collapsed merely
because they lack an exterior connection. In primal language the analogous
state retains all live forced-component identities and each separate isolate;
insertions test `{v} union (N(v) minus F)`, including `v` itself.

An explicit cell would need a geometrically repeatable port state, center
gain `12k+26` after all interface edits, and start/end closures of bounded
net score cost. A periodic interior density of one third alone does not
settle this: `T(k)=n^2/3+n-10/3`, so the linear boundary contribution matters.
The continuation supplies cell coordinates and an interior forest proof, but
not a valid closure. The nested-frame theorem does not obstruct general
periodic fills or offset nested frames.

## Concrete Moving-Phase Strip

Continuation, still paper-only. Additional read-only sources were
`analysis/PHASE_PATTERN.md`, `analysis/TILE_GRAMMAR.md`,
`analysis/RESIDUE_SHARED.md`, `analysis/RESIDUE_TWO_REVISED_CONSTRUCTION.md`,
the period-three and six-by-six bulk notes, and
`analysis/patterns/diagonal_patterns.py`. The stored side-11 and side-14 U
patterns were read, not executed. Historical computations at larger sizes
in these sources were not rerun or adopted as new evidence.

The useful distinction is between a doubly periodic cell and a periodic
**moving phase boundary**. The latter can change the number and endpoints
of long components. The following attempt uses that distinction rather than
another endpoint window. A dot means a preserved center; U means its
complement. Define three-cell packets

```text
L = UU.       R = .UU       X = U.U       H = UUU.
```

Fix `k>=3`. Packets occupy columns `1..3k`; packet `i` occupies columns
`3i+1,3i+2,3i+3`. The leading and trailing dots below are boundary centers
at columns zero and `3k+1`. Define rows

```text
C_a = . L^a X R^(k-a-1) .       0 <= a <= k-1,
W_a = . L^a H R^(k-a-1) .       0 <= a <= k-1,
D_a = . L^a H H R^(k-a-2) .     0 <= a <= k-2.
```

Their U counts are `2k`, `2k+1`, and `2k+2`, respectively. One three-row
advance `C_a W_a D_a` costs `6k+3`, exactly average charge one per row
relative to the two-U packet baseline. The inexpensive X row pays for the
two-H row needed to move the phase without a diagonal forced square.

Two consecutive advances, displayed on packets `a,a+1,a+2`, are the concrete
six-by-nine moving cell

```text
U.U .UU .UU       C_a
UUU .UU .UU       W_a
UUU UUU .UU       D_a
UU. U.U .UU       C_(a+1)
UU. UUU .UU       W_(a+1)
UU. UUU UUU       D_(a+1).
```

All packets to the left are L and all packets to the right are R. The display
applies when `a<=k-3`; it is not a tile to repeat independently in both axes.
The phase advances two packet positions across six rows.

### Exact Full-Board Attempt

Use these four cap rows, giving U columns rather than center columns:

```text
row 0:       {1,2},
row 1:       [1,3k+1],
row 3k:      [1,3k],
row 3k+1:    {1,3k}.
```

Between them put the word

```text
C_0 W_0 D_0 C_1 W_1 D_1 ... C_(k-2) W_(k-2) D_(k-2) C_(k-1).
```

In coordinates, `C_a` is at row `3a+2`, `W_a` at row `3a+3`, and `D_a`
at row `3a+4`, with only `C_(k-1)` retained in the last triple. There are
`3k-2` interior rows. The complete U count is

```text
caps:                 6k+5,
interior:             (k-1)(6k+3)+2k = 6k^2-k-3,
total:                6k^2+5k+2,
complementary count:  3k^2+7k+2 = T(k)+2.
```

Thus adding at most `C+2` further U vertices would suffice **arithmetically**
for `T-C`. The displayed count has six-width gain `12k+26`. These are
symbolic counts of a presently infeasible set, not lower bounds. The reason
it fails, and the actual open interface, can be determined without search.

### Interior Forest And Ports

Remove all boundary centers temporarily. The remaining centers are exactly
the following vertical rods and singletons:

```text
A_i = [2,3i] x {3i+1},              1 <= i <= k-1,
B_i = [3i+5,3k-1] x {3i+3},         0 <= i <= k-2,
x_a = (3a+2,3a+2),                 0 <= a <= k-1.
```

Every rod forces an interval tree. Different rod supports are disjoint.
Within either rod family the column separation is three. For cross-family
rods, only `A_i,B_i` and `A_i,B_(i-1)` can have columns within distance two;
their minimum center distances are respectively seven and three. All other
cross-family pairs have column distance at least four. These inequalities
also account for endpoint leaves, not just occupied centers.

For `1<=a<=k-2`, the star of `x_a` meets precisely

```text
B_(a-1) at (3a+2,3a+1),
A_(a+1) at (3a+2,3a+3).
```

The two vertices lie in different rod trees. The star misses all other rod
supports. At the ends, `x_0` meets only `A_1`, and `x_(k-1)` meets only
`B_(k-2)`. Stars of different x centers have center distance at least six
and are disjoint. Each rod appears in just one of these attachments.
Consequently the complete nonboundary forced support consists of **k
disjoint trees**, with ambient isolates elsewhere. This proves the open
interior's feasibility for arbitrary k, not just local unit-square legality.

Let

```text
t_i = (1,3i+1),        1 <= i <= k-1,
b_i = (3k,3i+3),       0 <= i <= k-2,
l   = (2,1),
q   = (3k-1,3k),
z   = (3k,3k-1).
```

These are the **entire** intersections of the interior support with the
forced support of the specified boundary centers. The exact partition is

```text
{l,t_1},
{b_(a-1),t_(a+1)} for 1 <= a <= k-2,
{b_(k-2),q,z}.
```

All listed coordinates are distinct. In particular this is not a state with
all independent interior trees merged into one abstract non-exterior block.
It is a matching of upper and lower ports, with one three-port end tree.

### Failed Cap And Specific Remaining Interface

The boundary center set has exactly five holes:

```text
(0,1), (0,2), (1,3k+1), (3k+1,1), (3k+1,3k).
```

Its forced support is one tree M. The boundary perimeter loses just the edge
between the adjacent top holes; at every corner at least one arm neighbor
is a hole, so inward edges are pendant rather than forming corner squares.
This is the same direct path-with-leaves proof as for a five-hole frame,
but with the actual new hole coordinates above.

Every one of the `2k+1` named ports lies in M. Gluing the k interior trees to
M therefore gives cycle rank

```text
(2k+1) - ((k+1)-1) = k+1.
```

Equivalently, each two-port tree creates one cycle and the three-port tree
creates two. The shared vertices are distinct, there are no shared edges,
and no unlisted support intersections exist, so this incidence calculation
is exact. This cap is decisively invalid; the excess is not a harmless dual
cycle excess. It is the cycle rank of the **primal forced graph**.

For these fixed interior trees, a replacement cap with the same distinct
contact coordinates must supply an acyclic bipartite incidence graph between
its actual components and the k displayed port blocks. If all `2k+1`
contacts remain, at least `k+2` cap components meeting them are necessary:
with t cap components, an incidence forest has at most `k+t-1` edges.
That component count is necessary, not sufficient; the displayed matching
must not create parallel routes through the new cap partition.

This is the concrete unsolved interface for this strip: replace the single
cap tree by such an incidence forest **without a linear net loss of centers**,
or rewrite the moving cell so that its upper/lower pairing changes before
closure. Arbitrarily adding `C+2` U vertices to the displayed candidate is
not a repair: deleting one center removes at most four edges, so it lowers
primal cycle rank by at most four. A bounded number cannot remove `k+1`
cycles. This last observation only excludes deletion-only bounded repairs;
distributed, count-balanced exchanges are not excluded.

The positive artifact is therefore a concrete target-charge moving cell,
an arbitrary-width interior forest, and its full coordinate port partition.
The negative artifact is the exact failed closure, not a new general no-go
for periodic fills. No cap with bounded net score cost survives this pass,
and the arithmetic `12k+26` gain must not be promoted to a construction gain.

## Verification Status

Only this new document was edited. Source and prior notes were read only;
pre-existing worktree changes were left untouched. No Lean build, script,
graph materialization, optimization, or bounded experiment was run. All new
formulas above are symbolic counts with paper proofs, not reported finite
search values or extrapolations from sides 11 and 14.

The concrete results are the exact nested-frame class obstruction and the
moving-phase cell's interior forest/port calculation with a refuted cap.
The unrestricted constant-gap lower problem, and in particular a verified
`12k+26` construction step, remain open.
