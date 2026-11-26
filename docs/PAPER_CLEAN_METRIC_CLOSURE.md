# Clean Metric Closure Attempt

Date: 2026-09-08. Paper investigation. No unconditional constant-gap upper
bound is proved. No Lean, search, or optimization was run.

## Result And Scope

Current checkpoint: independent read-only reviews covered the complete
note through Final Fragment And Front Test (original line 2362), with no
mathematical findings. This supersedes historical unaudited labels in the
appendices, not their explicit hypotheses. No Lean verification is claimed.

The main reviewed reductions and paper theorems are:

- Every narrow bank, W_B<=A/3, is paid with no asymptotic area remainder.
- A hypothetical K<n configuration has at most thirteen wide banks.
- Boundary-exposed banks with the specified actual interior-root paths
  admit a simultaneous payment with at most six units of error per bank.
- The explicit full-height two-root moving-seam skeleton has K>=4s-18
  on n=3s+5, hence f<=T+10, including arbitrary feasible additions.
- Canonical root restoration keeps only actual paths, but exposes unpaid
  incidence-cycle, restored-singleton, and interior-escape terms.
- Bank fragments bound skeleton/front counts, and total normalized
  unweighted axial front length is bounded; this does not pay the actual
  height-weighted packet debt.

The unconditional constant-gap bound remains open. Thirteen wide banks is
a reduction in geometric types to analyze, not thirteen already-paid roots.
Their partial terminals and weighted interaction can still grow with n.

The requested theorem remains open in this attempt. The completed new
deductions are spatial, rather than another elimination of the scalar cone:

1. An exact cutwise rail-forest formula expresses corridor length through
   actual carrier spans and a nonnegative fragmentation integral.
2. Under the hypothetical low budget `K<n`, the sum of the axial spans of
   all connected distance-three rail banks is less than `5n`. For every
   fixed positive epsilon, only `O(1/epsilon)` macroscopic banks are needed
   to carry all but `O(epsilon*n^2+n)` of the physical corridor-band area.
3. There is a canonical first-facing window system with at most three
   windows per nonsingleton carrier, counting the two orientations together.
   It excludes the arbitrary enclosing-pair reuse from the earlier note.
4. Opposing boundary-root carriers admit a simultaneous, matching-weighted
   span loss. A matched pair loses at least `n+3` from its combined `2n`
   carrier capacity. This gives a stronger, explicit low-budget exclusion
   whenever enough root pairs and boundary/component reserve coexist.

None of these statements assumes disjoint component boxes, cuts the board
into independently budgeted rectangles, or spends the isolate donors again.
The obstruction to combining them into coefficient three is detailed below.
In particular the macroscopic-bank theorem is not an additive-error theorem.

Inputs read in full: `PAPER_GLOBAL_METRIC_UPPER.md`,
`PAPER_GLOBAL_CAP_PAYMENT.md`, and `PAPER_ISOLATE_ROUTING_UPPER.md`, including
the corrected flat-packet transfer and the final refined clean certificate.
The carrier/contact reduction and projection discussion in
`PAPER_PROJECTION_UPPER_RESEARCH.md` were also consulted. The new deductions
below have not been independently reviewed or formally verified.

## Target And Retained Resources

Use vertex coordinates `0,...,n-1`, and put

```text
A=n-1, K=r+b+c,
3f+K=n^2+4n,
3X_2+Q_exc=A^2, 0<=Q_exc<=10K.
```

Here r counts actual straight filled carriers, including singletons; c
counts all components of the physical forced forest H, including isolates.
For `n=3k+2`, put `T=3k^2+7k`. Then

```text
3(f-T)=n+10-K.
```

The desired new spatial estimate is

```text
3X_2 <= A(K+C), with C an absolute nonnegative constant.       (1)
```

It would imply `K>n-11-C` and `3(f-T)<21+C`. In particular C=0
would imply `f<=T+6`. The exceptional area is already in this conversion.

The final isolate note instead supplies actual joined chains and

```text
L_*=g_+-j_C-nu_D-nu_N, X_2<=A L_*,
S >= 3L_*+1+B_C+nu_N+sigma_D-D_port+3j_C,
B_C=3(c-z-1)+t_0+3delta/2+C_C.                       (2)
```

Keeping their actual unused length `Delta_*=A L_*-X_2` gives the sufficient
debt

```text
max(0,D_port-B_C-nu_N-sigma_D-3j_C-3Delta_*/A).       (3)
```

This is only a sufficient certificate, not a new proof that (3) is bounded.
The endpoint slots in D_port and the retained isolate-join surpluses are
already allocated. The packet's inner three units are those same endpoint
slots, not a second bank. Any new use of carrier deficits below is a separate
inequality about the same F; it is not automatically an extra payment in (2).

## Cutwise Rail Forest

A horizontal nonsingleton carrier on row y has vertex interval `[l,u]`,
`l<u`, and FF edge labels `l,...,u-1`. Call it active at cut label i if
`l<=i<u`. Define vertical activity by rotation. Singletons have no active
cuts and need no assigned orientation.

At any fixed horizontal cut label i, form a graph whose vertices are the
active horizontal carriers, with an edge between rows differing by three.
This graph is a disjoint union of paths, including isolated vertices.

Indeed at one cut there is at most one carrier on any row. Its only possible
neighbours are on rows y-3 and y+3, and each edge strictly changes that row
coordinate. Each connected component is therefore a consecutive segment
of one arithmetic progression of rows of step three. No cycle is possible.

Every edge of this graph is exactly one horizontal straight crossing cell.
For rails on rows y and y+3, their FF edges at i force the cells `(i,y)`
and `(i,y+2)` to be opposite leaves. The intervening cell `(i,y+1)` is
all U, with those two deleted leaves, and is straight in the once-pruned
dual. Diagonal exclusion against the two FF edges forces its corners to
be U. Conversely the two opposite leaves of a horizontal straight cell
supply exactly these two FF edges. This is a bijection, including at the
ends of the board, not a choice of corridor windows.

Write `a_h(i)` for the number of active carriers and `p_h(i)` for the
number of components of this cut graph. Write `x_h(i)` for its number
of edges, equivalently its straight-cell count. Thus

```text
x_h(i)=a_h(i)-p_h(i).
```

Rotate and sum all cuts. Since every FF edge belongs to one carrier and
the total number of FF edges is f-r, this proves

```text
P_cut := sum_i p_h(i)+sum_j p_v(j),
X_2=f-r-P_cut.                                      (4)
```

The proof uses actual cut placements and the forest on each cut. Equation
(4) alone is not the requested upper bound: the substantive information
comes from lower bounds on this particular geometric P_cut.

## Banks And Fragmentation

Define the horizontal rail-bank graph on horizontal nonsingleton carriers.
Join two carriers when their rows differ by three and they have a common
FF edge label. Its connected components are horizontal banks. Define
vertical banks by rotation. A bank with one carrier is retained. Let
`r_ns` be the total number of nonsingleton carriers, so `r_ns<=r`.

For a bank B define

```text
W_B=max_B u-min_B l,
v_B=number of its carriers.
```

Here l,u are coordinates along its own axis. Every W_B is an edge-length
span in `[1,A]`. The union of the carriers' active-cut intervals in B is
the full integer interval `min_B l,...,max_B u-1`: adjacent bank vertices
have intersecting active intervals, and a connected union of intervals
has no gap. All horizontal carriers of a bank also have the same row
residue modulo three, with the analogous column statement vertically.

At a cut in this interval, the active part of B need not be connected.
Let `p_B(i)` count its components. It is at least one there and zero
elsewhere. No cut-graph edge connects two different banks. Consequently

```text
F_frag := sum_B sum_(i active in B) (p_B(i)-1) >=0,
P_cut = sum_B W_B+F_frag,
X_2=f-r-sum_B W_B-F_frag.                           (5)
```

These are bank spans, not bounding-box areas. Different banks may have
overlapping projections or boxes; all sums retain those multiplicities.
Fragmentation is not silently set to zero. The bank graph itself need not
be a forest, even though its graph at each individual cut is a forest.

Let X_B be the straight-cell count whose two rails belong to B. These
counts partition X_2, in both orientations together. At each active cut
there are at most `v_B-1` edges, whence

```text
X_B <= (v_B-1)W_B <= v_B W_B.                        (6)
```

This inequality and (5) are valid for arbitrary isolates and contacts.

### Low-Budget Concentration

Substituting the two original ledgers in (4), without discarding Q_exc,
gives

```text
P_cut=(6n-1-K+Q_exc)/3-r
     <=2n-1/3+3K-r.                                (7)
```

Thus the hypothetical regime `K<n-D`, `D>=0`, satisfies

```text
sum_B W_B+F_frag < 5n-3D-r-1/3.                     (8)
```

The equality used in (7) is algebra; the consequence for the sum of
geometrically defined bank spans uses the independently proved (5).

Fix `0<epsilon<=1`, and call B large if `W_B>=epsilon*A`. Under K<n,
(8) bounds the number of large banks by

```text
#large < 5n/(epsilon*A).
```

By (6), the other banks carry fewer than `epsilon*A*r_ns` straight
cells. Since `r<=K<n`, the width-three corridor bands belonging to large
banks have total physical area greater than

```text
A^2-10n-3epsilon*A*n.                               (9)
```

Here the bands are the straight cells together with their two deleted
leaves. They are disjoint physical cell sets by the original corridor
partition. No claim is made that the corresponding bank rectangles are
disjoint. A negative lower bound in (9) is simply uninformative.

There is also a macroscopic-bank existence statement whenever X_2>0:

```text
max_B W_B >= X_2/r_ns >= (A^2-10K)/(3r),             (10)
```

where the final inequality is useful when its numerator is positive.
For integer K<n and n>=12 this in particular gives a bank of span at
least `(n^2-12n+11)/(3(n-1))`. These are actual phase-coherent, overlap-
connected collections of rails, not abstract scalar assignments.

## Canonical First-Facing Windows

At each horizontal cut, list its active horizontal carriers by row.
Consecutive carriers in this list are first-facing at this cut. For a
fixed ordered pair, take maximal consecutive intervals of cut labels on
which that pair remains consecutive and active. These are its windows.
Their longitudinal width is the number of cut labels, and their height
is the row separation. The bounding rails are actual FF intervals
throughout the window. Use the identical definition vertically.

All such heights are at least three. Height one would contradict diagonal
exclusion using the two FF edges; height two would force the six-edge
perimeter cycle between them. Height-three windows are exactly positive
corridors, with their full straight portions. In particular the construction
does not omit any straight-cell area.

There are at most `3r_ns` windows over both orientations. To see this,
sweep the cut coordinate. Each carrier has one insertion and one deletion
in the ordered active list. An insertion creates at most two new adjacent
pairs; a deletion creates at most one. Initially the list is empty. Each
new maximal window starts with a newly created pair, so at most three
starts per carrier are possible. Simultaneous endpoints can be processed
in any order at that coordinate: intermediate pairs that exist for no
actual cut produce no window and only weaken this upper bound.

For each fixed orientation, the interiors of the windows as geometric
rectangles are disjoint: at a cut they are gaps between consecutive rows
or columns. This prevents summing all enclosing wider rail pairs around
one gap. It does not establish cross-orientation disjointness of the wider
windows, nor private carrier or isolate credits for them. In particular
the sum of their widths is not a new resource in K.

The source's distance-four theorem can be applied to actual distance-four
pairs with full overlaps; its private middle-strip witnesses remain valid.
For a wider window, no universal width payment from the final clean bank
has been proved. First-facing in this definition excludes intervening FF
rails, not interior singletons, perpendicular carriers, or paths around
the longitudinal ends. This distinction matters for a planar argument.

## Opposing Root Span Loss

Take any regular straight boundary-spine caps from the source's joint
contact construction. On the left each inward horizontal carrier has
left endpoint at x=2, and on the right it has right endpoint at x=n-3.
The first straight cell forces a nonsingleton carrier; its adjacent
contact hole excludes extension toward the boundary. Deduplicate repeated
contacts to the same root carrier before counting roots.

Let B_boundary be the set of pure boundary carriers used here, of size p.
A root carrier attached on both the left and right is called a bridge.
There are at most p-1 bridges when p>0. Retain just their two boundary
contact edges in the actual carrier contact forest and suppress each
bridge vertex. The resulting multigraph on B_boundary is a forest.
In particular two bridges between the same boundary pair would create
an actual forced cycle, not an extra pair of component credits.

Discard bridge carriers from both root lists. The remaining left and
right root sets are disjoint sets of actual carriers. Form the bipartite
graph connecting a left root to a right root when their row coordinates
differ by at most two. Let M be the size of any matching in this graph.
Matching ensures that each actual carrier is used at most once.

For every matched pair with vertex lengths ell_L,ell_R,

```text
ell_L+ell_R <= n-3.                                 (11)
```

Proof: distinct nonsingleton carriers in the same row have disjoint
intervals, with a U gap. In adjacent rows their column intervals cannot
overlap: a common F column and an inward horizontal neighbour of either
carrier would give diagonal F corners. In rows at distance two their
overlap has at most one column, since two overlap columns give two forced
vertical connections and the intervening rail intervals give a perimeter
cycle. The right-root interval cannot start before column two: it would
then contain columns two and three, both present in the nonsingleton
left root, giving a forbidden two-column overlap. Symmetrically the left
root cannot end beyond column n-3, since both roots would contain n-4
and n-3. These arguments use n>=11. Their union therefore lies in
`[2,n-3]`, which has n-4 vertices. Only the distance-two case permits
one overlapping column. This proves (11) in all cases.

Since every other carrier has length at most n, summing the private pairs
gives the unconditional inequality for this selected root system

```text
nr-f >= (n+3)M.                                     (12)
```

In particular a span-aware low-budget exclusion follows:

```text
(3n+1)K >= n^2+4n+3n(b+c)+3(n+3)M.                  (13)
```

For any fixed d>=0, (13) proves K>=n-d whenever

```text
b+c+(1+3/n)M >= 2n/3-1-(1+1/(3n))d.                (14)
```

For d=0 this gives f<=T+3. This is a conditional class, not an assertion
that the matching threshold always holds. Bridge removal has its actual
p-1 cost, not an absolute cost when the number of pure intervals grows.

For any chosen root graph the matching size itself has the exact Hall
description

```text
M_max=|L|-max_(U subset L)(|U|-|N(U)|).
```

Thus a proposed root-density argument must control the neighbourhood
deficiencies of the actual row positions. A count of left and right roots
alone is not such a control. One may rotate the argument, but may only add
the resulting carrier deficits when the participating carriers are disjoint.
Even then they cannot also be offered as fresh endpoint-slot credit in (2).

## Closure Tests And Failures

**Area versus spans.** Formula (5) exactly measures the physical rail
packing without boxes. It does not upper-bound X_2 by `A*K/3`.
With K<n, (8) controls a total span of order n, whereas the required new
payment concerns area of order n squared divided by n. Replacing all
carriers in a bank by its single axial span loses their multiplicities
v_B in (6). Treating each bank as one full-length allowance is therefore
invalid.

**Macroscopic reduction.** Equation (9) reduces most area to finitely many
phase-coherent banks at any fixed accuracy. This is stronger than scalar
near-complete area alone, but does not give constant excess. To leave only
O(n) uncontrolled area by this estimate requires epsilon=O(1/n); the
number of retained banks then may be O(n). Even a theorem giving K>=n-o(n)
would still allow unbounded sublinear excess. No limiting argument here
upgrades approximate concentration to the requested absolute constant.

**First facing and terminal paths.** The canonical windows have real rails
and no intervening parallel FF rail. This does not make each window a
disk containing the relevant paths of the forced forest. A rail can end,
and a rooted component can pass around it. To apply the source's alternating
boundary-point obstruction one must exhibit the whole path inside the same
disk, or instead account for the actual carrier span used in escaping it.
Adding an artificial continuation of a partial rail is not allowed. The
two monotone banks of a rigid one-pair seam still pass the ordinary planar
order test; nothing proved here reverses either terminal order.

**Root matching and coefficient.** The forest supplies bridge exclusion,
and spatial root proximity supplies (11). Neither supplies the universal
threshold (14). Even one order-n family of matched opposing roots of size
about n/3, with small b+c, only yields the order-2n/3 lower bound on K
from (13). Its carrier loss can be the same loss already measured by the
parallel-knight inset inequality. Adding the two right-hand losses without
a joint allocation would be reuse, not the missing coefficient three.

**No free interface or width bank.** No rectangular restriction was made.
If one now cuts the board to isolate the finitely many large banks, the
source's exact `sum K_part=K+2L` still applies. The artificial 2L cannot
be kept as payment. Likewise, the O(r) count of canonical wider windows
does not bound their total width by O(K); a window may have width of order
n. The separation-seven resource change and cross-orientation nonreuse
must still be addressed, not bypassed by the word first-facing.

## Remaining Theorem

A sufficient next spatial theorem would control the terminal regions of
the actual banks and first-facing windows simultaneously: after charging
private boundary holes, carrier spans, contacts, and the already allocated
clean resources only once, either enough ordered joins exist or enough
normalized unused length exists to bound (3) by an absolute constant.
Alternatively one can prove (1) directly and bypass that clean allocation.

This attempt establishes neither theorem. In particular it does not
derive a forced cycle for every hypothetical K<n-C layout. The new
bank concentration, linear-size canonical exposure system, and root-span
inequality are rigorous deductions; their promotion to a universal metric
payment is the remaining failure. No new example is offered in place of
that missing implication, and no scalar identity is claimed to close it.

Verification scope: the arguments above are symbolic interval, forest,
and coordinate proofs. No finite grid was instantiated. No optimizer or
Lean command ran. Only `docs/PAPER_CLEAN_METRIC_CLOSURE.md` was written;
all other worktree changes were left untouched.

## Height-Weighted Continuation

Date: 2026-09-08. The user reports independent review of the preceding
prefix. This appendix leaves that prefix unchanged; its new claims do not
inherit that review. The complete `PAPER_CLEAN_ALLOCATION.md` was read,
including the peak-chain Hall theorem and its exact unused-length
cancellation. The explicit nested-frame construction in
`PAPER_CONSTANT_GAP_LOWER.md` was read for an analytic test, not an optimum
search.

The unrestricted constant-gap theorem is still not proved. There is,
however, an improvement to the reduction: the epsilon-area error is
unnecessary. All banks of width at most A/3 can be paid completely from
private carrier units. Under K<n, at most 13 wider banks remain. Their
height-weighted excess is stated explicitly below, including the cost
reduction from additional carrier fragments. This is an exact global
reduction with no small-bank error, not another restricted strand class.

### The Proposed Unweighted Bound Is False

The candidate

```text
sum_B W_B <= K+O(1)                                 (15)
```

fails for feasible boards, even when there are exactly four banks and
EVERY bank carries positive corridor area. Thus deleting the zero-area
banks does not repair it.

Here is a uniform analytic test. For this construction only, coordinate
pairs are (row,column). Take n=6m+2, m>=2, and the nested-frame
construction from the lower note, using the same orientation on every
frame. For j=0,...,m-1 its square has corner (3j,3j), side ell=n-6j, and
is preserved except for the five translated local vertices

```text
(0,1), (0,2), (1,ell-1), (ell-1,ell-2), (ell-2,0).
```

In the innermost side-two square, preserve `(3m,3m),(3m,3m+1)`.
Each large frame has four straight carriers. Its forced perimeter is
a path, because precisely one perimeter edge has two deleted endpoints;
all remaining edges of its support are pendant. Different frames have
preserved-set distance at least three, so their closed neighbourhoods
are disjoint. The innermost pair also has tree support. These facts prove
feasibility for every m, including the actual ambient isolates.

There are exactly four banks. The top carriers of consecutive large
frames are on rows differing by three and have overlapping FF intervals;
the innermost pair joins this bank too. The bottom carriers form a second
bank, and the left and right carriers form the two vertical banks. The
top and bottom rows have different residues modulo three, as do the left
and right columns, so the indicated banks cannot merge. Their spans are

```text
top: n-4; bottom: n-3; left: n-3; right: n-3.
sum_B W_B=4n-13=24m-5.                              (16)
```

All four banks have positive overlaps between consecutive large frames
when m>=2. The score and budget, obtained by summing the frame sizes, are

```text
f=2+sum_(j=0)^(m-1) (4(n-6j)-9)=12m^2+11m+2,
r=4m+1, b=5,
K=n^2+4n-3f=15m+6, c=11m.
```

In particular

```text
sum_B W_B-K=9m-11 -> infinity.                      (17)
```

This example has K=(5/2)n+1, not K<n. It disproves the proposed
UNCONDITIONAL width payment; it does not refute a low-K-only version of
(15), and does not refute the desired metric theorem. A low-K-only proof
of (15) would still suffice, but is not supplied by this test.

### Bank Height Is A Valid Capacity

For each bank B let H_B be the difference between its extreme transverse
carrier coordinates, and define

```text
a_B=H_B/3,
s_B=v_B-1-a_B.
```

The quantities a_B and s_B are nonnegative integers. To prove this,
connectedness of the bank graph, whose edges change transverse coordinate
by three, forces every intermediate row or column of its residue class
to occur. There are exactly a_B+1 distinct transverse levels, with at
least one carrier on each. Thus v_B>=a_B+1. Repeated carrier fragments
on one level are counted in s_B, not identified with one carrier.

At a fixed cut at most one carrier is active on each level, and its
cutwise graph is a forest. Therefore

```text
x_B(t)<=a_B,
3X_B <= H_B W_B,
a_B<=floor(A/3)=k on n=3k+2.                        (18)
```

This verifies the user's proposed height restriction in the correct
form: the number of ACTIVE levels is bounded, whereas the total number
v_B of carrier fragments need not be at most k+1. Consequently (15),
if true with an absolute constant, would have implied
`3X_2<=(n-2)(K+O(1))`. The failure is the width payment, not (18).

The rectangles with side lengths H_B,W_B can overlap, and can include
large regions not belonging to their bank. Equation (18) is an individual
upper bound, not a claim that those rectangles partition the board.

### Full Payment Of Every Small Bank

Call B small if W_B<=A/3, and wide otherwise. Let r_1 count singleton
carriers, r_ns=r-r_1, and t_bank count all banks, including one-carrier
and zero-corridor banks. Banks partition the nonsingleton carriers.

For EVERY small bank, the prefix's physical cutwise bound gives

```text
3X_B/A <= (3W_B/A)(v_B-1) <= v_B-1.                 (19)
```

This is a private allocation from the original r term of K, and it can
be made cell by cell. Choose one distinguished carrier of each bank by
any fixed ordering. At each active cut, root its cut-forest component at
that carrier if the carrier is active, and root every other component
at its lowest transverse carrier. Orient the path edges away from these
roots. Assign each edge's straight cell to its child carrier. Every
straight cell is assigned exactly once, each carrier receives at most
one cell per cut, and the distinguished carrier receives none.

Thus each other carrier receives at most W_B straight cells, with total
normalized band cost at most 3W_B/A. In fact it receives at most its own
number of FF edges, because it must be active at every charged cut. Use
that much of its original unit in r. Different banks use different actual
carriers, and singletons are not used at all. The units may be fractional,
as the metric target itself is normalized by A. This routing is only a
counting assignment in the cutwise rail forest: it asserts no new path
in H and performs no component deletion. There is no area approximation
or carrier-unit reuse.

The retained small-bank refund is explicitly

```text
R_small=sum_(B small) (1-3W_B/A)(v_B-1) >=0.         (20)
```

Every straight cell of every small bank has now been included, regardless
of how many scales of widths occur. There is no logarithmic loss and no
epsilon*n^2 remainder. One does not subdivide banks or introduce artificial
boundary credits in making this payment.

This allocation is a DIRECT K argument. It must not also be added as a
new bank to the isolate note's clean certificate, which already derived
its credits from K. The following continuation consistently uses the
direct argument instead.

### At Most Thirteen Unpaid Banks

For a wide bank, reserve the same v_B-1 carrier units as a baseline. Its
remaining sufficient demand, using (18), is

```text
E_B=max(0,H_B W_B/A-(v_B-1))
   =max(0,a_B(3W_B/A-1)-s_B).                       (21)
```

All narrow banks have E_B=0. A wide bank can have E_B=0 too, particularly
when its many actual fragments already pay its rectangle capacity.
Summing (18)--(21), with (19) used for small banks, proves unconditionally

```text
3X_2/A <= r_ns-t_bank + sum_(B wide) E_B - R_small.  (22)
```

The unspent original resource consists of

```text
R_free=b+c+r_1+t_bank+R_small.
```

Thus a sufficient global spatial theorem is

```text
sum_(B wide) E_B <= R_free+C,                       (23)
```

for an absolute C>=0. It would imply `3X_2<=A(K+C)` and the desired
constant upper excess by the prefix's conversion. In particular C=0
would give f<=T+6. No claim that (23) always holds is made here.

To seek (23), it is enough to work under K<n: when K>=n, the original
area inequality already gives `3X_2<=A^2<A K`. In that low-budget regime,
one can sharpen the prefix's coarse span estimate using integrality.
Since n=3k+2, the global ledger makes K a multiple of three, so K<=n-2.
Also f<=nr and the same ledger imply

```text
r >= (n^2+4n-K)/(3n) >= n/3+1+2/(3n),
r >= k+2=(n+4)/3.
```

Consequently (7) gives `sum_B W_B<=(14n-23)/3`. Every wide bank has
integer width at least k+1=(n+1)/3. Thus

```text
#wide <= (14n-23)/(n+1)=14-37/(n+1)<14.
```

Hence there are at most 13 wide banks. This is not the earlier fixed-
accuracy truncation. ALL the area of the arbitrarily many remaining
banks was paid in (19), and their unused carriers and fractional refunds
remain in R_free. In particular an inability to control tiny banks is no
longer a reason for leaving an epsilon-area error in this approach.

More generally, any cutoff tau*A with 0<tau<=1/3 gives at most
`5n/(tau*A)` retained banks and fully pays the smaller ones. Taking
tau=1/3 gives the fewest exceptional banks within this particular
one-carrier-unit payment. Taking tau larger would leave a positive demand
per small-bank carrier and requires a different proof, not a rescaling.

### Internal Contacts And Fragment Directions

There is an additional physical restriction relevant to a proposed
telescoping contact payment. Let m_B be the number of contact-forest
edges with both carriers in B. Then

```text
m_B<=s_B,
v_B-m_B>=a_B+1.                                    (24)
```

For a horizontal bank, a contact between different rows would require
row separation two, since its hole has opposite F neighbours. Bank rows
instead differ by multiples of three. Thus every internal contact is
between collinear fragments on one row, across a single U vertex. On
each row those contacts form a subgraph of the ordered path of fragments,
and there are at most one fewer contacts than fragments. Summing the
a_B+1 nonempty rows proves (24). Rotation covers vertical banks.

The quantity s_B in (21) consequently has a concrete meaning: additional
same-level fragments already contribute carrier units before internal
contacts can reduce component count. The contact inequality does NOT
provide an additional m_B credit on top of that same s_B.

In particular the contact forest induced on B has at least a_B+1
components. These are components AFTER other carriers are deleted, not
necessarily a_B+1 ambient H components. They may be joined through a
boundary spine or other external carriers. Treating them as fresh c
units would repeat the earlier boundary-root deletion error.

Nor can one contract each entire bank and apply forest acyclicity to the
result. A bank is connected by corridor-rail adjacency, not necessarily
by physical contact paths. The nested-frame test makes this distinction
literal. Each frame's four carriers form a contact path in the order
top, right, bottom, left. Identifying the four banks across frames creates
parallel contact edges along these three pairs. The resulting bank graph
has cycles for m>=2, although the original contact graph is a forest.
Such an identification is not a forest-minor operation.

Thus a contact proof of (23) must retain the separate rooted pieces and
their locations. Ordinary forest rank does not telescope bank demands
against distinct ambient components.

### Comparison With Peak-Chain Hall Allocation

Distinguish W_peak, the COUNT of optimal allowances in
`PAPER_CLEAN_ALLOCATION.md`, from the lengths W_B in this note. For a fixed
execution of its paid dirty/donor joins, let w_d(t) count base-chain hulls
covering cut label t in axis d. Let x_d(t) be the number of actual straight
cells at that label, summed over all banks of that axis. Then exactly

```text
w_d(t)=x_d(t)+g_d(t), g_d(t)>=0,                    (25)
```

where g_d(t) counts chains whose hull contains t but whose straight
projections do not. A base chain has at most one straight cell at a given
axial label, because its intervals were joined with strictly ordered
projections. This proves (25) without identifying physically different
rows. Summing g_d(t) is precisely that note's internal hull-gap count.

Its Hall theorem controls peaks of x_d+g_d. Equations (19) and (22)
instead control the integral of actual x_d, bank by bank. A large peak
from many short overlapping intervals need not consume much area; the
small-bank payment therefore need not solve that peak Hall problem.
Conversely, the gap term g_d is not a collection of fresh bank-width
witnesses: the source has already included it in unused chain length.

One paid base chain can contain corridors from different banks. Splitting
it to assign hulls to individual banks can undo paid dirty or donor joins.
That is not needed for (22), which partitions straight CELLS, and would
require returning the corresponding credits if used in the clean
allocation instead. Neither method authorizes adding its own resource
total to the other method's total.

Even the optimal peak allocation, with complete unused length, still has
the source's exact cancellation

```text
3*(number of extra joins)+3*(unused length)/A
   =3N-3X_2/A.
```

The new small-bank theorem bounds part of the physical X_2 geometrically;
it is not a way to evade this cancellation. After that part has been
paid, a peak-Hall proof still has to relate the wide-bank area to actual
unspent natural resources. Optimizing interval concatenations alone
supplies no further inequality of that kind.

### What The Finite-Bank Reduction Does Not Prove

The outstanding sufficient estimate is now (23), on at most 13 wide
banks under K<n. Its left side uses heights, widths, and actual fragment
counts, rather than merely the unweighted width sum disproved in (17).
Its right side uses only original, jointly available resources. This
removes the multiscale truncation issue but does not finish the theorem.

Three attempted final steps remain unjustified:

1. Summing H_B W_B as if the bank boxes were disjoint is not valid.
   A bank can be sparse within its box, and two bank boxes can overlap.
   Any saving from this sparsity or overlap must be proved for the actual
   cell sets, not assumed as a rectangle partition.
2. The a_B+1 rooted pieces from (24) are not independent c credits.
   Reconnecting them through a long perpendicular carrier can use few
   new carriers. To charge its span, one must also track where the bank
   rails terminate and what happens on the other side of that carrier.
   No universal non-reusing endpoint-direction charge is proved here.
3. A bounded number of wide banks is not a bounded number of terminal
   events. Each bank may have order-n carriers and a long moving boundary.
   A constant-width seam of length O(n) WOULD have only O(1) normalized
   area cost, but its removal does not make a staircase-shaped bank close
   to its bounding rectangle: that difference can have order-n-squared
   area. Nor may an order-n interface's artificial 2L budget be retained.
   Paying order-n endpoints at a constant budget unit EACH would instead
   be a growing normalized error. Finite bank count alone supplies neither
   a Hall condition for those demands nor a forbidden alternating root order.

No universal bound on the positive part of
`sum E_B-R_free` has been obtained. In particular, (22)--(23) are not
presented as a scalar proof that the excess is bounded: the uniform
spatial implication (23) is precisely the missing assertion, and it may
be stronger than necessary because of the rectangle overestimate in
(18). One can replace that overestimate by actual area in a future proof,
but merely writing the resulting exact deficit is not new evidence.

The completed progress is the analytic rejection of the unconditional
unweighted width target, the height/fragment capacity, full private payment
of all small banks, the resulting at-most-13-bank reduction without an
epsilon error, and the internal-contact restriction. The global constant
and a forced-cycle contradiction for all K<n-C configurations remain
unproved.

Verification for this appendix consists of the displayed arbitrary-size
proofs and 16,786 exact-rational arithmetic cases checking the height
demand, small-bank refund, thirteen-bank count, and nested-frame formulas.
Those cases are scalar checks, not geometric feasibility evidence. No
grid was instantiated, no optimization of any size ran, and no Lean
command ran. Whitespace checking passed. Only this appendix was written;
the reviewed prefix and all other files were left unchanged.

## Rooted Boundary Coverage Continuation

Date: 2026-09-08. The preceding material is preserved unchanged while
under review. Read the complete new finite-wide-bank appendix of
`PAPER_CLEAN_ALLOCATION.md`, through its protected-root comparison (34).
The arguments here use its DIRECT K allocation, not a second copy of the
clean isolate bank. This continuation has not been independently reviewed.

There is a substantive root-payment theorem. For t consecutive
three-spaced rail levels reaching the last two columns, with an actual
common connection behind those columns, the opposite boundary supplies
at least `2t-3` units from boundary holes, distinct inward isolates, and
protected pure-boundary carriers. The number of roots is unrestricted.
The statement permits each rail to stop at depth two, or extend farther
toward the boundary. It includes pure singleton carriers and does not
count nonpure boundary endpoints as free pure units.

These payments can be made simultaneously for all wide banks with the
specified exposure, with total error at most six per selected bank, not
six per root. Thus the at-most-thirteen-bank reduction makes this loss
absolute. The hypothesis is not proved for every remaining wide bank,
and the unconditional constant-gap theorem is still not obtained. The
precise uncovered geometry is stated at the end.

### The Current Available Resources

Use the new source's notation, distinguishing its q_B from cut-component
counts:

```text
p_B = number of nonsingleton pure-boundary carriers in bank B,
q_B = max(1,p_B),
Q_roots = sum_B q_B,
R_sb = sum_(B small) (1-3W_B/A)(v_B-q_B),
R_av = b+c+r_1+Q_roots+R_sb.                        (26)
```

All these resources are jointly retained by that source. A pure singleton
carrier has its original unit in r_1. Every other pure-boundary carrier
has its original unit in Q_roots. In particular a perpendicular boundary
spine is retained even when its own bank has height zero and no packets.

The duplicate packet-rectangle area has already been removed by the
source. Its remaining sufficient comparison is

```text
|R_union|/A <= sum_(B wide)(v_B-q_B)+R_av+O(1).       (27)
```

The payment below uses a specified subset of R_av. It does not add the
old R_free, recover already donated V/T credits, or treat deletion
components as ambient c units.

### A Physical Rooted Window

Normalize the target boundary to the right side x=A. Choose

```text
y_i=y_0+3i, 0<=i<t,
2<=y_0<=y_(t-1)<=A-2.
```

Assume the following ACTUAL geometry:

1. Both `(A-3,y_i)` and `(A-2,y_i)` are preserved, for every i.
2. The vertices `(A-2,y_i)` are connected in the subgraph of H induced
   by `x<=A-2`.

Condition 2 is about existing paths, not an added separator or a repaired
configuration. A common perpendicular pure-boundary spine on the left,
with the actual inward rail contacts, is one way to supply those paths.
The condition also permits other existing interior connections.

Put `J=[y_0-1,y_(t-1)+1]`. Define h_J to count boundary holes `(A,y)`
with y in J. Define p_J to count ALL actual pure-boundary carriers
meeting this boundary interval, including singleton carriers. Finally,
let z_J count globally isolated vertices of the form

```text
(A-1,y), y_0<y<y_(t-1), y not equal to any y_i.
```

Only the indicated interior off-level witnesses are counted in z_J;
the two outer off-level positions in J are deliberately not used.

**Rooted-window theorem.** Under these hypotheses,

```text
h_J+z_J+p_J >= 2t-3.                               (28)
```

This is a coefficient-two payment for the rows of a rooted bank. It
does not assume that the side is almost full or that there are no
isolates elsewhere.

### Forced Labels And The Genuine Cycle Test

Let epsilon_i indicate whether `(A-1,y_i)` is F. This permits both
shorter endpoints and extensions toward the boundary. Diagonal exclusion
against the displayed back FF edges forces

```text
(A-2,y_i+1), (A-2,y_i+2) to be U;
(A-1,y_i+1), (A-1,y_i+2) to be U                    (29)
```

between every two successive marked levels. For example the two
exclusions in the first line use `(A-3,y_i)` and `(A-3,y_i+3)`.
The second line uses the corresponding F vertices at column A-2.
The two outer positions `(A-1,y_0-1)` and
`(A-1,y_(t-1)+1)` are U as well, by the same local diagonal rule.

At an off-level adjacent to y_i, the left neighbour of `(A-1,y)` is U
and its other off-level vertical neighbour in column A-1 is U.
Consequently, for the INTERIOR off-level positions in z_J,

```text
(A-1,y) is isolated
  iff (A,y) is U and the adjacent epsilon_i is zero. (30)
```

The nearest marked level is unique: the two off-levels between marks
are adjacent respectively to the lower and upper mark. At the two
outer off-levels, an additional supplier outside J may exist; this is
why they are excluded from z_J. There are only two such positions.

If epsilon_i=1, diagonal exclusion forces BOTH boundary neighbours
`(A,y_i-1),(A,y_i+1)` to be U. Any boundary F vertex at y_i in this case
belongs to the inward horizontal carrier, and is not called pure.
Every other boundary F vertex in J has its inward neighbour U. Its
boundary F run belongs to an actual pure-boundary carrier. This remains
true for a run consisting of one vertex: its inward neighbour is U,
so it is a pure singleton unless it continues along the boundary outside
J, in which case its carrier is again pure. A boundary FF continuation
cannot turn inward in a feasible set.

Consider the forced boundary path on the vertices of J. Its edges are
present exactly when at least one endpoint is F. Every component of
this path contains at most ONE marked boundary F vertex `(A,y_i)`.
Indeed each such F vertex has a forced two-edge connection through
column A-1 to `(A-2,y_i)`, irrespective of epsilon_i. Two such
connections, their boundary path, and a simple connecting path from
condition 2 form a literal cycle in H. The interior path has x<=A-2;
the boundary path has x=A; their two joining paths are disjoint except
at their endpoints. No virtual bank edge participates in this cycle.

### Four-State Proof Of The Width Price

Here is a complete finite certificate for the remaining one-dimensional
count. It proves (28) at arbitrary t, not by testing windows of bounded
length.

Read the boundary word in triples

```text
(y_i-1, y_i, y_i+1), i=0,...,t-1.
```

The middle position of each triple is marked. A state records the
previous letter and whether its current forced boundary-path component
already contains a marked F. The four states are

```text
0=(U,0), 1=(U,1), 2=(F,0), 3=(F,1).
```

An edge U--U begins a new component and clears the second flag. Any
other edge retains the flag. A marked F is forbidden when the flag
is already one; otherwise it sets the flag. Start in state 0, with
a fictitious preceding U and no earlier marked attachment. Ignoring
outside attachments only relaxes the necessary cycle condition.

For a triple of type epsilon, assign the following costs:

* Each marked U costs one boundary-hole unit.
* Each off-level U costs `2-epsilon`. For epsilon=0 this is a hole
  unit and its candidate inward-isolate unit. For epsilon=1 it is only
  the hole unit.
* Each start of a boundary F run costs one pure-carrier unit, EXCEPT
  an epsilon=1 marked F. That F is an isolated boundary run with an
  inward FF continuation and is not pure.

When epsilon=1, the two off-level letters must both be U. This implements
their proved diagonal exclusion, rather than charging an isolate beside
an extended rail. All other allowed letters and states are retained.

The following table gives the MINIMUM cost of a three-letter transition;
a dash means no transition. It is obtained by the eight binary triples
for epsilon=0 and the two possible triples for epsilon=1, with the
marked-F cycle test above. No states or boundary words are optimized away.

| Incoming state | To 0 | To 1 | To 2 | To 3 |
|---|---:|---:|---:|---:|
| 0 | 3 | 2 | 3 | 1 |
| 1 | 3 | 2 | 4 | 3 |
| 2 | 3 | 2 | 2 | 0 |
| 3 | 3 | - | 4 | 2 |

Use the potential

```text
phi(0)=-1, phi(1)=-1, phi(2)=0, phi(3)=-2.
```

Every entry in the table satisfies

```text
transition cost >= 2+phi(out)-phi(in).              (31)
```

Summing t transitions, starting in state 0, proves total cost at least
`2t-1`, since every final potential is at least -2. The pure-run cost
counts p_J exactly, including a pure run continuing into J from outside.
The hole cost is h_J. By (30), all the candidate isolate costs except
possibly the two outer off-levels are actual, distinct witnesses in z_J.
Thus the computed cost is at most `h_J+z_J+p_J+2`. This proves (28).

Pure singleton units are essential in this proof. For example the
periodic boundary word `.FFFFF.F.` with marks at positions 0,3,6 has
three holes, one off-level inward isolate, one long pure run, and one
pure singleton per period, with epsilon=0 throughout. Consecutive
periods have a U--U break, so the marked-F component condition is
respected. Omitting the singleton would leave only five units for three
marks; retaining it gives six. This is a check on the required resource
type, not a global upper-bound counterexample.

### Payment For An Exposed Wide Bank

Assign a positive-height wide bank a target side perpendicular to its
axis. Call it exposed for this payment if, after rotation to the right
side, EVERY one of its transverse levels in `[2,A-2]` has the FF edge
`(A-3,y)--(A-2,y)`, and all those vertices `(A-2,y)` are connected in
`H[x<=A-2]`. The rail on a level may extend to column A-1 or A. Other
same-level fragments elsewhere in the bank are permitted.

This definition checks actual FF edges and actual paths. Having W_B>A/3,
having a bounding box reaching the boundary, or being in one ambient
component does not by itself satisfy it.

Write a=a_B. There are a+1 transverse levels, and at most two of them
lie outside `[2,A-2]`, because the levels are three-spaced. Thus the
regular levels form a consecutive run with

```text
t=a+1-d, 0<=d<=2.
```

Use the source's protected-root inequality `q_B-1<=s_B`. The entire
positive rectangle demand of this bank is bounded by

```text
D_B=max(0, |R_B|/A-(v_B-q_B))
   =max(0, 3a W_B/A-a-s_B+(q_B-1))
   <=2a.                                          (32)
```

This retains all fragment and protected-boundary-root counts with their
correct signs. It does not spend s_B a second time as a contact credit.

For t>=2 apply (28) to the regular levels. Since
`2a=(2t-3)+(2d+1)`, the bank has the genuine resource payment

```text
D_B <= h_J+z_J+p_J+5.                              (33)
```

If t<=1, then a<=2 and D_B<=4; simply pay that bank from the same
five-unit absolute allowance, without requesting boundary resources.
The bank's packet set need not be a rectangle: (33) pays the full
rectangle demand, and therefore also its actual packet demand.

In particular a height-zero boundary spine may connect arbitrarily many
of these rails. No new c unit is requested for each root, and no
assumption that their deletion components are independent is used.
The common spine supplies existing paths; the payment comes from the
opposite boundary word and its actual inward isolates.

### Simultaneous Four-Side Nonreuse

Select any N exposed positive-height wide banks, assigning each one
exactly one target side. Under K<n, N<=13. Form windows only for those
having t>=2; let their number be N_0<=N.

Windows on the SAME side are disjoint. All their terminal rail FF edges
are active at the same near-boundary cut. Two such edges on different
rows have separation at least three. Separation exactly three would
join their carriers in the same rail bank. Thus rows belonging to two
different selected banks have separation at least four. A run with a
rail at every third level cannot be interleaved by another such run:
an interleaving row would be within distance two of a run rail, or
coincide with it. The marked row intervals are consequently disjoint
and separated by at least four. Enlarging each by its two outer
off-levels still leaves the J windows disjoint.

The h_J witnesses therefore use different open-side boundary holes.
The z_J witnesses use different inward vertices. Across adjacent sides
these inward witnesses are also disjoint: on the right they have x=A-1
and row in `[2,A-2]`, whereas on the top they have y=1 and column in
`[2,A-2]`, and similarly for the other sides. The deliberately excluded
outer off-level isolate positions avoid all four inner-corner collisions.

Pure boundary carriers need one extra accounting step: a long pure
carrier may meet two disjoint windows on its own side. With N_s windows
on that side, its total repeated occurrences, summed over all carriers,
are at most N_s-1. Indeed every repeated occurrence crosses an intervening
gap between consecutive windows, and at most one actual pure carrier
can cross a particular gap. A pure carrier cannot skip an intermediate
window while continuing along the same side. Open-side windows on
different sides cannot meet the same pure carrier, even at corners.

Let R_pay be the sum of the following ORIGINAL units, counted only once:

```text
the union of the h_J boundary-hole witnesses;
the union of the z_J global isolate witnesses;
the actual pure-boundary carriers meeting the windows.
```

The pure singletons in the last line use r_1; the other pure carriers
use their protected units in Q_roots. The first two lines use b and
the isolate part of c. These are separate resources of (26), so

```text
0<=R_pay<=R_av.
```

Assign each repeated pure-carrier coupon to just one requesting window.
The lost occurrences cost at most N_0, a conservative allowance including
the empty-side cases. Summing (33) proves the simultaneous result

```text
sum_(B selected) D_B <= R_pay+6N <= R_pay+78.        (34)
```

All numbers of carrier roots inside the windows are unrestricted.
There is no error proportional to their counts or to their widths.
The available resource after this allocation is `R_av-R_pay`, not
another copy of R_av. In particular a pure spine used to supply paths
for one bank can also be a boundary witness elsewhere only through its
single, explicitly owned protected coupon.

### Exact Unclosed Case

This is a joint metric payment, but not a proof that every wide bank is
exposed. Let U be the remaining positive-height wide banks after applying
(34). Height-zero wide banks have v_B=q_B=1 and empty R_B, so they
have zero packet demand; their protected root units are still retained
or explicitly spent in R_pay as above.

The direct small-bank allocation and (34) give the unconditional
parameterized inequality

```text
3X_2/A <= K+6N
          +sum_(B in U) [3X_B/A-(v_B-q_B)]
          -(R_av-R_pay).                           (35)
```

One can upper-bound the remaining packet area by the SINGLE-COVERED
union of the remaining R_B, using the source's exact box discount. A
sufficient remaining comparison is therefore

```text
|union_(B in U) R_B|/A
 <= sum_(B in U)(v_B-q_B)+(R_av-R_pay)+C_0.          (36)
```

If U is empty, (35) already supplies an absolute metric error at most
78. Equation (36) is NOT proved when U is nonempty. The advance is that
the entire family of exposed banks, including arbitrary root multiplicity
at perpendicular boundary spines, has now been removed with a proved
simultaneous price. Equation (35) is the remaining ledger after that
payment, not a claim that its remaining signed term is bounded.

There are two precise ways a positive-height wide bank can still fail
the exposure hypothesis on every candidate target side:

1. Some regular transverse level has no near-side back FF edge. The
   bank's width is a union span; individual rails may end on a moving
   interior interface. The number of such missed levels is not bounded
   by the number of banks. No assumption that they cost only O(1) each
   bank is made.
2. All those FF edges exist, but their root vertices are connected only
   through the target-side strip, or are not connected at all in the
   complementary induced H subgraph. Deleting that strip can split one
   actual component into order-n pieces. Those pieces are not additional
   c coupons. Whole-bank contraction or a virtual connecting tree would
   invalidate the literal cycle test used in (28).

In particular the unresolved one-sided moving-seam pattern is not
silently paid. Its rails may all root at a height-zero spine on their
near side while their far endpoints stop at varying interior columns.
Choosing the near side can fail the common-root localization; choosing
the opposite side can fail the common near-boundary FF edge. The
low-K assumption and thirteen-bank count have not been shown to force
enough private replacement width for these failures, even after all
box overlap is discounted exactly.

This continuation therefore proves the rooted-window inequality (28)
and the non-reusing global payment (34). It does not prove (36) for
the remaining banks, an unconditional `K>=n-O(1)`, or the requested
unrestricted `f<=T+O(1)` theorem. No new conjecture about a bounded
per-bank deficit is substituted for that missing implication.

Verification: the four-state certificate was checked by enumerating its
33 admissible typed three-letter transitions and verifying (31), including
the exclusion of nonpure marked F units. All 6,778 admissible typed-word
paths of one through four triples also passed the telescoped bound; they
use at most 12 boundary positions. These are finite proof-certificate
checks, not grid optimizations. The spatial deductions and simultaneous
nonreuse have the arbitrary-size proofs above. Whitespace checking passed.
No board was instantiated, no optimization above size 15 (or any grid
optimization) ran, and no Lean command ran. Only this appendix was written;
the previous prefix and all other files were left unchanged.

## Moving Interface And Terminal Width

Date: 2026-09-08. Append-only continuation. The preceding results and their
review status are unchanged. No unconditional constant for every feasible
configuration is proved in this continuation.

There is now an arbitrary-extension theorem for a full-height moving
interface between two actual outer-root systems. The interface need not
be monotone: downward jumps are allowed, and forest acyclicity permits
at most one upward jump of size two. Its terminal regions are not fixed
caps; arbitrary feasible F is allowed there and everywhere else.

For the precise geometry below, on `n=3s+5` with `s>=2`, the conclusion is

```text
K >= 4s-18.                                        (37)
```

Thus this moving-seam geometry cannot occur under K<n when s>=23. In
particular it has an actual constant upper excess at every size:
`K>=n-21`, hence `f<=T+10`. This is not a theorem that every low-K bank
configuration contains such a full-height seam. The residual internal-
terminal and multiple-root cases are identified after the proof.

The completed steps are a root-preserving rise constraint, an exact
total-variation corridor formula, a coefficient-one terminal width
payment using ORIGINAL carrier and sealed-component units, and their
joint allocation. There is no payment per missing contact.

For (37) the direct allocation is rebuilt from the original K units:
the earlier small-bank and exposed-bank payments are not simultaneously
retained. This is an alternative bound on the same actual configuration,
not an extra donation of cap carriers to an already spent bank.

### The Actual Rooted Seam

Put `A=n-1=3s+4`. Use (x,y) coordinates, and suppose integers a_j satisfy

```text
2<=a_j<=A-4, 0<=j<s.
```

Require the following preserved vertices:

```text
left spine:  (0,y), 1<=y<=3s;
right spine: (A,y), 2<=y<=3s+1;

L_j: (x,3j+2), 2<=x<=a_j;
R_j: (x,3j+3), a_j+2<=x<=A-2, 0<=j<s.              (38)
```

Assume H(F) is a forest. All additional preserved vertices, including
the remaining boundary and both terminal regions, are arbitrary. The
spines may extend farther along their sides. Each is part of one actual
pure-boundary carrier.

The L_j and R_j are exactly 2s different actual carriers, including
possible singleton carriers. Here are the endpoint checks needed for
this assertion in an arbitrary extension:

* The holes at x=1 and x=A-1 on their respective attachment levels are
  forced by diagonals against the two spine vertices immediately above
  and below. Thus a tooth cannot extend toward its spine as an F carrier.
* The next seam-side vertex after L_j is diagonal to the first F vertex
  of R_j. The preceding vertex before R_j is diagonal to the last F
  vertex of L_j. Thus neither can extend across the displayed seam gap.
* A nonsingleton tooth cannot extend vertically because carriers cannot
  turn. A singleton tooth cannot extend vertically either: such an
  extension would create two horizontal contact paths to its own spine
  on consecutive rows, closing the height-one, width-two perimeter cycle.
  The stipulated spine ranges contain both adjacent attachment levels.

Consequently the two spines and the 2s teeth supply at least `2s+2`
distinct original r units. This is not a count of carrier fragments
created by restriction.

Keep only each spine path, its horizontal attachment paths, and its
own teeth. They form two vertex-disjoint actual subtrees T_L,T_R of H.
All left paths stop at x<=A-4 and all right paths start at x>=4; their
horizontal rows differ. Thus they do not meet each other's spine or
horizontal paths. No assertion that the two subtrees are different
AMBIENT components is needed.

### Rise Constraint From Real Connections

The rows of R_j and L_(j+1) differ by two. If
`a_(j+1)>=a_j+3`, they have two common preserved columns. The two
vertical forced paths and the two horizontal FF edges form a six-cycle.
Therefore, in every feasible extension,

```text
a_(j+1)<=a_j+2.                                    (39)
```

Equality gives a physical contact at

```text
(a_j+2,3j+4),
```

joining R_j to L_(j+1). The middle vertex is U: if it were F, it would
be diagonal to the preceding F vertex in the nonsingleton L_(j+1),
whose endpoint is a_(j+1)=a_j+2>=4. These contact holes and their two-edge paths
are distinct for different j, and their interiors are outside T_L,T_R.
Two such contacts would connect the same two vertex-disjoint trees
twice, making a literal cycle in H. Hence equality in (39) occurs at
most once. If a separate existing path already joins the trees without
using these contact paths, it occurs zero times, but that stronger
assumption is not used.

In particular

```text
sum_j max(a_(j+1)-a_j,0) <= s,
a_(s-1)-a_0 <= s.                                  (40)
```

This is the coefficient-one drift allowance, plus just one exceptional
extra step for the entire pair of root trees. It does not contract rail
banks or count ghost cycles as forced cycles.

Missing contacts do not receive individual payments. In particular the
ordinary slope-one seam has no contacts of the displayed kind; (40)
still permits an arbitrarily long such seam. The terminal widths, not
the number of missing contacts, will pay it.

### Exact Moving-Strip Area

Let `V=sum_j |a_(j+1)-a_j|`. For adjacent left teeth, the common FF
length is `min(a_j,a_(j+1))-2`. For adjacent right teeth it is
`A-4-max(a_j,a_(j+1))`. Zero lengths are retained as zero.

The physical rail-to-corridor bijection therefore gives exactly

```text
X_seam=(s-1)(A-6)-V.                               (41)
```

These are actual straight cells and their disjoint width-three packets,
not the sum of two bank rectangles. The corresponding carriers were
proved immutable above, so an arbitrary extension does not lengthen
these overlaps or identify these carriers.

Let V_+ and V_- be the upward and downward variations. Equation (40)
and the coordinate range imply

```text
V=2V_+ +a_0-a_(s-1) <= 2s+A-6=5s-2.
```

Thus even all additional corridor packets outside (41) have only
absolute normalized area:

```text
3(X_2-X_seam) <= A^2-3X_seam
                =39s+10+3V <=54s+4 <18A.           (42)
```

This observation is not needed to replace the global K ledger. It does
show why this is a full-height moving-strip result rather than a local
cap example with an uncontrolled quadratic outside region. Neither V
nor the extra packets are added as independent clean-bank credit.

### A Five-Row Terminal Certificate

The terminal estimate used below is also a specialization of the
variable-rail theorem in `PAPER_FAULT_LINE_ANALYSIS.md`. Here is a complete
smaller certificate for the needed case, so the uniform deduction can
be checked without relying on a finite list of strip optima.

On a five-row vertex rectangle with W columns, let row 3 be U and row 4
be F throughout; rows 0,1,2 are arbitrary. If its actual forced graph
is a forest, then

```text
f_rectangle <= 2W+2.                               (43)
```

Suppress a row-3 vertex when row 2 above it is F, making an edge from
row 2 to row 4; otherwise it is a leaf of row 4 and can be deleted.
Keep the four frontier vertices on rows 0,1,2,4, including all their U
vertices. Write the upper three F bits in that order as a word m.
The row-4 bit is always one. Within one column the reduced edges are

```text
0--1 if m_0 or m_1;
1--2 if m_1 or m_2;
2--4 if m_2.
```

Between columns an edge on a retained row exists if either endpoint is
F. A state records m and the connectivity partition of the four current
vertices, encoded as a restricted-growth string. To append a column,
start with the old equivalences and four new vertices, add the horizontal
edges and then the displayed within-column edges, rejecting an edge
whose endpoints are already connected. Restrict to the new frontier.
This is exact forest recognition, not an added edge between root labels.

The successor columns below have word order

```text
000 100 010 110 001 101 011 111.
```

Their initial state IDs are respectively
`8,12,14,16,18,19,20,21`. A dash is rejection. This table includes all
initial states and is closed under every accepted transition.

```text
ID word part P | successors
 0 000 0000 1 | 8 10 13  -  -  -  -  -
 1 000 0010 0 | 8 10 13  - 18  -  -  -
 2 000 0012 0 | 8 12 14  - 18 19 20  -
 3 000 0100 0 | 8 10 14 15  -  -  -  -
 4 000 0111 0 | 8 12 13 15  -  -  -  -
 5 000 0120 0 | 8 10 14 15 18  - 20  -
 6 000 0121 0 | 8 12 13 15 18 19  -  -
 7 000 0122 0 | 8 12 14 16  -  -  -  -
 8 000 0123 0 | 8 12 14 16 18 19 20 21
 9 100 0000 1 | 5 10  -  -  -  -  -  -
10 100 0010 1 | 5 10  -  - 17  -  -  -
11 100 0011 0 | 8 12  -  -  -  -  -  -
12 100 0012 0 | 8 12  -  - 18 19  -  -
13 010 0000 1 | 6  - 13  -  -  -  -  -
14 010 0001 0 | 8  - 14  -  -  -  -  -
15 110 0000 1 | 1  -  -  -  -  -  -  -
16 110 0001 1 | 2  -  -  -  -  -  -  -
17 001 0000 1 | 7  9  -  -  -  -  -  -
18 001 0111 0 | 7 11  -  -  -  -  -  -
19 101 0000 1 | 3  9  -  -  -  -  -  -
20 011 0000 1 | 4  -  -  -  -  -  -  -
21 111 0000 2 | 0  -  -  -  -  -  -  -
```

For a new word put `w(m)=|m|-1`, its preserved count INCLUDING the full
rail vertex minus two. The table verifies

```text
w(m)<=P(initial(m)),
P(old)+w(m)<=P(new),       0<=P<=2.
```

Induction over all W columns gives
`f_rectangle-2W=sum w(m)<=2`, proving (43) at arbitrary width.
There is no first-facing restriction on row 1 in this certificate:
horizontal FF runs there are retained, rather than assumed absent.

### Coefficient-One Terminal Width In Original Units

Suppose an actual horizontal carrier on row 4 above a physical boundary
row 0 contains the vertex interval I=[u,v], of length ell. For ell>=3,
restrict to the five-row rectangle on the STRICT interior columns
`u+1,...,v-1`, so W=ell-2. Row 3 is U by diagonal exclusion against the
full rail, so (43) applies. Its exact rectangular ledger gives

```text
K_rectangle=7W+10-3f_rectangle >= W+4.              (44)
```

Use the following ORIGINAL resources:

* h counts holes on the physical boundary over these interior columns.
* p counts actual pure-boundary carriers meeting that boundary interval.
* d counts all actual carriers other than those in p that meet rows
  0,1,2 of the window.
  Long horizontal carriers on row 1 are included; their units are not
  falsely called short-carrier or already-refunded units.
* c_closed counts components of the restricted forced graph that meet
  neither longitudinal end column.

Every component counted by c_closed is an actual global H component.
All row-3 vertices attach to the full row-4 path, which reaches both end
columns. Thus a closed component avoids rows 3 and 4. It avoids the two
end columns, has no neighbour above the board, and has no forced exit
through row 3. There is no possible external attachment. The components
are distinct, including any globally isolated vertices among them.

The remaining local component count is at most ten, since every other
component contains one of the ten end-column vertices. Also
`b_rectangle<=h+10`: the bottom rail has no holes, and the two artificial
short sides contribute at most ten units in total. Convexity of actual
straight carriers gives `r_rectangle=1+p+d`; their intersections with
the rectangle do not split into several F components. The one is the
full rail carrier. These bounds also cover W=1.

Combining with (44) proves

```text
ell <= h+p+d+c_closed+19.                           (45)
```

For ell<=2 use the same inequality with no requested resources. Its
constant is deliberately not optimized.

This is a coefficient-ONE width payment with arbitrary filling and
arbitrary connectivity elsewhere. It does not spend restricted
components that can reconnect outside. Nor does it use a free long
guillotine interface: local r and c were mapped directly to original
carriers and genuinely sealed components, with every remaining end
component charged to the constant-size end columns. The full rail is
what makes this mapping possible. No inequality for a second rectangle
or its artificial K budget was retained.

For a parallel rail at distance TWO from the physical boundary, there
is an even simpler width payment. Over any common interval of at least
two rail vertices, the intervening row is U and the boundary has no FF
edge, by the six-cycle exclusion. Every preserved boundary vertex in
that interval therefore belongs to a different pure carrier, including
pure singletons. Thus

```text
ell = h+p.                                         (46)
```

A length-one interval can instead be discarded for one constant unit.

### Joint Payment Of The Moving Seam

Return to (38). The first left tooth is on row two, and the last right
tooth is four steps above the opposite boundary. Their vertex lengths
are

```text
ell_L=a_0-1,
ell_R=A-a_(s-1)-3.
```

By the actual root-forest drift bound (40),

```text
ell_L+ell_R=A-4+a_0-a_(s-1) >= A-4-s=2s.           (47)
```

Apply (46) at the first terminal, with its one-unit allowance when
ell_L=1, and (45) at the last terminal. These resource sets are private
together:

* Their physical boundary holes lie on different open sides.
* Their pure-boundary carriers lie on different open sides and are
  distinct from the two vertical root spines.
* The carriers d in the second cap meet its last three rows. They are
  distinct from all 2s immutable teeth, whose rows stop at A-4, and from
  both spines, whose columns are outside the cap window. They are also
  distinct from the first terminal's pure-boundary carriers. Row A-3 is
  U over this window, so an interior vertical cap carrier cannot extend
  to that opposite boundary.
* The c_closed units are actual global components and are counted once.
  They are not the row-4 component, which meets the end columns.

Let R_term be the sum of these original r, b, and c units. Equations
(45)--(47) give

```text
R_term >= ell_L+ell_R-20 >=2s-20.
```

The 2s tooth carriers and the two root-spine carriers have not been used
in R_term. Therefore

```text
K >= (2s+2)+R_term >=4s-18,
K-n >= s-23 >=-21.                                 (48)
```

This proves (37) and its stated constant-gap consequence. Nothing was
assumed about the number of other carriers or components. In particular
one may not omit d from (45) when testing a proposed completion, but
those d units really are available in (48), because this proof reserved
the original core/spine units and did not previously spend the cap
carriers on some other bank's area.

### What This Does And Does Not Globalize

The moving-strip payment is substantive: a full-height slope-one seam,
all its permitted downward perturbations, and a possible single
two-column rise cannot evade the bound by arbitrary terminal repacking.
The proof uses terminal widths that telescope as in (47), not a fresh
donation for each missing seam contact. The exact area formula (41)
also explains why the small per-link gaps alone were too weak: their
normalized total variation loss can be only O(1).

The finite-wide-bank reduction does NOT yet force (38). It can have
several partial seams whose endpoints lie at other wide banks rather
than at the physical boundary, a changed phase at a terminal, or level
pieces that do not share the two displayed actual root trees. The
coefficient-one payment (45) uses a PHYSICAL boundary on one side. At
an interior interface, its h vertices are not original b units, and its
formerly closed components may escape through that side. Giving them
the same price would be the forbidden free-interface step.

Likewise, if the two actual root trees are replaced by many root
clusters, repeated two-column rises need not create the same two-tree
cycle. Ghost edges joining clusters merely produce cycles in an
augmented graph, not in H. No allocation from actual c or refunded
carrier units has been proved for that change of hypothesis.

Thus the remaining global obligation is specific: expose terminal
widths of the internal, partial seam network and transport their
coefficient-one payments to original boundary/carrier/component
resources, without charging an internal boundary hole or a split root
component as fresh credit. The number of wide banks is bounded, but
the number of unlocalized root pieces or missed rail levels need not
be. No uniform O(1) price for each bank pair is assumed here.

No unrestricted `f<=T+C` follows from this continuation. The completed
new theorem is (48), valid in every feasible EXTENSION of the explicit
full-height rooted moving-seam skeleton, together with the independently
usable original-resource terminal width theorem (45). The internal-
terminal/root-cluster transport needed for the general finite-bank
configuration remains unproved.

Verification: the fixed-rail frontier has four vertices, 22 reachable
states, and 70 accepted transitions. Its reachable state set closed
within four columns; the complete table, initialization, and all
potential inequalities were checked directly. Other exploratory local
state checks used at most five frontier vertices and closed within four
columns. They showed why dropping closed-component or middle-carrier
charges is not a valid automatic payment. These are finite transition
checks, not optimizations of a board larger than 15. The arbitrary-size
proofs are the cycle arguments, displayed certificate, and resource
injections above. A further 1,074 direct skeleton/extension checks on sides
11 and 14 verified the one-extra-rise forest criterion and its stricter
five-hole-frame version. All 301 feasible cases also passed actual carrier
immutability, the original ledger, the variation bound, and (42). These
checks optimized no configuration and do not replace the uniform proofs.
No Lean command ran, and only this appendix was written.

## Root Hulls And Interior Escape Transport

Date: 2026-09-08. Append-only continuation; the moving-seam theorem above
is left unchanged while under review. Read the new Moving Physical Strip
continuation of `PAPER_CLEAN_ALLOCATION.md`, including its common-root
forest and simultaneous telescope. No unconditional constant-gap theorem
is proved in this pass.

The completed deductions address three different parts of transport:

1. A canonical root decomposition uses only restored ACTUAL event paths.
   It gives a 24-unit root term without assuming connectivity in the
   deleted-event forest, but with two explicit, not-yet-paid defects.
2. Every fixed pair of parallel banks has a coefficient-one metric
   contact price from private endpoint insets. This holds without any
   root-connectivity hypothesis and includes fragmented banks.
3. An interior terminal window has an exact additional escape demand.
   Its escaping components are kept in the frontier partition, not
   counted as globally sealed components.

These are uniform deductions. They do not show that the two root defects
or the escaping interface demand have bounded total cost. In particular
they do not replace those terms by O(1) just because there are at most
thirteen wide-bank colors.

### The Common Event Forest

Use any nonempty collection of physical moving strips satisfying the
NONREUSE hypotheses in the allocation note: disjoint gap coupons and
event-path interiors, and no repeated named stripe baseline. This is
an input to the present argument, not a decomposition theorem for all F.

Let p count the singleton-supplier paths and u the upward-two contact
paths. Delete all their internal vertices simultaneously, as in that
note. Contract each resulting actual H component meeting a selected
rail, and restore the paths as edges. Call the resulting graph Q.

Q is a forest. Its vertices are actual deleted-event components, not
rail banks. If m is its vertex count and c_R its component count, then

```text
|E(Q)|=p+u=m-c_R.                                  (49)
```

Here c_R is exactly the number of ambient H components meeting the
selected rails. The equality uses the proved event-path degrees and
the fact that their other neighbours are pendant leaves. Every Q
vertex contains at least one selected rail.

Give a Q vertex all bank colors occurring among those rails. A vertex
may have several colors, and one color may occur at many vertices.
Let q be the number of occurring colors; in the wide-bank reduction
q<=13. Color does not mean connectivity.

### Canonical Restoration, Not Ghost Contraction

Within each tree of Q, take the unique paths between vertices having
the same bank color. Let E_H be the UNION of their edges, over all
colors and trees. An edge occurring in several such paths is retained
only once. Let p_H,u_H be the numbers of the two event types in E_H.
Write p_F,u_F for the remaining event counts.

E_H is exactly the minimum set of event edges that must be restored
to connect every bank's roots WITHIN each ambient H component:

* Necessity: deleting any edge of a unique tree path disconnects its
  endpoints. A restoration connecting those equal-colored roots must
  contain every edge of their path.
* Sufficiency: their entire paths are present in E_H by definition.

There is no path between different ambient components, and no ghost
edge is introduced to create one. Realizing E_H means restoring the
original two- or four-edge paths and their actual vertices in H.
Its connected pieces can therefore be contracted legitimately.

Let m_H be the number of root vertices after this contraction. Since
E_H is a subforest,

```text
m_H=m-p_H-u_H,
p_F+u_F=m_H-c_R.                                   (50)
```

All occurrences of a bank color within an ambient tree now lie at one
contracted vertex. Different colors may lie at the same vertex. If q_C
is the number of bank colors present in ambient component C, this gives

```text
m_H-c_R <= sum_C(q_C-1).                            (51)
```

This is the safe root decomposition: only actual connected subtrees
were contracted, and actual ambient components stayed separate.

### Where The Bounded Root Term Ends

Form a bipartite INCIDENCE graph with the q bank colors on one side and
the c_R actual ambient components on the other. Put one edge for each
bank/component incidence. Let gamma_I be its component count and beta_I
its cycle rank. This graph records incidence only; it is not asserted
to be a subgraph or minor of H. Exactly,

```text
sum_C(q_C-1)=q-gamma_I+beta_I <= q-1+beta_I.         (52)
```

Keep the signed price of the mandatory restored events:

```text
H_price=2p_H-u_H.
```

The original moving-strip coupon inequality has the form

```text
sum t <= sum(a_last-a_first)+z_Gamma+3p-u.
```

After spending the p actual singleton units just once, its remaining
event price is 2p-u. Equations (50)--(52) give the exact decomposition
and its bound

```text
2p-u = H_price+2(m_H-c_R)-3u_F
     <= 2(q-1)+2beta_I+H_price-3u_F.                (53)
```

Thus the topological part that really is bounded by the bank count is
at most 24. The two additional defects are explicit:

```text
2beta_I,        H_price=2p_H-u_H.                   (54)
```

Neither defect is declared nonnegative or paid; H_price should retain
its sign. In particular mandatory restored contact paths help rather
than hurt. Mandatory restored singleton paths cost two MORE units here
because their original singleton unit has already been used in p.

If all selected rails lie in one ambient H component, beta_I=0. If, in
addition, the mandatory restoration uses only contact events, H_price
is nonpositive. Then (53) really gives a root error at most 24 without
assuming that each bank was connected in the original T_ext. This is
a proved consequence of actual restoration, not assumed connectivity.

For general configurations, beta_I need not vanish. Even though each
ambient component is counted once as a vertex, it can contain several
bank colors. Replacing `sum_C(q_C-1)` by c_R would be an unjustified
change of coefficient. Cycles of the incidence graph are not forced
cycles in H. Similarly, the required E_H paths cannot be selected away
by a different spanning-tree choice: they are unique paths in a forest.

Substitution into the allocation note's common strip certificate gives
the following valid replacement of its root term:

```text
3X_2/A <= K+6N+24
          +sum(a_last-a_first)-3J_loss/A-R_unused-R_rest
          +2beta_I+H_price-3u_F.                    (55)
```

All notation and nonreuse assumptions other than the new root
decomposition are those of that certificate. In particular z_Gamma and
p have already been subtracted from R_rest. They are not available to
pay (54) a second time. Equation (55) is a parameterized inequality,
not a global bound on its unpriced terms.

### Repeated Parallel Contacts Have A Full Metric Price

There is a geometric restriction on repeated color-pair contacts which
does not use (49)--(55). For a nonsingleton carrier C with axial vertex
interval [l_C,u_C], give its two physical axial ends the inset slots

```text
d_left(C)=l_C,
d_right(C)=A-u_C,
D_C=d_left(C)+d_right(C)=n-|C|.
```

For a bank B put `D_B^span=sum_(C in B) D_C`. This is a measured carrier
length deficit, not an additional copy of an r unit. Let m_BD count all
actual contact-forest edges between two DISTINCT banks B,D with parallel
axes. Put epsilon_BD=1 when they have the same transverse residue modulo
three, and zero otherwise. Then

```text
(A+2epsilon_BD)m_BD <= D_B^span+D_D^span.            (56)
```

Proof for horizontal banks; rotate for vertical ones. A contact is
either between collinear carriers across one U vertex, or between rows
at distance two with a common F column.

In the collinear case the facing endpoints have coordinates x and x+2.
Their outward inset slots sum to `(A-x)+(x+2)=A+2`. Such a contact can
only occur between banks with the same transverse phase.

In the distance-two case, the two carriers' F intervals have only one
common column: two common columns would give the six-cycle between
parallel rails. Because both carriers are nonsingletons, this common
column is an endpoint of each, and they extend in opposite axial
directions. At its coordinate x the two outward insets sum to
`(A-x)+x=A`. These banks have different transverse phases.

For a FIXED pair of different phases, the row shift is uniquely either
+2 or -2. A given axial carrier end therefore has at most one contact
to that bank: the possible neighbour row and the F vertex on it are
both fixed. For equal phases only the unique collinear outward contact
is possible. Thus no endpoint slot is used twice within the fixed bank
pair. Summing the displayed exact slot weights proves (56), including
arbitrary numbers of same-level fragments. No matching loss is needed.

There is a safe simultaneous version. Choose nonnegative weights theta_BD
on parallel bank pairs with

```text
sum_(D paired with B) theta_BD <=1 for every B.
```

Then

```text
nr-f >= sum_B D_B^span
      >= sum_pairs theta_BD(A+2epsilon_BD)m_BD.     (57)
```

The first sum here is over the banks used in the weighted selection.
Each bank's deficit is used with total coefficient at most one. One
can instead impose the sharper individual endpoint-slot capacities,
but cannot set every theta to one without checking them. An endpoint
may contact more than one other bank through different holes.

For example, writing
`M=sum theta_BD(1+2epsilon_BD/A)m_BD`, the original ledger and (57)
prove the actual unrestricted metric consequence

```text
(3n+1)K >= n^2+4n+3n(b+c)+3A M.                    (58)
```

This is a full-coefficient price per selected parallel pair. It is not
a proof that a sufficiently large non-reusing selection always exists.
Nor may D_B^span/A be inserted into R_rest as fresh money while retaining
all the carrier capacity from which it was measured.

In particular the positive part of H_price is not covered automatically
by (56). Its singleton paths are four-step bridges, not direct contacts
between parallel nonsingleton carriers. Their gap-isolate and singleton
coupons are already present in the strip telescope. Perpendicular bank
contacts are different again: an endpoint of one carrier may attach to
an interior point of the other, so the opposite-inset equality used in
(56) is unavailable. A height-zero perpendicular spine can have many
such contacts.

### Interior Terminals With Their Escape Partition

The terminal theorem (45) has a precise interior version. Place its
five-row rectangle at an interior location, still with a full F rail
on row 4 and row 3 U, and clip its longitudinal ends as in that proof.
The row named 0 is now an INTERIOR face, not the physical board boundary.

Let d_cap count the actual carriers meeting its first three rows, and
let h_face count the U vertices on that face. Among restricted H
components avoiding both longitudinal end columns, separate:

* c_sealed: components having no forced exit through the interior face;
* c_escape: components having at least one actual forced edge through
  that face to the outside.

The full row-4 component meets both end columns, and every row-3 vertex
joins it. Thus components in the displayed two classes avoid rows 3,4.
Those counted by c_sealed are genuinely global H components. Those
counted by c_escape are not given global component coupons.

The other local components number at most ten, by their distinct
end-column vertices. The same rectangular calculation as (44)--(45)
therefore proves

```text
ell <= d_cap+h_face+c_sealed+c_escape+19.            (59)
```

This is the correct local starting point for interior transport. At a
physical boundary c_escape is zero and h_face is original boundary
deficiency. At an interior face neither substitution is valid.

One can preserve the escape data exactly: retain the restricted
components on both sides, all actual crossing forced edges, and their
incidence partition. Contracting those CONNECTED components gives a
forest. If the two side-component counts are c_in,c_out and the number
of crossing forced edges is e_cross, then

```text
c_in+c_out=c_global+e_cross.                        (60)
```

Here outside means the entire complementary vertex set. The count
e_cross includes the end and bottom interfaces as well as the named
interior face; (60) must not be applied to just some of the crossing edges.

For a larger sequence of interfaces the same statement follows by
deleting all crossing edges of H at once. It counts every resulting
piece, and every restored forced edge, once. It does not turn each
piece encountered during transport into a new ambient component.

The corresponding full K ledger still has the exact two-unit interface
price per grid edge recorded earlier in this note: a U--U edge creates
two artificial hole units; an F--U edge creates a hole unit and a forced-
component split; an F--F edge creates a carrier split and a forced-
component split. Each case totals two. Equations (59),(60) retain this
frontier information instead of spending it as original b or c.

### Unfinished Global Payment

The new root decomposition removes the need to GUESS a root partition.
It identifies the unique mandatory restorations and separates the
bounded color term from `2beta_I+H_price-3u_F`. The parallel contact
bound gives a real spatial price for one important repeated-pair case.
The interior terminal bound explicitly keeps all escaping components.

These facts do not yet yield the required transport inequality. Three
unpaid quantities remain, in addition to the still-unproved general
non-reusing strip decomposition:

1. The signed terminal displacement sum. An internal terminal need not
   be the physical-boundary terminal paid in (45); (59) contains the
   additional h_face and c_escape demands.
2. Mandatory restored singleton bridges in H_price. Their original
   singleton coupons and private gap-isolate coupons have already been
   allocated. The full-price direct-contact lemma does not cover them.
3. Repeated bank/component incidences beta_I. The incidence cycles are
   not physical cycles. Charging every incidence to its component would
   spend a single original c unit several times.

Transport through paid small banks also has to use their ACTUAL remaining
refund, not their original carrier count. Their being called one color,
or their packets already being paid, does not connect their separated
root pieces or remove c_escape from (59).

No bound by an absolute constant has been proved for the sum of these
unpaid quantities after the legitimate resources are deducted. Thus
(53), (56)--(60) are rigorous deductions and accounting restrictions,
but the unrestricted `K>=n-O(1)` and `f<=T+O(1)` conclusions remain open.
No whole-bank contraction, free interface, or O(1)-per-pair error has
been assumed to obtain them.

Verification scope: these results have the tree-path, endpoint-coordinate,
and frontier-partition proofs above. The restoration/incidence formulas
also passed 500 abstract-forest checks on at most thirteen vertices;
these supply no grid-realizability evidence. Four explicit forced forests
on sides 11 and 14 attained equality in (56), testing both collinear
contacts and distance-two contacts, including two contacts using opposite
ends of the same carrier. No optimization, grid search, or Lean command
was run for this appendix. Only this appendix was written; the previous
text and all other files were preserved.

### Additional Port-Transport Check

The concurrently written `PAPER_TERMINAL_TRANSPORT.md` was read after
the arguments above. Its exact port lemma supplies another necessary
safeguard. For balanced signed loads alpha_i at ordered ports x_i of
one actual carrier, with `S_j=sum_(i<=j) alpha_i`,

```text
sum_i alpha_i*x_i = -sum_j S_j*(x_(j+1)-x_j),
minimum longitudinal transport = sum_j |S_j|*(x_(j+1)-x_j).
```

Consequently a legitimate contraction of a CONNECTED root hull is only
a topological operation, not a metric isometry. Even unit loads on its
contact edges do not imply bounded cumulative loads S_j along its
carriers. The restoration proof of (53) makes no such metric claim:
the terminal displacement remains explicitly unpaid in (55). Any
future attempt to cancel it through those connected hulls must retain
this longitudinal term or prove that the actual geometric seam loads
have a non-reusing payment for it. The bank count alone is not that
proof.

## Final Fragment And Front Test

Date: 2026-09-08. Append-only final test of the proposed joint fragment
payment. All earlier text is preserved. No unconditional constant-gap
theorem is obtained.

The proposed COUNTING step is valid. A bank with `v=a+1+s` carriers has
an edge-disjoint transverse-monotone decomposition of its actual
corridor-adjacency graph into at most s+1 paths. Its internal rail-graph
cycle rank is at most s. There is also a canonical geometric boundary
construction with at most 2s+2 side fronts and 2s+2 transverse-extremum
caps. Its total unweighted axial length is controlled by the already
proved cut-fragment integral, globally with no factor depending on s.

What fails is the proposed automatic conversion of those bounds into a
unit-priced packet terminal payment. The physical moving-strip telescope
contains UNNORMALIZED phase displacement. A unit geometric front is not
proved to carry that debt with unit load. In addition, bank/component
incidence cycles are not controlled by the internal bank cycle rank;
the existing nested-frame family has s=0 in every bank and growing
incidence rank. Both distinctions are made explicit below.

### Adjacent-Level Overlap Forests

Fix one bank B and suppress its subscript. Orient it horizontally for
notation. Its transverse levels are `y_0+3i`, `0<=i<=a`. Let m_i count
the carriers on level i. Then

```text
sum_i m_i=v=a+1+s,     m_i>=1.
```

Use each carrier's actual FF interval `[l,u)`, of positive edge length.
At one level these intervals are disjoint. The bank graph joins carriers
on adjacent levels when their FF intervals overlap in positive length.

The bipartite graph between any two adjacent levels is a forest. To
prove this, choose a remaining interval with smallest right endpoint.
If it had two neighbours on the other level, order those two disjoint
intervals from left to right. The first would end before the second
starts, and the second starts before the chosen interval ends. Thus the
first neighbour would have a smaller right endpoint, a contradiction.
The chosen vertex has degree at most one. Repeating proves acyclicity.

Let kappa_i count ALL components of this two-level graph, including
isolated carrier vertices, and let e_i be its edge count. Therefore

```text
e_i=m_i+m_(i+1)-kappa_i.
```

Write e for the number of bank edges and beta_bank=e-v+1 for the bank
graph's cycle rank. Summing the last equality gives the exact formula

```text
beta_bank
 =s+2-m_0-m_a-sum_(i=0)^(a-1)(kappa_i-1)
 <=s.                                               (61)
```

The bank graph is connected by its definition; that is the connectivity
used here. This graph is not the carrier CONTACT forest. When a=0 the
bank has one carrier and no edges, and the conclusion is immediate.

### At Most s+1 Monotone Skeleton Paths

Orient every bank edge toward the next higher level. Pair as many
incoming and outgoing edges as possible at each carrier. A deterministic
choice is to order the two edge lists by their neighbour intervals and
pair the first min(indegree,outdegree) entries. These pairings partition
all edges into directed paths. Directed cycles are impossible because
every edge increases the level.

Here is a sharp bound on their number, not a bound that loses another
copy of beta_bank. Let tau_i count the NONTRIVIAL components of the
adjacent-level overlap graph, and put

```text
Q_if=sum_i tau_i.
```

Each interface has an edge, since otherwise the bank would disconnect,
so Q_if>=a. Let T_through count carriers with positive indegree AND
positive outdegree. All other carriers occur in just one nontrivial
interface graph; a through carrier occurs in two. Summing the forest
edge counts over those interface components consequently gives

```text
e=v+T_through-Q_if.
```

The number P of paths produced by maximal local pairing is

```text
P=e-sum_C min(indegree(C),outdegree(C))
 <=e-T_through
 =v-Q_if <=v-a=s+1.                                (62)
```

Thus there are at most `2s+2` skeleton path endpoints. A one-carrier
bank may be given one trivial path. A two-level star, with one long
rail facing s+1 separate fragments, attains P=s+1, so the coefficient
cannot be improved on the basis of this geometry alone.

The paths can be placed geometrically. For each bank edge choose a
point inside its actual common FF interval, cross the corresponding
width-three corridor band there, and connect successive crossing points
along their common carrier. Each resulting path is transverse-monotone.
These are geometric paths derived from the rails, but their cross-band
segments are virtual: they are not asserted to be paths in H. Different
skeleton paths may also use the SAME carrier, or overlap longitudinally
on it. Edge-disjointness in the bank graph is not a carrier-slot or
transport-capacity assertion.

Monotonicity here is in the transverse level, not in both coordinates.
One interval on every three-spaced row, with a common left endpoint and
oscillating right endpoints, is a feasible collection of disjoint rod
supports. Its bank has s=0, but its right side front can have arbitrarily
many axial reversals. Thus a bound on AXIALLY monotone front pieces
does not follow from (62). The low-K variation bound below is a different
statement and does not bound the number of reversals.

### Actual Side Fronts And Their Total Axial Length

There is a separate geometric construction that does give non-reusing
boundary arcs. In the coordinates of B, thicken each FF interval
`[l_C,u_C]` to the rectangle

```text
[l_C,u_C] x [y_C-3/2,y_C+3/2].
```

This is an auxiliary ribbon constructed from actual carrier coordinates,
not an assertion about preserved vertices or H components. To avoid
spurious point connections, first replace each axial interval by
`[l_C+epsilon,u_C-epsilon]`, `0<epsilon<1/4`, and then take the limit
as epsilon decreases to zero. All positive FF overlaps remain, and
zero-length endpoint contacts do not join ribbons. No integer-area
error or new component coupon is introduced by this convention.

The union ribbon is connected. At the interface between two transverse
levels, a nontrivial overlap component with b upper intervals creates
b-1 new upper gaps. Each gap gives one horizontal cap with two side
fronts starting upward from its ends. An isolated upper interval creates
one such pair as well. All other upper boundary tracks continue from
below. Thus the number of new upward front pairs at interface i is

```text
m_(i+1)-tau_i.
```

This count is geometric: within a connected overlap component, any gap
between successive upper intervals is covered by the lower intervals;
otherwise its interval-overlap graph would disconnect. The two outer
tracks continue, and every internal upper gap accounts for one new pair.

Including the bottom level, the total number of upward front births is

```text
B_up=m_0+sum_i(m_(i+1)-tau_i)=v-Q_if<=s+1.           (63)
```

The downward/end count is the same, by reflection. Removing the local
minimum and maximum horizontal caps leaves at most `2B_up<=2s+2`
transverse-monotone SIDE FRONTS. There are also exactly 2B_up extremum
caps, counting the outer bottom and top caps. Caps and fronts partition
the ribbon boundary; boundary edge length is not reused.

These side fronts are not identified with the skeleton paths in (62).
In particular they have up to 4s+4 individual endpoints. One cannot take
the smaller endpoint count from (62) and the non-reusing boundary arcs
from (63) as if they were one proved construction.

The axial metric of this boundary is especially useful. At an axial cut
the ribbon has exactly p_B(t) transverse components, the same actual
cut-forest component count used in (4)--(5). Its horizontal boundary
has two intersections per component. Integrating, and then taking the
epsilon limit, gives exactly

```text
horizontal boundary length of B = 2 sum_t p_B(t).   (64)
```

This length includes all hole boundaries and all extremum caps. Therefore
the total axial variation along the side fronts, PLUS the cap lengths,
is at most this same quantity. Summing over both orientations and every
bank, the prefix's low-budget estimate proves

```text
sum_all_banks (front axial variation + cap lengths)/A
 <=2P_cut/A <10n/(n-1)<=11,  when K<n and n>=11.     (65)
```

This is a genuine geometric, non-reusing front bound. It does not come
from arbitrary balanced port loads. It also does not say that the debt
in the moving-strip certificate is carried by these fronts with the
unit weights used in (65).

### Exact Reservation Of Fragment Units

The proposed reservation can be made, but its exact size matters when
all pure-boundary units remain protected. For a wide bank the current
baseline is

```text
v_B-q_B=a_B+s_B-(q_B-1).
```

If it is reduced to a_B, the newly reserved carrier units number

```text
sigma_B=s_B-(q_B-1)>=0,                             (66)
```

not s_B in addition to the existing q_B protected units. Reserving all
s_B and also all q_B would spend q_B-1 units twice. Equivalently,
`sigma_B+q_B=s_B+1`; this is the total original resource available for
a hypothetical one-unit-per-skeleton-path payment in (62), if those
protected units are not already committed elsewhere.

Start just after the protected SMALL-bank allocation, before making
any later root payments. Let R_0 be its remaining resource R_av from
(26). After reserving (66) on all wide banks, put

```text
R_a=R_0+sum_(B wide) sigma_B.
```

The exact sufficient comparison becomes

```text
sum_(B wide) [3X_B/A-a_B] <= R_a+C.                 (67)
```

There is no gain by reservation alone, since exactly

```text
sum_(B wide)[3X_B/A-a_B]-R_a
 =sum_(B wide)[3X_B/A-(v_B-q_B)]-R_0.               (68)
```

A real decomposition payment could of course prove (67). But reducing
the baseline raises its unpaid area by precisely the units reserved.
Those same units cannot also remain as the old negative fragment term
in the wide-bank demand. The identities specify one joint account;
they are not the missing inequality.

### Why A Normalized Endpoint Is Not Yet A Unit Debt

The actual moving-strip inequality in the allocation note is

```text
t <= (a_t-a_0)+z_Gamma+3p-u.
```

Its terminal displacement is a_t-a_0, NOT `(a_t-a_0)/A`. If a terminal
coordinate is normalized by phi=a/A, the term becomes

```text
A*(phi_last-phi_first).                            (69)
```

Bounding the range of phi by one therefore does not bound that budget
term by one. No change of notation can remove its factor A.

There is an equally direct area check using actual banks. A bank with
one carrier on every level, all of common FF width W, has

```text
s=0, X_B=aW, 3X_B/A-a=a(3W/A-1).                   (70)
```

Its ribbon has just two side fronts and two caps. The normalized total
cap length is only 2W/A, but its packet demand after the a-unit baseline
is order a when W is close to A. In the ribbon area formula, transverse
height is the weight multiplying axial boundary displacement. Unit
boundary length in (65) is not that height-weighted packet area.

This distinction also occurs in the actual rigid moving-strip family
already proved feasible in `PAPER_CLEAN_ALLOCATION.md`, equations
(47)--(48). Its horizontal banks and its two height-zero spine banks
all have s_B=0. The strip has t steps, a_t-a_0=t, and no gap coupons,
yet its actual packet excess over the 2t stripe baseline is

```text
t-21t/(3t+4),
```

which is unbounded. The geometric fronts are simple, and their normalized
coordinate ranges are bounded. The original terminal width still has
its unnormalized price. This family has large K, so it does not refute
a low-K theorem using additional natural resources. It does refute
the LOCAL inference that simple fronts and bounded normalized endpoints
alone give an O(1) packet payment when s=0.

### Incidence Rank Is Not Bank-Graph Rank

The bound beta_bank<=s in (61) concerns edges between three-spaced rails.
It does not bound cycles in the bank/ambient-component incidence graph.
The nested-frame family already established in (16)--(17) gives an
analytic test with no new construction or optimization.

On n=6m+2 there are four banks. The top bank has m+1 carriers on m+1
levels, including the innermost pair; the other three banks have m
carriers on m levels. Hence

```text
s_B=0 and beta_bank(B)=0 for EVERY bank.
```

The m large frames are m different nontrivial H components, each meeting
all four banks. The innermost pair is one further component, meeting
only the top bank. The incidence graph on all these actual carriers has
four bank vertices, m+1 component vertices, 4m+1 incidence edges, and
one connected component. Its cycle rank is therefore

```text
beta_inc=(4m+1)-4-(m+1)+1=3m-3.                    (71)
```

Thus a blanket bound `beta_inc<=sum_B s_B+O(1)` is false, even with
four wide banks and no bank-graph cycle at all. If beta_I is defined
using a more restricted set of selected strip roots, a new theorem
about that selection is required; (71) is not a claim that these frames
already supply the needed moving-strip decomposition.

Again the family is outside K<n and has many genuine isolates. It does
not refute payment from all of r+b+c. It shows why the fragment count
alone cannot pay cross-bank incidence rank, and why virtual rail-bank
connectivity and actual contact connectivity must remain distinct.

### Final Status Of This Route

The final push establishes the requested O(1+s) skeleton count, its
coefficient-one cycle bound, and an actual geometric side-front
construction with a joint low-K axial-length bound. It also gives the
exact fragment reservation needed to avoid spending protected roots
twice.

It does NOT identify the genuine packet terminal debts with unit loads
on those fronts. The existing moving-strip identity shows the missing
scale explicitly in (69). Nor do the front paths lie in H or make
colored root pieces connected. Transferring them to the actual contact
forest would still need the port-congestion and escape payments in the
preceding appendices. Finally, (71) rules out paying general incidence
cycles from s alone.

Consequently no proof of (67) with an absolute C has been obtained, and
the unrestricted constant upper bound remains unproved. The exact new
lemmas are (61)--(66); the failures are the unproved debt-to-front
identification at its correct coefficient, the unchanged deficit in
(68), and the distinction demonstrated by (71). No constant deficit
per front, per bank pair, or per contracted bank is assumed.

Verification: 204 explicit feasible boards on sides 8, 11, and 14
provided 992 bank checks. The inputs were three-spaced horizontal rod
families, two sharp branching-star cases, and the existing nested frames.
They verified the adjacent-level forests, exact cycle formula, path and
front count bounds, axial boundary-length formula, and nested-frame
incidence counts. No preserved-set objective was optimized. The uniform
proofs are the interval-forest counting and geometric boundary arguments
above, not an extrapolation from these checks. No Lean command or
optimization above size 15 ran. Only this appendix was written; the
previous note text and all other files were left unchanged.
