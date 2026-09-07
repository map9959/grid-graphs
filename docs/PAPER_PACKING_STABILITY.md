# Paper Packing Stability

Date: 2026-09-07. Paper deductions and open research obligations, not new
Lean theorems. No builds or computational experiments accompany this note.

## Purpose

The [half-coefficient proof](PAPER_HALF_COEFFICIENT_UPPER.md) gives, on paper,

```text
P(3k+2) <= T(k) + floor(k/2) + 1,  k>=3,
T(k) = 3k^2+7k.
```

The checked repository bound remains `T+floor(2k/3)` for k>=5. The next
objective is an upper excess bounded independently of k, not another endpoint
exclusion. The lower objective is separate; see
[constant-gap lower research](PAPER_CONSTANT_GAP_LOWER.md).

## Unrestricted Scheduling

Put `N=3k-2`, `Q=k-1`, so `N=3Q+1`. Use deep row indices 1 through N,
vertical steps 1 through N-1, and good horizontal rows 2 through N-1.
For every occupied horizontal row y, assign

```text
T_y = [y-1,y+1]  if y = 2 mod 3;
T_y = [y-2,y]    otherwise.
```

Each assignment has three affected steps. Row 2 is shifted, avoiding lower
clipping. The last interior row N-1 is zero modulo three and is unshifted;
the last shifted row is at most N-2. Thus there is no upper clipping.

Rows three apart have the same shift, and rows at least four apart cannot
overlap even with opposite shifts. Only nearby rows can share steps, and
their actual horizontal edge-column sets are disjoint by four-/six-cycle
obstructions. The joint capacity proof therefore works for arbitrarily many
occupied rows. It needs no minority-orientation or high-excess hypothesis.

This exploits N=1 modulo three. It is not a general arbitrary-height theorem.
For height N=3q, q full horizontal rods on rows 2,5,...,3q-1 demand 3q
disjoint assigned steps from only 3q-1 available steps. That different-height
schedule is impossible.

## Exact Good-Edge Loss

At step t, let V_t be the good vertical-edge columns, and let A_t be the
physical union of horizontal edge-left-column sets assigned to t. Use the
coordinate interval `I=[2,3Q+2]`, of cardinality `3Q+1`.

The following resources are disjoint subsets of I:

```text
vertical blocks: union_{v in V_t} {v-1,v,v+1};
horizontal endpoints: A_t union (A_t+1).
```

Let rho_t be the number of consecutive runs in A_t, taking rho_t=0 for
the empty set. Let w_t count the positions of I in neither resource. Then

```text
3|V_t| + |A_t| + rho_t + w_t = 3Q+1.
```

The one-dimensional identity behind this equation is
`|A_t union (A_t+1)|=|A_t|+rho_t`.

Define `Lambda=Q(N-1)-GOOD`, where GOOD counts both orientations of good
deep FF edges. Every horizontal edge is assigned three times, so

```text
3 Lambda = sum_{active t} (w_t+rho_t-1)
           + 3 sum_{inactive t} (Q-|V_t|).
```

All summands are nonnegative. This is an exact decomposition, not an assumed
stability certificate. In particular, if Lambda<=L, at most 3L active steps
have a vacancy or multiple horizontal runs, and at most L inactive steps
have fewer than Q vertical edges.

At Lambda=0, every inactive step is vertically saturated. Every active
step has one horizontal edge run, whose endpoint interval and the vertical
three-column blocks tile I exactly.

**This is local tiling stability, not a global rail classification.** One
consecutive run in A_t can be assembled from carriers on different nearby
rows. Counting its runs does not count its carriers. Singleton preserved
vertices contribute no FF edge directly.

## Exact Boundary Reserve

On each of the four middle boundary paths, retain all hole vertices and
all pure preserved vertices, including isolated retained vertices. Add
exactly the bad mirror edges and the pure-interval FF edges. Call this
ordinary path subgraph A_s and its component count c_s.

With u_s the hole count and p_mid,s the number of pure carriers meeting
that middle path, its forest ledger gives

```text
BAD_s = u_s + p_mid,s - c_s.
```

The vertex set is nonempty without assuming all-coveredness: either it
contains a hole, or the entire middle path is preserved and an adjacent
pair forces a pure boundary carrier. Thus c_s>=1 for every side.

Put

```text
u_mid = sum_s u_s;
Q_boundary = b-u_mid;
P_loss = p-sum_s p_mid,s;
R_boundary = Q_boundary + P_loss + sum_s c_s.
```

Four distinct near-corner holes give Q_boundary>=4. Pure carriers cannot
meet two middle sides, so P_loss>=0. Consequently

```text
R_boundary >= 8;
BAD = b+p-R_boundary;
Omega = R_boundary-8 >= 0.
```

This retains the slack discarded by `BAD<=b+p-8`. The auxiliary path
graph is not asserted to be a subgraph of the forced graph: its UU mirror
edges are generally unforced.

## Exact Global Identity

Use the existing actual carrier partition `d=r-p-h`, where h counts
nonpure carriers with no deep vertices. Let `K=(4n-4)-B-E` as in the half
proof. Define **signed** `e=f-T`; natural-number truncated subtraction is
not suitable for the identity below.

Convex trimming of straight carriers gives `Z=d+GOOD+BAD` for the original
deep induced graph. Combining this with the ambient ledger gives

```text
4e + c + h + K + Lambda + Omega = 2k+11,
```

or equivalently

```text
4e + R_boundary + c + h + K + Lambda = 2k+19.
```

These identities hold at paper level for every feasible F, k>=3, without
any excess, orientation, or coverage hypothesis. Nonnegativity, c>=1, and
the checked K>=5 theorem recover the half-coefficient bound.

To obtain `e<=C`, one would need, for example,

```text
c+h+K+Lambda+Omega >= 2k+11-4C.
```

This last displayed inequality is an equivalent accounting target, **not a
proved geometric estimate**. The measured decomposition above tells us which
resources must be counted; it does not establish that enough exist.

## A Constant-Bound Saturated Subcase

The following is a completed paper deduction, not a general stability theorem.
Assume Lambda=0 and that there are no good horizontal edges.

Every good vertical step then contains Q=k-1 edges. A maximum three-spaced
column set in [3,3Q+1] has ordered coordinates `3i+epsilon_i`, for i=1,...,Q,
where the epsilon_i are nondecreasing and belong to {0,1}. Two consecutive
steps cannot change an epsilon: the shared row would then have adjacent F
vertices with vertical edges, forcing a cell cycle. Thus all steps use the
same axes, and Q actual carriers fill the full deep height.

Their three-column blocks cover the N deep columns except one. Every other
deep F vertex must lie in that free column: a vertex immediately adjacent to
a full rail would make a preserved bend and a cell cycle. Two consecutive F
vertices in the free column would make a six-cycle with the nearest full rail.
There are consequently no bad deep FF edges either.

If t counts the additional preserved vertices in the free column, then

```text
Z = QN+t;
e = 6+t-K.
```

When the free column is internal, it is two columns from each of two full
rails. Each additional F vertex joins those rails by a literal four-edge
path. Two such vertices would create a cycle, so t<=1. Hence e<=2.

There is also a stronger component count. Apart from at most 3t positions
covered by these vertices and their vertical neighbors, and two possible
contacts at the longitudinal ends, all free-column vertices are actual ambient
isolates. A rail supplies a further nonisolated component. Therefore

```text
c >= N-3t-1 >= 3k-6;
e <= min(2, floor((12-k)/4)).
```

In particular this internal-free-column branch satisfies f<=T for k>=9.
The floor above is the integer floor, including when 12-k is negative.

### Endpoint Free Column

At an endpoint free column, side next-ring vertices can also cover the free
column, so the preceding isolate count does not apply. There is an exact
local reduction instead. Let s count preserved vertices in the adjacent
two-column annulus side strip, and retain t for the deep free-column F count.

Each of the other three two-column side strips has at most N preserved
vertices. To see this, a double-preserved slice forces its neighboring slices
empty; double slices are at least three apart by a six-cycle obstruction.
Assigning a different neighboring empty slice to each double proves the bound.
Each corner block contributes at most two preserved vertices. Thus

```text
B+E <= s+3N+8;
e <= s+t-N+2.
```

Different free-column F vertices attach to distinct components of the actual
adjacent two-column forced strip: otherwise their two paths to the same full
rail create a cycle. They are also three-spaced and force the neighboring
next-ring positions to be unpreserved.

These facts reduce this case to a concrete small-width paper problem:

```text
s+t <= N+C, for an absolute constant C.
```

That inequality is not proved here. Nor would proving it complete the general
upper theorem: mixed saturated tilings and positive Lambda would still require
a quantitative propagation argument. The completed result in this section is
the internal-free-column case, not a blanket assertion about all saturated sets.

## Physical-Lift Obstruction

The boundary reserve cannot be promoted to a physical merger bound without
accounting for its unforced edges. Here is the exact correction.

Let A be the disjoint union of the A_s, with vertex set W and component
count C_A. Let J be a literal physical subforest of the forced graph,
containing W and all forced edges of A. Define

```text
t = |E(A) minus E(J)|;
x = |V(J) minus W|;
L = |E(J) minus E(A)|.
```

The two forest ledgers give exactly

```text
C_A = c(J) + (L-x) - t.
```

The term L-x measures physical joining surplus. The term t counts the
selected virtual edges, normally UU mirrors, absent from the physical
forest. It cannot be discarded. Cycles in J union A may contain these
unforced edges and do not contradict forced acyclicity.

Likewise, arbitrarily many singly attached teeth can join the same physical
tree without forming a cycle. A tooth argument must prove two distinct
attachments or an independent vacancy/component cost. The known strip
counterexamples rule out charging every replacement carrier solely from its
presence in a three-column block.

## Remaining Research

The unresolved upper step is to connect the local tilings across successive
steps and to their actual boundary attachments. A useful proof must show how
replacement rods, turns, and singly attached teeth produce distinct measured
vacancies, boundary reserve, or actual final components.

The pointwise identities do not prove such a propagation law. In particular,
no linear lower bound on the total reserve with coefficient two has been
established, and no constant upper excess is claimed.

For the lower side, the nested-frame obstruction and moving-phase strip in
the companion note are separate results. Correct count growth does not make
the latter feasible: its proposed cap creates k+1 cycles. Neither the
half-coefficient upper proof nor the local stability formula supplies a
constant-gap lower construction.
