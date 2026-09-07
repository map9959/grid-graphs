# Paper Half-Coefficient Upper Bound

Date: 2026-09-07. Status: paper proof, not a newly Lean-verified bound.

## Result And Status

For every integer `k>=3`, set `n=3k+2>=11` and `T=3k^2+7k`. If `F` is a
feasible preserved set in the `n` by `n` grid, then the paper argument below gives

```text
|F| <= T + floor(k/2) + 1.
```

Consequently the same paper upper bound holds for `P(3k+2)`, the maximum
feasible cardinality. The proof is unconditional for every feasible `F`:
there is no coverage, missing-side, counterexample, orientation, occupied-row
count, or carrier-count premise. There is no attainability or sharp-`T` claim.

The existing Lean-verified upper bound remains `T+floor(2k/3)` for `k>=5`. This document
does not change any Lean theorem, root import, build, or verification claim.
The supplied audit history reports **three independent read-only paper
audits of the earlier proof, with no fatal gap found**, followed by **two
additional independent read-only audits of this unconditional simplification,
also with no fatal gap found**. These are reported paper-review outcomes,
not audits run by this documentation edit and not kernel verification.
The new geometric, scheduling, and slack lemmas below are not formalized.

See the [Paper Upper Program](PAPER_UPPER_PROGRAM.md) and
[handoff](HANDOFF_U1_U3_L2.md) for the checked milestone and earlier program.
The improvement changes the coefficient of the linear excess from `2/3` to
`1/2`: the saving over the checked formula is

```text
floor(2k/3) - floor(k/2) - 1 = k/6 + O(1).
```

Thus it saves `k/6-O(1)` vertices asymptotically, not merely a constant gap.
Some small values agree with the checked bound.

## Coordinates And Accounting

Use physical coordinates `(x,y)` in `{0,...,n-1}^2`. Let `U` be the complement
of `F`. The forced graph `H` has all grid vertices and every grid edge with
at least one endpoint in `F`. Feasibility means that `H` is a forest.
An `FF` edge has both endpoints in `F`.

The notation is as follows; all component counts refer to actual graphs.

| Symbol | Meaning |
|---|---|
| `f` | `|F|` |
| `r` | Number of connected components of the grid induced on `F`, called carriers |
| `c` | Number of components of `H` on all `n^2` vertices, including isolates |
| `b` | `sum_{u in U}(4-deg_grid(u))`: open-boundary holes have weight one, corner holes weight two |
| `p` | Number of carriers wholly in the outer boundary, called pure carriers |
| `h` | Number of nonpure carriers not meeting the deep square, called shallow carriers |
| `d` | Number of carriers meeting the deep square: `d=r-p-h` |
| `B` | Number of preserved outer-boundary vertices |
| `E` | Number of preserved next-ring vertices, at distance one from the boundary |
| `K` | `4n-4-B-E`, the two-layer loss; the checked annulus cap gives `K>=5` |
| `Z` | Number of preserved vertices in the deep square `{2,...,n-3}^2` |
| `N,Q` | `N=n-4=3k-2=3Q+1`, `Q=k-1` |
| `e` | Signed integer excess `f-T`, not truncated natural-number subtraction |

Every carrier is a filled straight interval, with singletons allowed. Indeed,
a perpendicular pair of successive induced edges puts preserved vertices at
opposite corners of a unit square, forcing its four-cycle. A connected
component with no turn lies on one axis, and connectivity fills its interval.

The exact global ledger is

```text
3f+r+c+b = n^2+4n.
```

For completeness, the induced forest has `f-r` edges. The sum of grid
degrees on `F` is `4f-4n+b`, since the total boundary deficiency is `4n`.
Subtracting the induced-edge count once gives the forced-edge count
`3f+r-4n+b`. Equating this to `n^2-c` proves the ledger. In particular `c>=1`.

At each corner its two adjacent open-boundary vertices
are diagonally opposite in a unit square, so at least one is a hole. These
give four distinct weight-one Near witness holes. They will be reserved
outside the middle boundary paths below; no stronger lower bound on `b`
is needed. A straight pure carrier meets at most one open side (a side
without its corners); a corner singleton meets none. Fix the coordinate
axes arbitrarily. No minority-orientation choice is needed.

## Bad Edges And Boundary Paths

Partition the original deep `FF` edges into `BAD` and `GOOD`. Bad horizontal
edges lie on the first or last deep row, physical `y=2,n-3`. Bad vertical
edges lie on the extreme deep columns, physical `x=2,n-3`. All other deep
`FF` edges are good. These four bad families are disjoint as edge sets.

### Mirror Lemma

Mirror each bad edge to the parallel boundary edge at distance two. For
example, `(a,2)(a+1,2)` maps to `(a,0)(a+1,0)`, where
`2<=a<=n-4`. The map is injective on each side.

The mirror cannot be `FF`: together with the bad edge it forces the
six-cycle around the width-one, height-two rectangle. More strongly,
**any preserved endpoint of the mirror belongs to a pure carrier**.
To prove this, suppose `v=(a,0)` is preserved and nonpure. Straightness and
connectivity force its immediate inward neighbor `w=(a,1)` to be preserved;
equivalently this is the checked nonpure-boundary next-ring-neighbor fact.
Then `w` and the other bad endpoint `(a+1,2)` are diagonally opposite in a
unit square, forcing a four-cycle. The argument for the other endpoint
and each other side is identical by square symmetry. No condition on the
other mirror endpoint being a hole is needed for this purity conclusion.

### Side Path Lemma

For a side `s`, let `MID_s` be its boundary path with positions
`2,...,n-3`. Let `u_s` count holes in this path, let `M_s` count preserved
vertices there belonging to pure carriers, and let `p_mid,s` count pure
carriers meeting this path. This lemma holds unconditionally for `n>=6`,
so that the path has `N=n-4>=2` vertices.

Every pure carrier intersects `MID_s` in either the empty set or one filled
interval. Distinct such intervals are disjoint. Their internal `FF` edges
therefore number exactly `M_s-p_mid,s`.

Let `W_s` be the vertex set consisting of the `u_s` holes and the `M_s`
pure preserved vertices. This set is always nonempty: a hole in `MID_s`
belongs to it; if there are no holes, the entire path is preserved, and
an adjacent pair forces its straight carrier to lie along the boundary,
hence to be pure. Thus in this case `M_s>=2`.

On `W_s`, take the interval edges together with the bad mirror edges.
The mirror lemma ensures that all endpoints are in this vertex set.
The two edge families are disjoint because a bad mirror is not `FF`.
This graph is a subgraph of an ordinary path, hence a forest; it need not
be a subgraph of the forced graph, since a mirror can be `UU`.

Since `W_s` is nonempty, the ordinary forest bound always gives

```text
(M_s-p_mid,s) + bad_s <= u_s+M_s-1,
bad_s <= u_s+p_mid,s-1.
```

This includes `p_mid,s=0`: then `M_s=0`, `u_s>=1`, and the same path
bound gives `bad_s<=u_s-1`. No side-coverage fallback is needed.

Sum over the four sides. A pure carrier meets at most one `MID` side, so
`sum_s p_mid,s<=p`; carriers avoiding all `MID` paths can make this strict. The four `MID`
paths are disjoint and avoid the eight positions immediately adjacent to
corners. The four mandatory Near witness holes used above are outside
these paths. With the weights defining `b`, this gives `sum_s u_s<=b-4`.
Consequently

```text
BAD <= sum_s u_s + sum_s p_mid,s - 4 <= b+p-8.         (1)
```

This is **`b+p-8`, not `2b-8`**. The pure intervals are counted jointly with
the mirrors on a physical path; separate per-hole incident-edge allowances
would lose the needed coefficient. Equation (1) holds for every feasible
set when `n>=6`, not just all-covered sets.

## Good Edge Packing

Index deep rows by `1,...,N`, with deep row `y` at physical row `y+1`.
Index vertical steps by `t=1,...,N-1`. Retain physical column coordinates.
Let `V_t` be the set of columns of good vertical `FF` edges at step `t`.
Thus

```text
V_t subset {3,...,n-4} = {3,...,3Q+1}.
```

For an interior deep row `y`, let `E_y` be the set of physical left columns
of its horizontal `FF` edges. Then `E_y subset {2,...,n-4}`. Its occupied
row set `S={y:E_y nonempty}` lies in `{2,...,N-1}`. There is no restriction
on its cardinality.

### Local Exclusions

The following elementary forced-cycle exclusions apply to the actual edge
sets, without any longness assumption.

1. Distinct columns of `V_t` differ by at least three. Distance one forces
   the unit-square cycle; distance two forces the six-cycle around a
   width-two, height-one rectangle.
2. If `0<|y-z|<=2`, then `E_y` and `E_z` are disjoint. A common left column
   would give parallel horizontal `FF` edges at row distance one or two,
   forcing respectively a four- or six-cycle.
3. A horizontal edge with left column `a` in row `y` is compatible only
   with vertical columns outside `{a-1,...,a+2}` on each valid step in
   `{y-2,y-1,y,y+1}`. For column `a-1` or `a+2`, a preserved vertical endpoint
   is diagonally opposite a preserved horizontal endpoint in a unit square.
   For column `a` or `a+1`, the same diagonal obstruction applies using the
   other horizontal endpoint. The step range ensures a vertical endpoint
   is one row above or below the horizontal edge.

In particular, for any such compatible horizontal edges, their endpoint
columns avoid each three-column block `{x-1,x,x+1}` with `x in V_t`.

### Three-Step Schedule

Use the fixed residue schedule on every interior row, occupied or not.
Because `N=3Q+1`, define integer intervals

```text
T_y = [y-1,y+1]  if y mod 3 = 2,
T_y = [y-2,y]    otherwise.
```

Every interval has three steps and lies in `{1,...,N-1}`. The lowest row
`2` is shifted and starts at step `1`; every unshifted row is at least `3`.
The last interior row `N-1` has residue `0` and is unshifted. Every shifted
row is at most `N-2`, so its last step is at most `N-1`. Each interval lies
in the four-step compatibility range of the local exclusions.

Rows at distance three have the same residue and shift, so their assigned
intervals are disjoint. At distance at least four even the latest possible
left endpoint interval ends before the earliest possible right interval:
`y+1<z-2`. Rows at distance one or two may
share steps, but their `E` sets are disjoint by the local exclusions.
It follows that at every step the sets in

```text
A_t = union_{y in S, t in T_y} E_y
```

are pairwise disjoint, and

```text
sum_t |A_t| = 3 sum_{y in S}|E_y|.
```

All residue-two rows are shifted, not just an initial occupied chain.
The construction works for any number of occupied rows, without separated
rows, a carrier bound, or `N>=13`. At `k=3`, `N=7`, its complete schedule is

```text
2: [1,3],  3: [1,3],  4: [2,4],  5: [4,6],  6: [4,6].
```

### Joint Step Lemma

At a fixed step the three-column blocks centered at `V_t` are disjoint and
contained in the physical deep-column interval `{2,...,n-3}`, of length
`N=3Q+1`. They avoid the union of horizontal endpoint columns

```text
W_t = A_t union {a+1:a in A_t}.
```

If `A_t` is nonempty, then `|W_t|>=|A_t|+1`: the successor of the largest
element is an extra endpoint. Thus

```text
3|V_t| + |A_t| + 1 <= N = 3Q+1,
3|V_t| + |A_t| <= 3Q.
```

If `A_t` is empty, the block count gives `3|V_t|<=3Q+1`, and integrality
gives the same conclusion `3|V_t|<=3Q`. We have therefore proved the joint
inequality for every step, including empty steps. This uses a physical
union, not a sum of potentially overlapping shadows.

Summing over all `N-1` steps and using the schedule yields

```text
3 sum_t |V_t| + 3 sum_y |E_y| <= 3Q(N-1),
GOOD <= Q(N-1).                                      (2)
```

Thus (2) holds for every feasible `F` in the stated residue-two grids,
in either fixed orientation.

## Original Deep Identity

The identity needed here is for the **original induced deep graph**, before
deleting bad edges:

```text
Z = d + FF_deep = d + BAD + GOOD.                     (3)
```

To justify it exactly, intersect each actual straight filled carrier with
the convex deep square. Every nonempty intersection is one filled interval,
possibly a singleton, and is connected. Distinct carriers cannot acquire
an induced connecting edge on restriction. Thus the induced deep graph has
exactly `d` components, one for each original carrier meeting the square.
It is a forest, so its edge count is `Z-d`.

Deleting bad edges can split these intervals. The number of components of
the good-edge graph is not `d` in general, and no identity with that altered
component count is used. Deep singleton carriers remain in `d` even though
they contribute no deep edges.

## Exact Global Slack Identity

Define the nonnegative integer slacks

```text
Lambda = Q(N-1)-GOOD >= 0,
Omega  = b+p-8-BAD >= 0.
```

All subtraction here and below is ordinary integer subtraction. In
particular `e=f-T` is signed and may be negative. Equations (1)--(3), and
the exact layer partition `f=B+E+Z`, give for every feasible `F`, `k>=3`,

```text
f = 12k+4-K + d + Q(N-1) + b+p-8-Lambda-Omega
  = T+r-k-1-h-K+b-Lambda-Omega.                       (4)
```

Here `Q(N-1)=(k-1)(3k-3)=3k^2-6k+3`, and `d=r-p-h`.
In particular the pure-carrier count cancels without assuming `p=4`.
This is a measured bound in the actual quantities `r,h,K,b`, not a
generic rooted or long-carrier cap.

Substitute `f=T+e` and the exact ledger
`r=3k+12-3e-b-c` into (4). The boundary deficiency cancels and gives the
**unconditional exact identity**

```text
4e+c+h+K+Lambda+Omega = 2k+11.                        (5)
```

In particular the measured upper bounds, also unconditional, are

```text
f <= T+r-k-1-h-K+b,
f <= T + floor((2k+11-c-h-K)/4).
```

Since `n>=11`, the checked global annulus cap applies and gives `K>=5`.
Together with `c>=1`, `h>=0`, and both nonnegative slacks, (5) gives
`4e<=2k+5` directly, without a counterexample reduction. The uniform floor is

```text
floor((2k+5)/4) = floor(k/2)+1
```

for both parities of `k`. This proves `f<=T+floor(k/2)+1` for every feasible
set and every `k>=3`, with no small-case equality branch.

## Exact Packing Slack

The schedule also resolves `Lambda` into local nonnegative contributions.
Write `E_t^*=A_t` for the physical union of assigned horizontal edge-column
sets and `v_t=|V_t|`. Call a step active when `E_t^*` is nonempty. At an
active step let `rho_t` be the number of maximal consecutive integer runs
in `E_t^*`. Its horizontal endpoint union has exactly
`|E_t^*|+rho_t` columns: each run contributes one more endpoint than edges,
and different runs have disjoint endpoint sets.

Let `I={2,...,3Q+2}`, the full deep-column interval, of size `3Q+1`.
Let `w_t` count columns of `I` outside both the vertical three-column blocks
and the horizontal endpoint union. Those blocks and that union are
disjoint by the joint step lemma. At every active step the exact partition is

```text
3v_t + |E_t^*| + rho_t + w_t = 3Q+1,
3(Q-v_t)-|E_t^*| = w_t+rho_t-1 >= 0.
```

At an inactive step its contribution is `3(Q-v_t)>=0`, by integer packing.
Counting every horizontal edge three times therefore gives

```text
3Lambda = sum_{active t}(w_t+rho_t-1)
        + 3 sum_{inactive t}(Q-v_t).                 (6)
```

Define a defective active step to mean one with `w_t+rho_t-1>0` (not a
bad deep edge from the earlier partition). Each contributes at least one,
so

```text
number of defective active steps <= 3Lambda,
sum_{inactive t}(Q-v_t) <= Lambda.
```

An active step has zero contribution exactly when `w_t=0` and `rho_t=1`;
an inactive step has zero contribution exactly when `v_t=Q`. These are
local stability statements only. They do not identify a global rail family
or assert a linear reserve bound. Further development is intended for
`PAPER_PACKING_STABILITY.md`; that companion document is outside this edit.

## Source Anchors

The following are existing source anchors, not claims that the new paper
lemmas have already been formalized. Paths are relative to this document.
The named documentation and the three linked Lean files for closure,
annulus cap, and boundary geometry were read in the initial documentation
pass. This simplification edits only this paper; no search or build was run.
The primary program and handoff can be updated separately; they are not
edited here. Missing-side closure is now a historical anchor, not an input
to the unconditional proof.

| Input or distinction | Current repository anchor |
|---|---|
| Checked global bound `T+floor(2k/3)` | [Paper Upper Program, lines 24--30](PAPER_UPPER_PROGRAM.md#status-and-notation), recording `GridGraphs.maxPreserved_residueTwo_le_endpoint_refinement` and `GridGraphs.forced_card_le_endpoint_refinement` in `Accounting/EndpointUpper.lean` |
| Historical input only: entire missing-side closure, no `p` restriction | [ThreeCarrier/Closure.lean, lines 65--78](../lean/GridGraphs/Accounting/CarrierLayers/ThreeCarrier/Closure.lean#L65), `GridGraphs.CarrierLayers.ThreeCarrier.card_le_target_of_missing_side` |
| Historical input only: actual all-covered consequence | [ThreeCarrier/Closure.lean, lines 80--91](../lean/GridGraphs/Accounting/CarrierLayers/ThreeCarrier/Closure.lean#L80), `counterexample_all_sides_covered` |
| Boundary plus next-ring occupancy and `K>=5` | [Annulus/Cap.lean, lines 122--137](../lean/GridGraphs/Accounting/CarrierLayers/Annulus/Cap.lean#L122), `GridGraphs.CarrierLayers.Annulus.boundary_add_nextRing_card_le` and `five_le_loss` |
| Actual straight carriers | [CoveredBoundary.lean, lines 23--38](../lean/GridGraphs/Accounting/CarrierLayers/CoveredBoundary.lean#L23), using `induced_forced_connectedComponent_straight` |
| Nonpure preserved boundary vertex has a preserved next-ring neighbor | [CoveredBoundary.lean, lines 123--137](../lean/GridGraphs/Accounting/CarrierLayers/CoveredBoundary.lean#L123), application of `boundary_nonpure_carrier_nextRing_neighbor` |
| Actual pure supports and their disjoint mass | [CoveredBoundary.lean, lines 18--21 and 209--244](../lean/GridGraphs/Accounting/CarrierLayers/CoveredBoundary.lean#L209), `pureBoundaryVertices` and `pure_boundary_mass_eq_sum_le_capacity` |
| Global ledger and historical deep-edge identity | [Paper Upper Program, Status And Notation](PAPER_UPPER_PROGRAM.md#status-and-notation) and [Historical Mixed/Top Accounting](PAPER_UPPER_PROGRAM.md#historical-mixedtop-accounting-closed); (3) above supplies the exact convex-trim justification for this proof |
| Checked milestone and limits of existing verification | [handoff, Latest Continuation](HANDOFF_U1_U3_L2.md#latest-continuation) |

Neither the historical three-rod shadow certificate nor the conditional
rooted endpoint cap is imported as an unrestricted theorem here. The new
mirror/path lemma, fixed residue schedule, joint step count, and exact
slack identities are proved above at paper level.

## Audit Guardrails

The reported three initial independent read-only paper audits and two
additional independent audits of the simplification found no fatal gap.
The proof records the following sensitive points explicitly so that the
paper result can be checked or formalized without silently strengthening
its premises.

- Every feasible set is covered by this theorem; side coverage, missing-side
  closure, and `p=4` are not proof premises.
- Mirror purity applies to any preserved mirror endpoint; the intervening
  inward preserved vertex and the opposite bad endpoint give a literal cycle.
- The side count uses an ordinary path forest even for `UU` mirror edges.
  Its vertex set is always nonempty for `n>=6`, including when `p_mid,s=0`.
- The four mandatory Near holes are outside the four disjoint `MID` paths.
- Singletons remain in the global ledger and original deep-carrier count;
  no orientation choice or bound on the number of occupied rows is needed.
- The fixed residue schedule shifts every residue-two row, handles nearby
  rows jointly, stays inside the step range, and counts every horizontal
  edge exactly three times, including at `N=7`.
- The joint step count uses disjoint physical blocks and an endpoint union;
  its empty-horizontal case uses integer rounding.
- Equation (3) precedes bad-edge deletion. Good-graph components cannot
  replace the actual deep-carrier count.
- Signed excess and ordinary integer subtraction make (5) an exact global
  identity, even when `f<T`. Equation (6) is local packing stability only.
- No unique-root premise, root normalization, connectedness assumption,
  generic longness assumption, or new Lean build is part of the argument.

## Beyond One Half

The exact form (5) retains real leverage from `c`, `h`, `K`, `Lambda`,
and `Omega`. For example, any additional valid joint estimate
`Lambda>=delta` gives

```text
4e+c+h+K+delta <= 2k+11.
```

Further coefficient improvement would require quantitative good-edge
deficits or a global stability argument producing losses that grow with
`k`. The schedule is already unconditional; (6) does not itself prove such
growing losses. No linear reserve bound is asserted. Constant endpoint losses
alone do not change the coefficient. Such an argument must track actual
replacement carriers: deleting or shortening one rod and inserting other
carriers can change `r`, `d`, the active edge sets, and the available capacity,
even though the residue schedule itself is fixed.
A loss measured against a fixed rod list is not automatically a net global
loss after replacement.

In particular, one cannot assume an additional unit of deficit per carrier
in an unrestricted strip. A straight vertical spine can attain its baseline
edge capacity with zero such extra loss; other unrestricted strip examples
also admit separated singleton teeth. The old proposed local `L/2` strip
occupancy estimate is explicitly false, as recorded in the
[program guardrails](PAPER_UPPER_PROGRAM.md#overlap-and-guardrails): a vertical
spine of length `L` with separated opposite-column singleton teeth has
`L+ceil(L/3)` preserved vertices and a forced tree. Any stronger stability
claim must state and prove the global hypotheses that exclude these
replacement configurations and must count shared resources only once.

The half-coefficient paper theorem neither supplies the sharp all-covered
`T` upper bound nor constructs a target-count lower family. Those remain
separate tasks; the checked lower bound and all existing Lean claims are
unchanged.

## Historical Appendix

The first version proved the same numerical formula only for `k>=5` by
contradiction. A putative excess `e>floor(k/2)+1` gave `3e>=k+7`, hence
`r<=2k-1` from the global ledger and `b>=5,c>=1`. Checked missing-side
closure supplied all-coveredness. A minority-orientation choice then gave
at most `J<=k-1` horizontal good rows, and an initial occupied-chain
schedule worked under `N>=3J+1`. The side-path proof used coverage as a
fallback when its pure intersection was empty.

Those restrictions are superseded, not additional hypotheses of the
present theorem. The path vertex set is intrinsically nonempty, so coverage
is unnecessary. Shifting every residue-two row removes the occupied-chain,
minority-orientation, `J`, and `r` reductions. The exact signed-excess
identity now proves the bound directly for `k>=3`. The initial three paper
audits remain historical evidence for that earlier argument; the two
additional reported audits address the unconditional simplification. None
of these paper reviews changes the checked Lean upper theorem.
