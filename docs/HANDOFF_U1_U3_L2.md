# U1, U3, And L2 Checkpoint

Date: 2026-09-06. Updated after concentrated-gap and covered-shadow theorems,
the two-rail/notch follow-up, and full strict verification. Numerical bounds unchanged.

## Latest Continuation

**Latest checked lower result:** `GridGraphs.RailRepair.residueTwo_le_maxPreserved`
proves `L(k)=3k^2+6k+3+floor((k-1)/2)<=P(3k+2)`, k>=3. Writing
`T=3k^2+7k` as in the upper route,
`L(k)=T-floor(k/2)+2` for k>=5. The single terminal repair gains one
at odd k and agrees with the historical staircase at even k. It is not a
target pump: its checked six-width gain remains 12k+25, not 12k+26.

The previous five strictly compiled modules are `CarrierLayers/OneExcessSeparated.lean`,
`CarrierLayers/CoveredBoundary.lean`, and
`Constructions/ResidueTwo/RailRepair/{Geometry,Forest,Score}.lean`.
The upper modules prove root-separated hole charges and actual pure-mass
budgets, with the precise conditional scope below. Neither changes the global
upper formula or closes either upper branch.

The latest two modules are `CarrierLayers/ConcentratedGaps.lean` (7 public
theorems, 297 lines) and `CarrierLayers/CoveredDeficit.lean` (9 public theorems,
244 lines). They bound concentrated root-free gaps and link physical boundary
shadows to carrier length. Their conditional certificates and local losses do
not close either upper branch or improve the numerical bounds.

**Previous checked U3 result (still valid):** for n=3k+2, k>=5, ANY missing open side implies
`f<=T(k)+1` and `b>=2k+3`, independently of p. A missing side is met by no
pure boundary carrier; it need not have zero preserved vertices. No maximality
or connectivity assumption beyond forced-graph acyclicity is required.
In particular p<=3 implies f<=T+1. The formerly unique two-excess profile
`(r,c,b)=(k+2,1,2k+3)` is now excluded. Every feasible f>=T+2 set covers
all four open sides with four distinct actual pure carriers, hence p>=4.

Previous milestone's files under `lean/GridGraphs/Accounting/CarrierLayers/`:

- `MissingSide.lean`: missing-side bounds and distinct side-covering pure carriers.
- `MissingSideSharp.lean`: uniform f<=T+1 and four distinct side-covering carriers.
- `RadialNearTightBoundary.lean`: near-tight boundary geometry and root/pure-carrier nonreuse.
- `RadialNearTightExclusion.lean`: exclusion of the last two-excess profile.
- `RadialOneExcess.lean`: exact one-excess slack and saturated-root isolate bounds.

Public endpoints in namespace GridGraphs:
`residueTwo_card_le_target_add_one_of_missing_side` and
`residueTwo_four_distinct_pure_carriers_of_two_excess`.
The root and Regression cover all five leaves transitively. Regressions check
f<=T+1 at k=5/7, the uniform missing-side bound, and p>=4 at f>=T+2, k=5.

**Verification complete:** full strict build passed with 8,941 jobs, zero
warnings/errors, exit 0. All 163 audited public theorems (previous 147 rerun
plus all 16 new theorems) use only standard logical axioms. There are 234
modules under GridGraphs, plus the aggregate root. Root and Regression cover
both new upper fronts and the repaired lower bound. Details and logs are below.

**PROOF NOT FINISHED:** the one-excess and all-sides-covered upper branches,
sharp global upper bound, and target-count lower family remain open.

**L2 paper progress:** [L2_FIXED_RAIL_POCKET.md](L2_FIXED_RAIL_POCKET.md) proves at paper level that
arbitrary repacking of the bottom two deep rows cannot improve the staircase
while its frame and all rails stay fixed. It gives the exact allowable-center
and spacing classification. This is not a formal Lean result or a general
pump obstruction. Successful surgery must escape that fixed outside geometry.

[L2_RAIL_REPAIR_RESEARCH.md](L2_RAIL_REPAIR_RESEARCH.md) supplies a terminal-rail
repair whose uniform forest proof and score are now backed by Lean:
`G(s)=3s^2+12s+12+floor(s/2)`, s>=2, n=3s+5. It gains one when s is even
and is count-neutral when s is odd, but its six-width gain is still 12s+37,
not 12s+38. The repair does not accumulate into a pump. The module
`analysis.searches.l2_rail_repair_research` ran finite restricted searches only
at n=11/14: with the original frame and earlier rows fixed, last-four-deep-row
repacking has maxima 49/76, not global optima. The historical packaging pass
passed three focused and seven layout tests, replaying fixed witnesses without
searching. Those finite tests did not establish the uniform theorem; the later
Lean proof does. The previous main-agent run passed 13 tests (three terminal,
three propagating, seven layout), without searches. The separate
[propagating-interface alternative](L2_PROPAGATING_INTERFACE.md) remains a
paper forest argument for a candidate that fails the actual target gain.

The [two-rail/notch follow-up](L2_TWO_RAIL_INTERFACE.md#notch-follow-up) reports
n11/n14 restricted maxima 49/76 unrestricted, 48/75 rootless, and 47/75
joined-rootless. All six notch searches had 100,000-node caps and finished
exhaustively within the specified windows, not globally. An explicit independent
joined output reaches the lower extension, but adding the next center without
deletion closes a cycle. Deleting the obstructing tail center permits a
count-neutral continuation. The following step consumes independence through
the frame at n11 or hits the next tail square at n14. No uniform pump follows.
The latest main-agent run passed 19 tests without searches during tests;
the note separately records its deliberately one-node budget-status test.
These new lower results remain finite/paper evidence, not Lean theorems.

## What The Route Labels Mean

These labels refer to the latest research plan, not similarly named stages in
older roadmaps. The canonical definitions are in
`ROADMAP.md`, under **Research Route Labels**.

| Label | Meaning | What would complete the route |
|---|---|---|
| **U1** | **Boundary-six control:** classify the boundary and next ring at b=6, then combine its refined carrier bound with other boundary-budget branches. | A stronger unconditional upper bound. The planned next-ring and bound-improvement milestones are checked; sharpness remains open. |
| **U2** | **Boundary-five attachment rigidity:** generalize the canonical frame reasoning to arbitrary b=5 sets, prove actual boundary/spoke connectivity, and forbid fully spanning deep carriers. | A checked stricter b=5 capacity or equality exclusion, with missing-spoke exceptions handled. General attachment rigidity is still unfinished. |
| **U3** | **Global near-extremal packing:** trade off long carriers, boundary contacts, layer occupancy, and forced components without reusing resources. No b=5 or b=6 restriction. | Exclude every counterexample above T. Missing-side f<=T+1 and exact three-unit slack remain valid. Root-separated charges give f<=T conditionally on p+\|S\|>=7; existence is open. Actual pure-mass budgets are checked but not independently addable. Both upper branches remain open. |
| **L1** | **Relayout the staircase:** move rails/attachments so its uncovered vertices admit additional legal promotions. | An explicit target-count family with a uniform forest proof. The terminal parity repair is now formal, but does not reach the arbitrary-width target. |
| **L2** | **Six-width pumping:** use compatible 11x11 and 14x14 seeds and prove a geometric `k -> k+2` operation gaining `12k+26` preserved vertices. | All-width closure, count, and acyclicity. Seed budgets and the uniform terminal repair are checked, but its gain is only `12k+25`. The separate propagating candidate is paper-level and fails the target gain. |
| **L3** | **Escape the staircase:** use a different boundary pattern, or directly build a target-sized unpreserved set with connected U-U dual. | An actual arbitrary-width construction, not an abstract graph or an assumed connectivity certificate. This remains open. |

U denotes upper bound and L lower bound. The user selected **U1 and L2, with
a push into U3**. The routes are alternatives/complements, not a fixed six-step
pipeline. In particular, neither a connected forced graph nor boundary
deficiency five is required of every successful lower construction.

The L2 seeds have scores 48 and 76, not the optimal early scores 49 and 77.
They are useful because they match the stable polynomial T at k=3 and k=4;
a valid six-width pump could then reach the stable range. Matching those seed
counts is not a proof that a proposed geometric invariant is preserved.

## User Requirements

- Continue upper/lower proof research, emphasizing U1 and L2 and pushing into U3.
- Split a Lean module before extending it beyond 1,000 lines. Use sub-subfolders.
- Keep every linter warning addressed; no suppression or backward flags.
- No new optimization searches above 15x15. Existing fixed witnesses may be checked.
- Full project verification may run without a timeout; do not rebuild mathlib unnecessarily.
- Preserve concurrent worktree changes. The user has committed checkpoints during work.

## Earlier U1 Milestone (Still Current Bound)

The earlier U1 milestone proved the unconditional stable residue-two upper bound:

```text
P(3k+2) <= 3k^2+7k+floor((2k+2)/3),    k>=5.
```

Previously the final floor was `(2k+3)/3`. The improvement is one vertex when
k is divisible by three. Examples: P(20)<=154 instead of 155; P(29)<=312
instead of 313. At that historical milestone the uniform staircase lower was
`3k^2+6k+2+floor(k/2)` for k>=3. It remains valid, but the new terminal
repair improves it at odd k. No target-count lower pump has been found.

The previous terminal milestone changed the uniform lower formula to L(k).
The latest gap/shadow and notch pass changes neither bound. Current bounds are:

| Side | Formal lower | Global upper |
|---:|---:|---:|
| 17 | 110 | 114 |
| 20 | 149 | 154 |
| 23 | 195 | 201 |
| 26 | 246 | 254 |
| 29 | 304 | 312 |

The uniform 110 lower matches the existing finite witness at side 17;
**P(17) is not proved exact**.

## Definitions

F is a feasible preserved set; H contains every grid edge incident to F.

```text
f = |F|
r = number of components of grid[F] (preserved carriers)
c = number of components of H on ALL vertices, including isolates
b = boundary deficiency of univ\F
p = number of preserved carriers contained entirely in the outer boundary
T(k) = 3k^2+7k
```

Existing exact ledger: `3f+r+c+b=n^2+4n`.

## Checked New Modules

All names below are in namespace GridGraphs unless otherwise noted.
All new modules have passed direct checks with warnings treated as errors.

### Boundary Six

`lean/GridGraphs/Accounting/BoundarySix/` contains:

- `Geometry.lean`: boundary corner/near/second-position and distance-two-pair geometry.
- `Witnesses.lean`: four distinct near-corner U witnesses.
- `Decomposition.lean`: b=6 boundary decomposition, accounting for corner weight two.
- `Pairs.lean`: uniqueness of the possible unordered distance-two UU pair.
- `NextRing.lean`: `boundaryDeficiencySum_compl_eq_six_next_ring_card_le_one`,
  for arbitrary feasible F, n>=9, b=6. At most one next-ring vertex is preserved.
- `Balance.lean`: for n>=9, b=6, the preserved boundary count is at least
  `4n-10`, and preserved boundary plus preserved next-ring count is at most
  `4n-9`. Also exports `boundaryDeficiencySum_compl_eq_six_boundary_count_bounds`.
- `CarrierBound.lean`: `forced_card_le_boundary_six_components`, n>=12,
  proves `f<=(n-4)r+7` at b=6. `forced_card_le_small_boundary_components`
  combines the b=5 and b=6 cases under b<=6.
- `Upper.lean`: `maxPreserved_residueTwo_le_boundary_six_refinement`, k>=5,
  is the new unconditional upper bound above. It covers ALL boundary budgets.

`Geometry/GridLayers.lean` now owns the generic public predicate `IsNextRing`.
It was extracted from the new BoundarySix module so global results do not
depend on a b=6 theorem merely to define a layer.

### Global Carrier Layers

`Accounting/CarrierLayerBound.lean` defines `pureBoundaryCarriers F` and proves,
for arbitrary feasible F and n>=5, writing B for preserved boundary count and
E for preserved next-ring count:

```text
p <= r
B <= n*p+E
f <= B+E+(n-4)*(r-p)
```

The substantive injectivity theorem is
`boundary_nonpure_carrier_nextRing_neighbor`: a boundary F vertex in a
nonpure carrier has a preserved next-ring neighbor in the same carrier.
`nextRing_preserved_boundary_neighbor_unique` prevents reuse of that neighbor.

`Accounting/CarrierLayers/NextRingInjection.lean` proves, for arbitrary budgets,

```text
E <= number of unpreserved boundary vertices <= b
4n-4 <= n*p+2b                   (n>=7 for the last inequality)
```

The injection is explicit. For a next-ring vertex (row,column), choose a
diagonally adjacent boundary vertex: top first, then bottom, then left, then
right. Coordinate ranges make the images injective, and the unit-cell
obstruction makes every image unpreserved.

### Historical Three-Carrier Reductions

`Accounting/CarrierLayers/` also contains `RadialSideGeometry.lean`,
`RadialPacking.lean`, `RadialSideCounting.lean`, and `RadialSide.lean`.

For n=3k+2, k>=5, and p<=3 they prove:

```text
b >= 2k+2
f <= T(k)+2
if f>=T(k)+1: c<=5 and k+2<=r<=k+6
```

Reason: a pure boundary carrier lies on one side. With at most three, some
open side has none. Every preserved vertex there is radial and has a preserved
inward neighbor. Unit/six-cycle obstructions space these positions at least
three apart, so at most k of that side's 3k noncorner vertices are preserved.
There are at least 2k holes on that side, plus two corner witnesses outside it.

`CarrierLayers/Counterexamples.lean` combines these with the global injection:

- `residueTwo_stable_counterexample_three_le_pureBoundaryCarriers`: any stable
  counterexample for k>=7 has p>=3, without any b assumption.
- `residueTwo_stable_counterexample_pure_boundary_cases`: either p=3, f<=T+2,
  c<=5, k+2<=r<=k+6, OR p>=4.
- `residueTwo_two_excess_three_carrier_profiles`: if p<=3 and f>=T+2,
  then f=T+2 and only these numerical profiles remain:

```text
(r,c,b) = (k+2,1,2k+3)
       or (k+3,1,2k+2)
       or (k+2,2,2k+2).
```

These are historical necessary conditions, not constructions. The latter two
profiles were excluded by `RadialTightExclusion`: exact roots at 2,5,...,3k-1
force a third off-side hole against the two-hole budget. Its unique-profile
endpoint was an intermediate milestone, not the current open problem.
`RadialNearTightExclusion` now excludes the first profile as well.

### Current Missing-Side And One-Excess Results

For the near-tight two-excess profile, let q count preserved roots on a
missing side. Root and pure carriers are physically distinct, so `q+p<=r`.
The near-tight bounds force `p=3, q=k-1`. An empty boundary triple exists;
since c=1 its middle cannot be an ambient isolate, forcing an inward F
witness. Its carrier is distinct from all q root carriers and all p pure
carriers, giving `r>=q+p+1=k+3`, contrary to r=k+2. MissingSideSharp extends
the exclusion to any missing side independently of p. This proves the uniform
f<=T+1 bound and the four-distinct-carriers conclusion above.

For k>=5, p<=3, and f>=T+1, RadialOneExcess proves the exact natural slack:

```text
f=T+1, r=k+2+a, c=1+d, b=2k+3+e, a+d+e=3.
m=k-q, m<=e+1, p<=a+m+2.
```

At root saturation `r=q+p`, equivalently `p=a+m+2`, distinct empty-block
middles are ambient isolates. Together with a component containing F they
give `c>=m+1`, hence `m<=d`. Outside saturation, inward witnesses from
different empty blocks may share a horizontal carrier: do NOT claim general
nonreuse. These are necessary conditions, not a one-excess exclusion.

### Root-Separated Holes And Covered Boundary

`OneExcessSeparated.lean` proves `q+p+|S|+1<=r+c` for selected hole
middles S separated by actual preserved roots on a missing side, without
assuming root saturation. Nonisolated middles charge distinct extra induced
carriers; isolated middles charge distinct ambient components, plus one
component containing F. Root separation proves nonreuse. Arbitrary witnesses
in a shared root-free gap can reuse a horizontal carrier and cannot be charged
separately. The derived bound is `3f+p+|S|<=9k^2+21k+9`; for k>=5,
`p+|S|>=7` implies f<=T. Existence of a sufficiently large S is NOT proved.
The previous exact three-unit one-excess slack and saturation-only m<=d
remain valid.

`CoveredBoundary.lean` defines actual pure boundary occupancy P, distinct
from the extremal function P(n). It is the sum of pure-carrier lengths,
with `P<=n*p`. Every nonpure carrier has at most two boundary contacts:
`B<=P+2(r-p)` without a size threshold, and `B<=P+E` for n>=5.
For n>=7, `4n-4<=P+2b` and `4n-4<=P+b+2(r-p)`.
These measure the SAME physical resources, not independent charges to add.
Neither this nor the separated-hole theorem is a new unconditional upper bound.

### Concentrated Gaps And Covered Shadows

`ConcentratedGaps.lean` proves `3q+L<=3k+4` for an inclusive root-free interval
of length L on a missing open side (k>=1). Under k>=5, p<=3, f>=T+1 it gives
`L<=16` and `L+6k<=3b-2` (also `L<=3e+7` in the exact slack profile).
Shared inward-carrier witnesses force the intervening interval to be root-free,
excluding inclusive spans >=17 in this branch only. This does not reduce the
whole proof to finite-board search: distant component identifications remain.
Independently, a preserved interval of length L forces at least `floor(L/2)`
actual holes two rows away, for arbitrary disconnected preserved row occupancy.
This local row loss is not globally addable without overlap control.

`CoveredDeficit.lean` defines S as a union of actual boundary holes shadowed by
preserved next-ring vertices, counting shared witnesses once. Here S is the
shadow union, not the earlier selected root-separated middles. For pure boundary
mass P and `D=n*p-P`, n>=7 gives `P+|S|<=4n-4`; at p=4,
`D>=|S|+4`, and with all sides covered `D>=n*(p-4)+|S|+4`.
A top next-ring segment of length L>=2 with endpoints in one actual carrier
and columns in [1,n-2] casts L+2 contiguous boundary holes (n>=5), hence
`D>=L+6` for n>=7, p=4.

Cancellation against the existing contact budget gives `|S|+2p<=b+2r`
(n>=7), not an additional independent charge. For k>=5 the certificate
`|S|+2p+b+2c>=6k+19` suffices for f<=T, but is NOT guaranteed.
At p=4, `|S|<=b` means it forces `b+c>=3k+6`, already stronger than the old
sufficient `b+c>=2k+8`. Do not treat this as a new sharp branch solution:
the actual new value is the physical shadow/length link. Both upper branches
remain open, with no new unconditional numerical bound.

### Formal Terminal Repair

`RailRepair/Geometry.lean` proves coordinates, deep placement, and physical
support intersections; `Forest.lean` proves unconditional forced acyclicity;
`Score.lean` proves inner count `3s^2+1+floor(s/2)`, full score G(s), parity
gain, six-width difference, and the uniform lower endpoint L(k), k=s+1.
This backs the existing paper single-terminal repair uniformly, including
nonempty X pockets. It does not formalize the separate propagating alternative
or the research note's separate formulas for r and c.

### Historical Lower Seed Ledger

`Constructions/ResidueTwo/Staircase/ComponentLedger.lean` proves:

- `Ffull_compl_boundaryDeficiency`: b=5 uniformly for the checked staircase.
- `Ffull_component_sum`: `r+c+3*((s+1)/2)=6*s+7`, s>=2, side n=3s+5.
- `seed_two_profile`: n=11, f=48, r=9, c=7, b=5.
- `seed_three_profile`: n=14, f=76, r=12, c=7, b=5.
- `componentCost_step_two`: the ACTUAL family's combined r+c grows by 9
  when s grows by 2 (side grows by 6).
- `Ffull_card_step_two`: the actual preserved score grows by `12s+37`,
  one less than the target growth `12s+38`.

Seed component counts use kernel-checked induced edge counts of the two
fixed witnesses (39 and 64), then the forest ledgers. They do not enumerate
configurations or compute the connected-component quotient by brute force.

Separate uniform formulas for r and c have NOT been proved. The expected
formulas are r=4+2s+ceil(s/2) and c=4s+3-4ceil(s/2), but do not advertise
them as checked. No six-width geometric closure invariant is proved.

## Verification Status Right Now

Historical targeted builds passed, including:

```bash
LEAN_NUM_THREADS=2 lake --wfail build \
  GridGraphs.Accounting.BoundarySix.Upper \
  GridGraphs.Accounting.CarrierLayers.Counterexamples \
  GridGraphs.Accounting.CarrierLayers.RadialSide \
  GridGraphs.Constructions.ResidueTwo.Staircase.ComponentLedger

LEAN_NUM_THREADS=2 lake --wfail build GridGraphs.Tests.Regression
```

The last command was rerun after adding the component-step lemmas and passed.
Root `GridGraphs.lean` imports the new leaf modules, so all new helpers are
reachable. Regression tests cover the new upper bounds, global p>=3 condition,
the conditional three-carrier bound, b=6 next-ring uniqueness, and c=7 seeds.

The latest full strict command in ROADMAP.md, including the five modules outside
the aggregate closure, passed after integrating ConcentratedGaps and
CoveredDeficit: **8,941 jobs, zero warnings/errors, exit 0**.
The inventory is 234 modules / 84,372 lines under GridGraphs, plus the 179-line
root (235 library files / 84,551 lines total). The two new modules have
297 and 244 lines, with 7 and 9 public theorems respectively, all below 1,000.
The 11 pre-existing oversized modules listed in lean/STATUS.md were untouched.
Root and Regression import both new modules. New regressions give row occupancy
<=7 two rows away from an L=4 interval on a 9x9 board, and f<=110 at k=5
under shadow-cost threshold 49. They retain the symbolic lower/upper interval and lower
regressions at sides 17, 20, 23, 29, plus the existing upper restrictions.

All 163 public theorems in the 31 audited modules passed strict `#print axioms`
checks: the previous 72+31+44 were rerun alongside all 16 new public theorems;
dependencies are subsets of `propext`, `Classical.choice`, and `Quot.sound`.
No `sorryAx` or native proof axiom appeared. Logs:

- `/tmp/opencode/u1-u3-l2-gap-shadow-full-build.log`
- `/tmp/opencode/u1-u3-l2-gap-shadow-previous72-axioms.log`
- `/tmp/opencode/u1-u3-l2-gap-shadow-previous31-axioms.log`
- `/tmp/opencode/u1-u3-l2-gap-shadow-previous44-axioms.log`
- `/tmp/opencode/u1-u3-l2-gap-shadow-new16-axioms.log`
- `/tmp/opencode/U1U3L2Audit.lean`
- `/tmp/opencode/U1U3L2MissingSideAudit.lean`
- `/tmp/opencode/U1U3L2RailRepairAudit.lean`
- `/tmp/opencode/U1U3L2GapShadowAudit.lean`
- `/tmp/opencode/u1-u3-l2-gap-shadow-source-lengths.log`

Private helpers are covered transitively where used, not individually printed.
`RailRepair.attachment_subsingleton` is axiom-free. This is not a library-wide
audit; six legacy `native_decide` uses in three separately built counterexample
tests are outside these 163 audited results.
See [Lean STATUS](../lean/STATUS.md), [README](../lean/README.md), and
[EVIDENCE](../lean/EVIDENCE.md) for the verified snapshot and audit coverage.
These are recorded verification results, not a build rerun for this docs update.

## Next Concrete Goals

1. U3: exclude one-excess configurations using a+d+e=3, the root-separated
   charge, and concentrated gaps <=16. Develop global gap-loss accounting from
   actual two-row holes with overlap control and distant component identities
   retained. Prove enough separated holes or another obstruction; bounded gaps
   are not a finite-board reduction. Use m<=d only at saturation.
2. U3: address the all-sides-covered branch. At f>=T+2 there are four distinct
   actual pure carriers covering the open sides. Use actual pure mass P,
   nonpure contacts, radial roots, and the new physical shadow/length link
   without adding overlapping charges. The p=4 shadow-cost certificate is
   already inside the old sufficient high-budget branch, not a new solution.
3. L2: find a propagating rail/attachment repair compatible with both n11/n14
   seed branches and gain 12s+38 (12k+26) per six-width step. The terminal
   repair is formally verified but gains only once; its attempted repetition collides through existing
   attachments. Change those attachments or relayout the geometry, tracking the
   actual component partition and allowing unattached components. Neither fixed
   c=7 nor a single main component is a required invariant. The separate paper
   propagating-interface sweep pays for the attachment cut without recovering
   the needed center; it is not a successful actual-gain candidate. Following
   the notch tests, jointly free the remaining tail from `(h,s+6)` and the
   right endpoint/frame continuation `(h+1,h+2..h+4)`, with h=3s. Retain an
   independent output after the last join and pay for deletions and Delta b.
   The current paid continuation is count-neutral, not a gain mechanism.

## Lower Research Caution

The read-only lower agent returned a flawed seam-pocket analysis: it treated
preserved vertices as isolated and omitted the always-present center vertex
when counting component mergers. NONE of that purported obstruction was
formalized or added to the roadmap. Do not reuse it as a no-go theorem.

Correct insertion accounting: an isolated center plus four isolated neighbors
become one new star, reducing c by FOUR, even with no main-component attachment.
An isolated center with three isolated neighbors and one old-component neighbor
also reduces c by four. Both add one induced carrier and save three total
budget units. Rootless components are allowed. The exact insertion criterion
is in `Surgery/ForcedExchange.lean`.

Do not confuse matching component budgets at the two seeds with a proved pump.
The stable exact diagonal formula, sharp upper bound, and target lower family
remain open.
