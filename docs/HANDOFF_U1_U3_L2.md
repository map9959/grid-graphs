# U1, U3, And L2 Checkpoint

Date: 2026-09-07. Updated after EndpointUpper and final full strict verification.
The global upper is now `T+floor(2k/3)` for every k>=5, without b/c/r or
coverage premises. Entire missing-side T closure and the formal lower are unchanged.

## Latest Continuation

**Computation checkpoint:** See [RUST_CERTIFICATE_CORPUS.md](RUST_CERTIFICATE_CORPUS.md)
for the bounded Rust corpus tool and source/witness audit. Historical exhaustive
records claim P(17)=110, whereas [110,113] is the current Lean interval. Do not
describe the historical 110 as merely a beam-search incumbent, or the new
primal replay as an independent reproduction of the historical UNSAT result.
The byte-identical unmirrored source and old result artifacts are preserved.

**Newest clean-strand checkpoint:** Read
[PAPER_CLEAN_METRIC_CLOSURE.md](PAPER_CLEAN_METRIC_CLOSURE.md) and
[PAPER_CLEAN_ALLOCATION.md](PAPER_CLEAN_ALLOCATION.md) first. All narrow banks
are now paid without an epsilon remainder. Under K=r+b+c<n, at most thirteen
wide banks remain; their named rectangle overlaps are discounted jointly
with zero error. Boundary-exposed banks have a six-unit-per-bank payment,
and the explicit full-height two-root moving seam gives f<=T+10 even under
arbitrary feasible additions. The common-root and boundary-exposure
hypotheses must not be dropped.

The current gap is a joint payment for partial wide-bank terminals and
their height-weighted fronts. Actual root restoration leaves incidence-cycle
and singleton-restoration costs; interior windows retain escaping components.
The available fragment pool is s_B-(q_B-1), not a new full s_B alongside
protected boundary units. A vertex-disjoint carrier-path cover can discard
too much packet area to be funded by one unit per fragment. An edge-path
cover retains packets but may reuse carriers. Neither is a global closure.

[PAPER_MAXIMUM_CLEAN_UPPER.md](PAPER_MAXIMUM_CLEAN_UPPER.md) proves the exact
support-intersection criterion and a tie-broken maximum translation lemma.
Repeated attachments can block a slide even for a pendant wide-bank hull.
[PAPER_TERMINAL_TRANSPORT.md](PAPER_TERMINAL_TRANSPORT.md) shows why legal
carrier contraction does not erase longitudinal metric cost; its assigned
loads are not claimed actual seam demands. All four notes were independently
reviewed through their final appendices. No unconditional constant theorem,
new Lean build, or optimization is claimed; grid checks stayed at side 14
or below. Earlier formal bounds and verification totals remain unchanged.

**Newer upper-only checkpoint:**
[PAPER_ISOLATE_ROUTING_UPPER.md](PAPER_ISOLATE_ROUTING_UPPER.md) has a reviewed
simultaneous donor allocation with no isolate-count error. Use its retained
clean bank, not a previous certificate that spends V_rem or T_rem again.
This gives T+6 with arbitrary isolates when clean through strands are long;
the clean short-strand obligation remains open. Its endpoint-resource
appendix retains additional private port and join-surplus payments.

[PAPER_GLOBAL_CAP_PAYMENT.md](PAPER_GLOBAL_CAP_PAYMENT.md) proves backed-fold
and specified flat-packet cases, and a restricted T+floor(k/3)+4 bound.
Review refuted the original unrestricted flat-packet isolate transfer:
an outer packet anchor can be J_4. That transfer is withdrawn; the explicit
outer-J_3 version passed re-review. The packet's 3t_F and four 3/4 endpoint
slots are the same credit, never additive.

[PAPER_GLOBAL_METRIC_UPPER.md](PAPER_GLOBAL_METRIC_UPPER.md) gives disjoint
distance-four width charges and a wider replacement-carrier example. It
does not prove every low-budget configuration exposes enough such windows.
All three complete notes received independent review, including corrections.
No unconditional constant bound or Lean change is claimed. Bounded checks
and strip experiments stayed within dimension 15.

**2026-09-08 upper-only research:** The next active route is
[PAPER_DUAL_UPPER_RESEARCH.md](PAPER_DUAL_UPPER_RESEARCH.md). The connected
UU-edge dual, pruned once, decomposes into straight corridors, bend strands,
and actual junctions. Reviewed paper theorems give T+3 without junctions and
T+6 for several isolate-free classes with unboundedly many through strands.
The opening table states the separate hypotheses. This is not a universal
constant-gap theorem, even under the assumption of no isolated holes.

The global metric conversion is A^2=3X_2+Q_exc, Q_exc<=10(r+b+c), A=n-1.
An adequate straight-length budget gives 3(f-T)<19+D. Matching/rank and
boundary accounting pay all but specified interior corridor ends. Pendant
paths pay non-immediate caps; literal boundary witnesses pay several shallow
cap types; axial insets pay sufficiently deep caps. Remaining immediate caps
can be backed by preserved pure boundary intervals, so a fresh hole token per
cap is false. Spare length and matching credit cannot be spent separately.
Isolate-induced routing remains open despite the valid exceptional-area bound.

Independent reviews covered the complete dual argument through the final
cap appendix. They corrected the definition of complement-separating rods to
exclude full boundary rods; subsequent reviews found no mathematical errors.
The new [contact](PAPER_CONTACT_CHARGING_RESEARCH.md) and
[projection](PAPER_PROJECTION_UPPER_RESEARCH.md) notes were also reviewed.
[Nested-cycle research](PAPER_NESTED_CYCLE_UPPER_RESEARCH.md) records additional
scoped obstructions. No Lean build or optimization was run, and no literal
example above side 14 was checked. All formal totals below remain unchanged.

**Latest PAPER-only continuation:**
[PAPER_HALF_COEFFICIENT_UPPER.md](PAPER_HALF_COEFFICIENT_UPPER.md) contains
the full audited argument for `P(3k+2)<=T+floor(k/2)+1`, now for every k>=3.
The new bound is NOT a Lean theorem. The original k>=5 contradiction proof
was simplified: shift every interior row at position 2 modulo 3, rather than
only an initial occupied chain. At deep height 1 modulo 3 this schedules any
number of rows. Each middle-boundary auxiliary path is nonempty even without
coverage: either it has a hole or an adjacent preserved pair forces a pure
carrier. Thus `BAD<=b+p-8` and the GOOD cap are unconditional.

**Latest continuation toward constant gaps:**
[PAPER_FAULT_LINE_ANALYSIS.md](PAPER_FAULT_LINE_ANALYSIS.md) now has a complete
58-state certificate for `TOTAL_F<=2N+2` in the five-column strip with column
3 unpreserved and column 4 arbitrary. It was independently reviewed, including
all 928 transitions. The stated square-family reduction gives `f<=T+4` even
with arbitrarily many rail interruptions. Phase switches and arbitrary fault
networks are not covered. A separate feasible loss-two example disproves
single-phase deletion stability; it does not refute constant-excess stability.

[PAPER_POSITIVE_LOSS_UPPER.md](PAPER_POSITIVE_LOSS_UPPER.md) records the joint
bound `2 BAD_H+3 BAD_V<=6Lambda`, refined physical-contact accounting, and a
refutation of its originally proposed universal nonnegative-loss certificate.
Full deep horizontal rows 1,4,...,N with an empty annulus violate that
certificate for every fixed constant, while having negative excess. Thus only
the positive-excess restriction is a live candidate. Its required geometric
inequality remains unproved. Canonical contacts retain their full signed
surplus; every actual hole has at most two preserved neighbors, necessarily
opposite. Generic degree-three/four connector reasoning is unnecessary here.

[PAPER_PACKING_STABILITY.md](PAPER_PACKING_STABILITY.md) retains the exact
signed identity `4(f-T)+c+h+K+Lambda+Omega=2k+11`, with actual nonnegative
reserves. It gives a physical vacancy/run decomposition of Lambda and warns
that auxiliary UU mirrors are not forced edges: converting their components
to physical merger counts introduces a subtraction for those virtual edges.
The new fourth-step propagation law bounds column-labelled interior
terminations by `3Lambda`, without treating these continuations as physical
paths. The [endpoint strip](PAPER_ENDPOINT_STRIP.md) is closed by a complete
22-state/176-transition potential certificate, independently audited on paper.

[PAPER_ZERO_LOSS_UPPER.md](PAPER_ZERO_LOSS_UPPER.md) now proves on paper
`Lambda=0 => f<=T+3` for k>=3 and, using the checked coverage input,
`f<=T+1` for k>=5. Independent classification and physical-contact reviews
found no fatal gap. Residue-one good rows vanish, leaving nested upper bands,
an optional inactive corridor, and nested lower bands. Actual deep components,
including singleton intersections extending into the annulus, each receive
two distinct physical contacts. Their forest rank gives `c_A>=d+1`.
The stable arithmetic is `6(f-T)+3p+3h+c<=23`. No virtual UU mirror edge
is used in that contraction. Positive Lambda is NOT covered by this proof.

[PAPER_CONSTANT_GAP_LOWER.md](PAPER_CONSTANT_GAP_LOWER.md) records a different
nested-frame obstruction and a moving-phase cell with exact `12k+26` count
growth. Its nonboundary interior is a forest, but the displayed cap has
cycle rank k+1. It is not a feasible witness. Constant-gap lower construction
remains open. [PAPER_MOVING_PHASE_CAP.md](PAPER_MOVING_PHASE_CAP.md) adds a
fixed-interior top-cap obstruction and bounded side-11/14 computations; it
does not rule out distributed count-balanced interior exchanges. The latest
paper and bounded experimental continuations ran no Lean builds or
optimization above side 15. All verification totals below still describe
the previous formal milestone, not these paper arguments.

[PAPER_DISTRIBUTED_LOWER_REPAIR.md](PAPER_DISTRIBUTED_LOWER_REPAIR.md) and its
new packaged experiment/test investigate count-balanced endpoint shifts that
preserve GOOD exactly. Descending seams expose isolated centers, but two
insertion ports are connected through four rods and the frame. This refutes
the specified promotion family, not distributed exchanges generally. The
bounded checks use sides 11/14 and explicit node caps; the main-agent focused
and layout run passed 10 tests. No constant-gap lower witness was obtained.

**Latest checked upper result:**
`GridGraphs.maxPreserved_residueTwo_le_endpoint_refinement` in
`Accounting/EndpointUpper.lean` proves `P(3k+2)<=T+floor(2k/3)` for ALL k>=5.
`GridGraphs.forced_card_le_endpoint_refinement` is the feasible-set version.
The namespace is `GridGraphs`, not `GridGraphs.EndpointUpper`. All three old
k%3=1 endpoint profiles are closed; no b/c/r/coverage assumptions are exported
by the global theorem. This is not the full sharp T theorem.

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

The preceding two modules are `CarrierLayers/ConcentratedGaps.lean` (7 public
theorems, 297 lines) and `CarrierLayers/CoveredDeficit.lean` (9 public theorems,
244 lines). They bound concentrated root-free gaps and link physical boundary
shadows to carrier length. Their conditional certificates and local losses do
not close either upper branch or improve the numerical bounds.

The preceding five modules are `CarrierLayers/GapGlobalCapacity.lean`,
`GapGlobalExclusion.lean`, `GapGlobalMinimal.lean`,
`CoveredGlobalMissingSides.lean`, and `GlobalUpperProfiles.lean`.
For EVERY feasible f>=T+1 set, k>=5, they prove at most one missing open
side, at least three physically covered sides, p>=3 (old threshold k>=7),
and r>=k+3 (old k+2). The entire p=3, r=k+2 branch is excluded for ANY c.
That milestone's counterbudget was `b+c+3*excess<=2k+9` for excess>=1, f>=T+excess.
That milestone proved the b>=6 branch bound `f<=T+floor((2k+1)/3)` and
classified the old global endpoint `T+floor((2k+2)/3)` at k%3=2 as exactly
that score with `(r,c,b)=(k+4,1,5)`. That implication remains valid, but its
old-maximum premises are now impossible, including f>=114 at n=17.

**Previous global upper:** `GridGraphs.BoundaryFive.maxPreserved_residueTwo_le`
proves `P(3k+2)<=T+floor((2k+1)/3)` for **all k>=5 and all boundary budgets**,
not only b>=6. The generic Near/Second hole pattern positions only the gap by a
square isometry preserving cardinality and forced acyclicity. The old endpoint
profile is then reapplied to the mapped set to obtain b=5,c=1. Its actual oriented
perimeter path and inward spokes force a nonpure singleton at `z=(2,2)`;
singleton capacity contradicts the old endpoint. No canonical orientations of
the other holes are assumed. This excludes `(k+4,1,5)` in its k%3=2 old-maximum
context, **not all b=5,c=1 sets**. The second-short corner packet is now checked;
there is still no generic ambient b=5 strict n-5 cap theorem.

`GridGraphs.CarrierLayers.FourCarrier.card_le_target_of_four_pure_missing_side`
closes the full p=4 missing-side branch with f<=T for every k>=5, including k=5.
The off-side path bound `p<=u+1` is formal, with u counting ordinary off-side
holes including corners. Its historical `missing_side_counterexample_pure_eq_three`
reduction left exactly p=3 and score T+1; ThreeCarrier now excludes those premises.

**Previous missing-side milestone (unchanged):**
`GridGraphs.CarrierLayers.ThreeCarrier.card_le_target_of_missing_side` in
`ThreeCarrier/Closure.lean` proves **f<=T for every missing open side, k>=5,
without any p or off-side cost W assumption**. Missing still means no pure
carrier meets the open side, not zero preserved occupancy. No maximality or
connectedness is assumed beyond forced-graph acyclicity. W2/W3/W4, mixed/top
cases, and k=5 equality are all closed; no missing-side proof work remains.

Every stable counterexample f>=T+1 is now **all-four-sides-covered**, with
**p>=4, r>=k+4, d=r-p-h>=k**, h counting actual shallow nonpure carriers.
`GridGraphs.CarrierLayers.stable_excess_budget` in `AllCoveredCounterexamples.lean`
proves **b+c+3e<=2k+8 for every e>=1 and f>=T+e**, without a coverage premise.
Annulus proves global B+E<=4n-9 for n>=9 and the physical deficit inequality
r+5<=2K+D. The earlier b>=7 bound f<=T+floor(2k/3) is now global by
EndpointUpper, including P(23)<=200 and P(32)<=376. The old k%3=1 profiles
`(r,c,b)=(k+5,1,5), (k+4,2,5), (k+4,1,6)` are ALL excluded, as detailed
below. Their necessary-profile implications remain valid with impossible
old-endpoint premises; they are not constructions or remaining tasks.

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

**Verification complete:** main full strict build passed **9,049 jobs, zero
warnings/errors, exit 0**. Audits cover **584 public theorems + 50 definitions +
3 abbreviations + 5 structures = 642 unique public declarations**,
not 642 theorems. Inventory: **342 modules / 100,477 lines**, plus the
**188-line root: 343 files / 100,665 lines total**. All 40 new modules are
in the aggregate closure; only the original five legacy targets lie outside.
Details and audit limits appear below. No build is active.

**PROOF NOT FINISHED:** only the all-covered sharp upper branch and the
target-count lower family/pump remain open. The remaining upper range is
`f=T+e, 1<=e<=floor(2k/3)`, not the excluded old endpoints. L(k) is unchanged.
[Paper Upper Program](PAPER_UPPER_PROGRAM.md) marks the old missing-side
mixed/top program **HISTORICAL, CLOSED** and explains the actual formal resolution.

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
That main-agent run passed 19 tests without searches during tests;
the note separately records its deliberately one-node budget-status test.
These new lower results remain finite/paper evidence, not Lean theorems.

The [terminal tail interface](L2_TERMINAL_TAIL_INTERFACE.md) improves the n=14
rootless-output candidate to 76 centers with a genuine 43-vertex rootless
component and a separate frame-attached cap. The paper family for s>=3 still
gains only 12k+25 per six-width step, not an accumulating target pump.
Ten bounded searches ran only at n=11/14; nine completed exhaustively in
their restricted windows. The n=14 joint joined-output search hit its
100,000-node budget, so its 76 is a lower bound, NOT a maximum. No global
optimum or uniform no-go follows. The historical main-agent run passed 23 tests
without optimization searches during tests (explicit replays and one-node
cutoff checks). No new Lean lower result follows from this finite/paper work.
No Python application files changed; the previous 23 tests were not rerun.
Earlier bounded finite-capacity certificate experiments used coordinates at most 13,
not a full-grid optimizer. No Python search or tests ran in the recorded
verification pass or this documentation update.

## What The Route Labels Mean

These labels refer to the latest research plan, not similarly named stages in
older roadmaps. The canonical definitions are in
`ROADMAP.md`, under **Research Route Labels**.

| Label | Meaning | What would complete the route |
|---|---|---|
| **U1** | **Boundary-six control:** classify boundary/next-ring geometry and combine all boundary-budget branches. | Global `T+floor(2k/3)`, all k>=5, no b/c/r/coverage premises. The old b=6 endpoint is fully closed, including E=1 position 3. All-covered sharpness remains open. |
| **U2** | **Boundary-five attachment rigidity:** use generic boundary geometry and real inward spokes, not assumed canonical normalization. | Both old k%3=1 b=5 endpoints are closed; the old k%3=2 endpoint stays closed. Actual two-short packets and the endpoint deep-root bridge are checked. Generic b=5,c=1 gives r>=k+6 for k>=7 without a score premise, not impossibility. Strict cap needs UniqueBoundaryRoots, not merely ambient b=5. |
| **U3** | **Global near-extremal packing:** trade off carriers, layer occupancy, and forced components without resource reuse or boundary-budget assumptions. | Missing-side f<=T is closed, k>=5, without p/W assumptions. Remaining `f=T+e`, `1<=e<=floor(2k/3)` is all-covered, p>=4, r>=k+4, d>=k, and b+c+3e<=2k+8. Seek quantitative nonreused losses beyond the excluded old endpoints. |
| **L1** | **Relayout the staircase:** move rails/attachments so its uncovered vertices admit additional legal promotions. | An explicit target-count family with a uniform forest proof. The terminal parity repair is now formal, but does not reach the arbitrary-width target. |
| **L2** | **Six-width pumping:** use compatible 11x11 and 14x14 seeds and prove a geometric `k -> k+2` operation gaining `12k+26` preserved vertices. | All-width closure, count, and acyclicity. Formal L(k) and the new paper tail/cap family still gain only `12k+25`. The 76-center n14 rootless output improves the interface, not the formal lower formula; an accumulating pump remains open. |
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

## Earlier U1 Milestone (Historical Bound)

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
The preceding BoundaryFive pass improved the global upper to `T+floor((2k+1)/3)`
for every k>=5. Annulus/ThreeCarrier left that formula and L(k) unchanged;
EndpointUpper now improves the upper to `T+floor(2k/3)`, leaving L(k) unchanged.
Throughout, the stable target is T=3k^2+7k, never T-1. Current bounds are:

| Side | Formal lower | Global upper |
|---:|---:|---:|
| 17 | 110 | 113 |
| 20 | 149 | 154 |
| 23 | 195 | 200 |
| 26 | 246 | 253 |
| 29 | 304 | 312 |
| 32 | 367 | 376 |

The current upper at side 35 is 447.

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
The historical and current module groups are distinguished below. All current
modules passed the final full strict build with warnings treated as errors.

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
  is the historical unconditional upper bound above. It covers ALL boundary budgets
  and remains valid, superseded by BoundaryFive in the stable range.

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

### Historical Missing-Side And One-Excess Reductions

The one-excess premises in this and the following older reductions are now
impossible by ThreeCarrier.Closure. They are valid infrastructure, not open cases.

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

The earlier GapGlobal results forced p=3 and a>=1, eliminating all four a=0 types
(d,e)=(0,3),(1,2),(2,1),(3,0). Set A=a-1 to derive
`r=k+3+A, c=1+d, b=2k+3+e, A+d+e=2` at p=3. This shifted form is
an algebraic consequence, NOT a new named Lean API. In particular c<=3 and
e<=2; the historical c=4 implication now has impossible premises.

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

With the new e<=2 consequence, `L+6k<=3b-2` gives the derived bound
`L<=13` in this same branch. The named L<=16 theorem remains valid; the
improved derived bound is not a new named API or a finite-board reduction.

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
the actual new value is the physical shadow/length link. These modules alone
did not close either branch; now only the all-covered sharp upper remains open.

### Global Capacity, Coverage, And Profiles

All endpoints here are in namespace `GridGraphs.CarrierLayers`.
`GapGlobalCapacity.lean` defines `nextRingCarriers F`: nonpure actual induced
carriers with no deep vertices, possibly including boundary endpoints.
For h equal to their count it proves, using natural subtraction,

```text
f <= B+E+(n-4)*(r-p-h)             (n>=5)
f <= 4n-4+(n-4)*(r-p-h)           (n>=7)
h <= a                           (k>=5, p=3, f>=T+1, r=k+2+a).
```

Deep capacity is removed once per actual shallow carrier, not once per hole
or inward witness. Reusing an inward carrier on one side forces it to be
shallow. `GapGlobalExclusion.lean` uses h=0 to obtain arbitrary-hole nonreuse
and first excludes the connected p=3, r=k+2 case. This intermediate result
is superseded in scope by `GapGlobalMinimal.lean`:
`card_le_target_of_three_pure_minimal_induced` proves f<=T for p=3,
r=k+2, every k>=5, ANY c, with no assumption that corners are preserved.

The mechanism is the actual boundary-injection image partition. At h=0,
preimages mapping onto a fixed open side belong to distinct nonpure carriers.
Writing H_s for actual holes on that side gives
`B+E+H_s<=4n-4+(r-p)`. Corners stay in the off-side part. At a missing
side H_s>=2k; combined with deep capacity at p=3, r=k+2 this contradicts
f>=T+1 throughout k>=5. This counts unused holes, not an additional
independent deficiency charge.

`CoveredGlobalMissingSides.lean` proves two distinct missing open sides have
disjoint holes giving b>=4k. The counterbudget excludes that for f>=T+1,
k>=5. Its endpoints `stable_counterexample_missing_sides_subsingleton`,
`stable_counterexample_three_le_covered_sides`,
`stable_counterexample_three_le_pure_carriers`, and
`stable_counterexample_induced_components_ge` give at most one missing side,
covered>=3, p>=3, and r>=k+3. The p>=3 threshold improves from k>=7;
the r bound improves from k+2. Covered sides require distinct physical pure
carriers. No maximality, boundary-budget, or connectedness premise is added.

`GlobalUpperProfiles.lean` proves `residueTwo_global_counterexample_budget`:
`b+c+3*excess<=2k+9` for k>=5, excess>=1, f>=T+excess.
`residueTwo_card_le_of_boundaryDeficiency_ge_six` gives the entire b>=6
branch bound `f<=T+floor((2k+1)/3)`, not a new global upper formula.
`residueTwo_old_upper_endpoint_profile` gives, for k%3=2 and
f>=T+floor((2k+2)/3), exact equality and `(r,c,b)=(k+4,1,5)`.
At that historical milestone the n=17 endpoint was 114 with r=9,c=1,b=5.
The next result excludes its old-maximum premises, not the profile theorem itself.

### Boundary Five Upper

The previous `Accounting/BoundaryFive/` chain contains eight modules: `GapPosition`, `Symmetry`,
`Perimeter`, `Inward`, `TopSingleton`, `SingletonBound`, `Endpoint`, and `Upper`.
The checked proof uses actual arbitrary feasible sets, not a canonical frame:

1. `holes_eq_insert_second` gives four Near corner witnesses and one Second
   hole adjacent to a witness, for n>=9 and b=5, without fixing other-hole orientations.
2. `exists_top_gap_pullback` uses a square isometry to place the two gap holes
   at `(0,1)` and `(0,2)`. It transports only cardinality and forced acyclicity,
   not a component/deficiency profile or a full canonical boundary pattern.
3. At k%3=2, reapply `residueTwo_old_upper_endpoint_profile` to the mapped
   old-endpoint set. This supplies b=5 and c=1 rather than assuming them.
4. The oriented actual perimeter path and real inward spokes force preservation
   of `z=(2,2)`. An off-boundary path would contradict uniqueness of the
   boundary-only path in the forest, excluding z's preserved neighbors.
   `top_gap_singleton` therefore gives an actual nonpure singleton induced carrier.
5. `card_add_side_le_of_singleton` proves `f+n<=(n-4)r+12` for n>=10, b=5,
   and a nonpure singleton. `old_upper_endpoint_no_nonpure_singleton` and
   `old_upper_endpoint_false` use this to contradict the old endpoint capacity.

`GridGraphs.BoundaryFive.forced_card_le_residueTwo_bound` and
`maxPreserved_residueTwo_le` conclude `f<=T+floor((2k+1)/3)` and the same bound
for P(3k+2), **every k>=5 and every boundary budget**. The improvement is one
when k%3=2; at other residues those historical floors agree. This does not
exclude all b=5,c=1 sets. The newer corner-packet and conditional strict-cap
results below do not prove a generic ambient `f<=(n-5)r+11` theorem.

### Four-Carrier Closure

`Accounting/CarrierLayers/FourCarrier/` contains 24 modules culminating in
`Closure.lean`. `pure_carriers_le_offside_holes_add_one` in `OffsidePath.lean`
(namespace `GridGraphs.CarrierLayers.FourCarrier`) proves
`p<=u+1` for n>=2 on a missing side. Here u is the number of **ordinary** holes
on the complementary perimeter path, including all four corners, not weighted
boundary deficiency. This path theorem needs no acyclicity assumption.

The physical image budget excludes p=4 missing-side counterexamples for k>=6.
At the residual k=5 equality, two shallow preimages force a deep second-position
root. Zero total deep deficit fills its radial axis; the actual boundary six-cycle
then contradicts feasibility. The resulting public endpoints are:

- `four_pure_missing_side_counterexample_false`: no p=4 missing-side set above T,
  for all k>=5, including n=17.
- `card_le_target_of_four_pure_missing_side`: every feasible p=4 missing-side
  set satisfies f<=T, with no one-excess assumption required in the conclusion's API.
- `missing_side_counterexample_pure_eq_three`: the historical missing-side
  counterexample reduction gives exactly p=3; its premises are now impossible.

Together with MissingSideSharp, this historically left score T+1. The next
proof closes that case too; the old A+d+e=2 and L<=13 restrictions no longer
describe an open branch. The newer endpoint corner packets are distinct from
this completed missing-side proof; a generic ambient b=5 n-5 cap is not claimed.

### Entire Missing-Side Closure

The new `ThreeCarrier/` chain derives its geometric inputs from a hypothetical
counterexample, rather than assuming a rod list, root phase, or pure count.

1. **W2:** the enlarged nonpure rectangle includes missing-side roots, their
   spokes, the next ring, and shallow horizontal carriers, not just the deep
   square. Former top deep-row exceptions become interior rows. Actual
   horizontal edge rows inject into at most three horizontal nonpure carriers;
   nearby shadows are handled jointly by the height-independent
   `MixedPacking.rectangular_three_rod_edge_bound`. Thus
   `V+H<=(k-1)(3k-1)`. The actual nonpure forest ledger and pure mass close
   W2, including k=5, without a residual equality case (`CostTwoClosure.lean`).
2. **W4:** `Annulus.counterexample_deep_carriers_ge` supplies global d>=k.
   The connected shallow-carrier argument in `CostThreeReduction.lean`
   contradicts the W4 profile. It is not a new connectivity assumption on F.
3. **W3:** the extra off-side hole stays **unclassified**. `CostThreeDefect.lean`
   charges bad vertical and bottom horizontal edges jointly to its two incident
   boundary edges, so their total is **<=2, not <=1**. The mixed bound is
   `V+H<=(k-1)(3k-1)+2`. The nonpure ledger gives
   `f<=10k+4+(k-1)(3k-1)=T-k+5<=T`, including k=5. The eight-case
   extra-hole adjacency classification is unused, unformalized, and unnecessary.
4. **Unrestricted closure:** `ThreeCarrier.card_le_target_of_missing_side`
   combines this with the prior FourCarrier closure, giving f<=T for all
   k>=5 with no p/W assumptions. `counterexample_all_sides_covered` then
   forces actual pure coverage of every open side at every positive excess.

No W2/W3/W4, mixed, top-position, or equality gap remains in this branch.

### Annulus And All-Covered Budgets

For n>=9 let A be the full two-layer annulus, S its selected preserved set,
and B/E the preserved boundary/next-ring occupancies. Set
`K=4n-4-B-E`, let rA/cA be induced/ambient annulus component counts, and
let i/o count selected inner/outer annulus corners. `Annulus/Cap.lean` proves
the exact cubic ledger `2|S|+rA+cA+i=|A|+o`, global `B+E<=4n-9`,
`K>=5`, and `rA+cA+4<=2K`. The cap has no boundary-budget or coverage premise.

`Annulus/Bridges.lean` counts literal longitudinal edge packets of M actual
full deep rods in the physical forest restricted to the annulus and those
rods. Each contributes n-4 deep vertices and n-3 edges. Disjoint packets and
the forest ledger give **M+1<=cA**, including annulus isolates; additional
lateral attachments are allowed. No quotient/contact forest is assumed.
With `D=(n-4)d-|F_deep|`, `Annulus/Deficit.lean` proves d<=M+D and
p+h<=rA, hence **r+5<=2K+D**. This D is total deep deficit, not the older
pure-boundary mass shortfall also called D in CoveredDeficit.

`Annulus/Counterexamples.lean` gives **d>=k globally** at f>=T+1, k>=5.
Combining with all-side coverage, `AllCoveredCounterexamples.lean` exports
`stable_counterexample_pure_and_induced` (p>=4, r>=k+4) and
`stable_excess_budget` (**b+c+3e<=2k+8 for all e>=1**, f>=T+e).
These are global necessary conditions, not an exclusion of all-covered sets.

`Annulus/Upper.lean` proves b>=7 implies `f<=T+floor(2k/3)` and classifies
the previous k%3=1 endpoint into three profiles. EndpointUpper now excludes
all three and makes the bound global; the side-23 interval is [195,200].
The older k%3=2 `(k+4,1,5)` endpoint remains excluded in its old maximum
context, not as a ban on every b=5,c=1 set.

### EndpointUpper Closure

All profiles here refer to the OLD k%3=1 score `T+floor((2k+1)/3)`.

1. **`(r,c,b)=(k+5,1,5)`:** `BoundaryFive/CornerPacket/Upper.lean` uses
   two actual short carriers and annulus losses. The exposed square isometry
   transports r/c/b, cardinality, and acyclicity, positioning only the gap;
   other corner-hole orientations remain free. Its stronger theorem
   `GridGraphs.BoundaryFive.CornerPacket.connected_boundary_five_components_ge`
   gives r>=k+6 for b=5,c=1,k>=7, without score or residue premises.
2. **`(k+4,2,5)`:** `Rootless/AmbientEndpoint.lean` derives the actual
   ambient-to-rooted-deep bridge. The singleton obstruction puts z=(2,2) in U,
   leaving w=(1,2) an ambient isolate. Ambient/annulus budgets give full deep
   rooting, unique boundary roots, and four deep corners in U; the exact deep
   ledger gives q=k. Four distinct corner-root carriers force all rods long.
   Three-spaced axes and nonreused missing triples contradict total rod deficit,
   including reciprocal and cyclic corner-root orientations at this endpoint.
3. **`(k+4,1,6)`:** `BoundarySix/Connected/Upper.lean` closes the entire
   old endpoint. E=1 and E=0 with an outer corner in U use the connected-annulus
   deep bridge and the same rooted endpoint obstruction. For E=0 with all outer
   corners in F, two distinct actual gaps force two deep corners in F. If neither
   is a singleton, two literal five-edge packets violate the physical perimeter
   forest edge count. An actual singleton and summed annulus deficits then
   contradict capacity, with no distinct-corner-carrier assumption.

`Rootless.strict_carrier_cap` proves the strict m-1 cap on the smaller grid
under `UniqueBoundaryRoots` (m>=2). The actual ambient bridge proves these premises
at the endpoint, NOT generically for ambient b=5 sets. Neither generic b=5,c=1
impossibility nor a generic ambient n-5 cap or `f<=(n-5)r+11` follows.
Reciprocal/cyclic packing is fully closed at the endpoint, not for all rooted
forests. The b=6,E=1 position-3 residual is closed at the old endpoint too:
the earlier position-2-only conjecture was wrong, and the proof handles the
third position without needing a false near-only classification.

`Accounting/EndpointUpper.lean` combines the exclusions with the previous
bound; outside k%3=1 the floors coincide. No full sharp T theorem or
attainability of the new upper endpoint is claimed.

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

The latest full strict command in ROADMAP.md includes the original five modules
outside the aggregate closure and passed with EndpointUpper integrated:
**9,049 jobs, zero warnings/errors, exit 0**, Lean/mathlib 4.33.1. It reused
cached dependencies, not a separate mathlib-wide verification, and ran without
an imposed time limit. The reported targeted EndpointUpper/Regression build
passed **8,882 jobs**, separate from the full count. **No build is active.**
Inventory: **342 modules / 100,477 lines**, plus the **188-line root:
343 library files / 100,665 lines total**.

| New group under `Accounting/` | Modules | Lines | Theorems | Definitions | Abbreviations | Structures |
|---|---:|---:|---:|---:|---:|---:|
| `BoundaryFive/CornerPacket/` | 6 | 1,196 | 30 | 0 | 0 | 0 |
| `BoundaryFive/Rootless/` | 15 | 2,206 | 69 | 12 | 0 | 2 |
| `BoundarySix/Connected/` | 18 | 2,402 | 73 | 10 | 1 | 1 |
| `EndpointUpper.lean` | 1 | 46 | 2 | 0 | 0 | 0 |
| **Total** | **40** | **5,850** | **174** | **22** | **1** | **3** |

All new modules are **31-521 lines**, below 1,000. All 11 old oversized modules
are untouched. Recursive imports confirm all 40 new modules are root-reachable.
The verifier added the otherwise unused valid `BoundarySix.Connected.RingEndpoint`
root import before taking the snapshot; EndpointUpper was already imported.
Only the five original legacy modules remain outside. RingEndpoint's necessary
conditions now have impossible old-endpoint premises, not an open residual.

Regression passed the uniform refined interval, unconditional P(23)<=200 and
P(32)<=376, and unchanged specializations at sides 17, 20, 26, 29, and 35,
alongside all earlier missing-side and component checks. No Regression repair
was needed; older weaker implications remain valid.

The unchanged `/tmp/opencode/TotalCurrentAudit.lean` and
`/tmp/opencode/AnnulusThreeCarrierAudit.lean` reran the previous **441** public
declarations (277+164). `/tmp/opencode/endpoint-upper-final-Audit.lean` checked
**202 new/changed declarations**: 200 in new files plus both Symmetry exports.
The old `exists_top_gap_pullback` is the only overlap, so **441+202-1=642
unique public declarations**, comprising **584 theorems + 50 definitions +
3 abbreviations + 5 structures**. All drivers import only `GridGraphs` and
passed with warnings as errors. Kinds, unique names, and coverage were checked
independently. Dot-named methods are included; generated constructors, recursors,
and projections are not extra source entries. Private helpers are covered
transitively. All dependencies are subsets of `{propext, Classical.choice,
Quot.sound}`, possibly empty, without `sorryAx` or a native proof axiom.

Exact current logs from Lean EVIDENCE (successful build/audit `.exit` files are 0):

- `/tmp/opencode/endpoint-upper-final-full-build.log`
- `/tmp/opencode/endpoint-upper-final-TotalCurrentAudit.log`
- `/tmp/opencode/endpoint-upper-final-AnnulusThreeCarrierAudit.log`
- `/tmp/opencode/endpoint-upper-final-endpoint-upper-final-Audit.log`
- `/tmp/opencode/endpoint-upper-final-inventory.log`
- `/tmp/opencode/endpoint-upper-final-post-audit-check.log`
- `/tmp/opencode/endpoint-upper-final-verification-summary.log`

Source/root/configuration fingerprints, including all 342 modules and every
test, stayed unchanged through build and audit. All **300 old modules other than
Regression and Symmetry** match the Annulus/ThreeCarrier snapshot. Existing Symmetry
intentionally adds the isometry export while preserving its old theorem statement.
This is local Lean source coverage, not a hash of all mathlib artifacts or the workspace.
This is **not a whole-library axiom audit**: six legacy `native_decide` uses
in three separately built counterexample tests remain outside coverage.
See [Lean STATUS](../lean/STATUS.md), [README](../lean/README.md), and
[EVIDENCE](../lean/EVIDENCE.md) for the inventory and audit conventions.
These are recorded verification results, not a build rerun for this docs update.
No Python application files changed. Earlier bounded finite-capacity experiments
used coordinates at most 13, not a full-grid optimizer. No Python or searches
ran in the recorded verification pass or this docs update; the prior 23 tests
are historical, not a new run.

## Next Concrete Goals

1. U3: work on the remaining **all-covered lower-excess range**,
   `f=T+e, 1<=e<=floor(2k/3)`, k>=5. Use p>=4, r>=k+4, d>=k and
   b+c+3e<=2k+8 to organize actual boundary/component slack. Strengthen the
   physical inequality r+5<=2K+D while retaining annulus isolates, literal rod
   packets, shared shadow unions, and carrier identities. No missing-side or
   old-endpoint proof work remains; no remaining excess level is asserted feasible.
2. U1/U2: seek quantitative general corner-packet, long-rod, and frame-budget
   losses beyond endpoint saturation. Do not assume generic ambient unique
   rooting, a quotient forest, or add overlapping charges. Endpoint reciprocal/
   cyclic packing is closed, but not a theorem for all rooted forests. The
   generic ambient n-5 cap and `f<=(n-5)r+11` are not checked consequences.
   Do not inflate the program with the dominated shadow certificate or assert
   that a proposed route reaches sharp T. See [Paper Upper Program](PAPER_UPPER_PROGRAM.md).
3. L2: find an accumulating tail/cap or rail/attachment repair compatible with both n11/n14
   seed branches and gain 12s+38 (12k+26) per six-width step. The terminal
   repair is formally verified but gains only once; its attempted repetition collides through existing
   attachments. Change those attachments or relayout the geometry, tracking the
   actual component partition and allowing unattached components. Neither fixed
   c=7 nor a single main component is a required invariant. The separate paper
   propagating-interface sweep pays for the attachment cut without recovering
   the needed center; it is not a successful actual-gain candidate. The new
   terminal-tail candidate clears the whole terminal rail and adds a separate
   frame cap, recovering a 76-center n14 forest with a 43-vertex rootless output.
   Its paper family still gains only 12k+25. Make the cap/interface improvement
   recur without consuming independence, paying for deletions and Delta b,
   and prove actual incoming/outgoing closure rather than only a family count.

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
