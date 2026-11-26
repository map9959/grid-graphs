# Paper Upper Program

Updated: 2026-09-07, after the verified EndpointUpper milestone.

## New Paper Track

The current clean-strand continuation is in
[Clean Metric Closure](PAPER_CLEAN_METRIC_CLOSURE.md) and
[Clean Allocation](PAPER_CLEAN_ALLOCATION.md). Reviewed proofs pay all narrow
banks, leave at most thirteen wide banks in K<n, remove overlap-capacity
reuse, and close the explicit full-height two-root moving seam at T+10.
The global obligation remains partial-terminal and height-weighted front
payment. A bounded number of banks or fronts is not a constant debt bound.
[Maximum-specific](PAPER_MAXIMUM_CLEAN_UPPER.md) and
[terminal-transport](PAPER_TERMINAL_TRANSPORT.md) continuations identify
additional exact conditions without proving that final payment. No new
unconditional upper formula or Lean result follows.

The newest continuation is the reviewed
[isolate allocation](PAPER_ISOLATE_ROUTING_UPPER.md). Its conservative clean
certificate has no isolate-count error, but clean short-strand debt remains
unpaid in general. [Global cap payment](PAPER_GLOBAL_CAP_PAYMENT.md) adds
constant-bound subclasses and records a withdrawn overbroad packet transfer;
the corrected version requires explicit outer-J_3 anchors. The
[metric continuation](PAPER_GLOBAL_METRIC_UPPER.md) proves width-sensitive
charges without establishing the necessary global exposure theorem.
No unconditional constant bound follows, and the formal milestone is unchanged.

The newest upper-only route is
[Planar Dual Upper Research](PAPER_DUAL_UPPER_RESEARCH.md). Its independently
reviewed corridor geometry gives T+3 and T+6 bounds for explicit classes,
including classes with arbitrarily many junctions and through strands. The
global constant-gap theorem remains open. Its natural target is r+b+c, not
a stronger weighted excess. The unresolved costs are surviving interior caps
and isolate-induced routing; the note gives exact budgets and guards against
counting matching gains and unused corridor length as independent credits.

Companion [contact charging](PAPER_CONTACT_CHARGING_RESEARCH.md),
[projection](PAPER_PROJECTION_UPPER_RESEARCH.md), and
[nested-cycle](PAPER_NESTED_CYCLE_UPPER_RESEARCH.md) notes retain the precise
scope of their identities and failed local proof rules. No new global bound
or Lean verification is claimed by this continuation.

The best unconditional paper argument remains in
[Paper Half-Coefficient Upper Bound](PAPER_HALF_COEFFICIENT_UPPER.md):
`P(3k+2)<=T+floor(k/2)+1` for every k>=3, at paper level. The fixed
residue schedule and nonempty middle-boundary path proof make it independent
of the missing-side reduction. It has not changed the checked global theorem.

[Paper Packing Stability](PAPER_PACKING_STABILITY.md) develops its exact
defect identity and fourth-step propagation. The
[endpoint strip](PAPER_ENDPOINT_STRIP.md) has a complete finite-state paper
certificate. The subsequent [zero-loss proof](PAPER_ZERO_LOSS_UPPER.md)
classifies mixed saturated configurations and counts two actual contacts per
deep component, giving `f<=T+3` for k>=3 and `f<=T+1` for k>=5 when
`Lambda=0`. Independent paper reviews passed; no new Lean theorem is claimed.
The general positive-loss stability estimate needed for `T+O(1)` remains
unproved. Virtual UU mirrors must not be used as physical forced connections.

The [fault-line continuation](PAPER_FAULT_LINE_ANALYSIS.md) proves a uniform
constant bound for one specified interrupted-rail family through a complete
58-state certificate. It permits arbitrary interruptions, but not arbitrary
fault networks or phase switches with preserved vertices in the fixed empty
column. The certificate passed independent paper review.

The [positive-loss contact program](PAPER_POSITIVE_LOSS_UPPER.md) supplies
exact corrections and a joint bad-edge bound. Its original universal
nonnegative-loss target is now REFUTED; restricting to positive excess avoids
that counterexample but does not prove the target. Signed full contact surplus
must be retained, and the weighted contact target is stronger than a bound
on excess alone. No general constant-gap upper is claimed.

The lower-side work is in
[Paper Constant-Gap Lower Research](PAPER_CONSTANT_GAP_LOWER.md). Its new
moving-phase interior has the desired count recurrence, but the proposed
boundary closure creates linearly many cycles. The
[moving-phase cap analysis](PAPER_MOVING_PHASE_CAP.md) shows that arbitrary
replacement of the top two rows, with its specified interior fixed, does not
remove the linear loss. Distributed exchanges remain possible research, not
a proved repair. No constant-gap lower bound is claimed.
The [distributed endpoint-shift attempt](PAPER_DISTRIBUTED_LOWER_REPAIR.md)
preserves GOOD but still has a four-rod attachment collision. Its restricted
failure does not rule out boundary redesign or changed rod rows.
The rest of this document records the formal milestone and its
earlier proof chains, not a formalization of the new paper track.

## Status And Notation

For the square of side `n=3k+2`, let `F` be feasible: the forced graph
`G_F`, containing every grid edge incident to `F`, is acyclic. Write
`f=|F|`, `r` for the number of induced preserved carriers, `c` for the
number of components of `G_F` on **all** vertices (including isolates),
`b` for the boundary deficiency of the complement, and `p` for the number
of carriers wholly in the outer boundary. The exact ledger is

```text
3f+r+c+b = n^2+4n,                 T(k)=3k^2+7k.
```

A missing open side has no pure boundary carrier meeting it; it need not
contain no preserved vertices. All-covered means all four open sides are
met by actual pure carriers. These definitions and the lower history are
from [HANDOFF_U1_U3_L2.md](HANDOFF_U1_U3_L2.md), which records the current
verified milestone and the historical endpoint statements it supersedes.

**Checked and included in the completed full strict aggregate build:**

- **EndpointUpper**, `Accounting/EndpointUpper.lean`:
  `GridGraphs.maxPreserved_residueTwo_le_endpoint_refinement` proves
  `P(3k+2)<=T+floor(2k/3)` for ALL k>=5, with no b/c/r or coverage premises.
  `GridGraphs.forced_card_le_endpoint_refinement` applies to every feasible F.
  All three old k%3=1 endpoint profiles are excluded, as detailed below.
  This is not the full sharp T theorem or an attainability claim.
- **Previous BoundaryFiveUpper**, `Accounting/BoundaryFive/Upper.lean`:
  `GridGraphs.BoundaryFive.maxPreserved_residueTwo_le` proves the previous
  global upper formula `P(3k+2) <= T+floor((2k+1)/3)` for every
  `k>=5`. The corresponding `forced_card_le_residueTwo_bound` applies to
  every feasible `F`. At `k=2 mod 3`, the former endpoint forces
  `(r,c,b)=(k+4,1,5)`; symmetry positions the unique gap, and a forced
  nonpure singleton contradicts endpoint capacity. This is not an assumed
  canonical frame or a generic strict-cap theorem. In particular `P(17)<=113`,
  not the stale `114` endpoint.
- **FourCarrierClosure**, `Accounting/CarrierLayers/FourCarrier/Closure.lean`:
  `GridGraphs.CarrierLayers.FourCarrier.card_le_target_of_four_pure_missing_side`
  proves `f<=T` for **all** `p=4` missing-side sets, `k>=5`.
  The image budget handles `k>=6`; at `k=5`, shallow preimages force a
  second-position root, deep equality fills its axis, and a boundary six-cycle
  contradicts feasibility. `missing_side_counterexample_pure_eq_three`
  historically left only `p=3`; those counterexample premises are now impossible.
- **ThreeCarrierClosure**, `Accounting/CarrierLayers/ThreeCarrier/Closure.lean`:
  `GridGraphs.CarrierLayers.ThreeCarrier.card_le_target_of_missing_side` proves
  **f<=T for the ENTIRE missing-side branch, k>=5, with no p or off-side
  cost W assumption**. W2/W3/W4, mixed/top cases, and k=5 equality are closed.
- **Annulus and all-covered budgets**, `CarrierLayers/Annulus/` and
  `AllCoveredCounterexamples.lean`: global `B+E<=4n-9` for n>=9,
  physical full-rod/deficit bounds, and **all four sides covered, p>=4,
  r>=k+4, d=r-p-h>=k** for every stable counterexample f>=T+1.
  `GridGraphs.CarrierLayers.stable_excess_budget` proves
  **b+c+3e<=2k+8 for ALL e>=1 and f>=T+e**, without a coverage premise.

The old missing-side one-excess reductions remain valid with impossible
premises. **No missing-side proof work remains. Only the all-covered sharp
upper branch is open.** The global formula is now `T+floor(2k/3)`.
The earlier b>=7 estimate from `Annulus.card_le_of_boundaryDeficiency_ge_seven`
now holds globally, including P(23)<=200 and P(32)<=376. The old k%3=1
profiles `(r,c,b)=(k+5,1,5), (k+4,2,5), (k+4,1,6)` are all excluded.
The remaining task is **f=T+e, 1<=e<=floor(2k/3)**, not those three profiles.
No general exclusion or existence claim for the remaining excess levels follows.

The checked lower bound remains

```text
L(k)=3k^2+6k+3+floor((k-1)/2) <= P(3k+2),  k>=3;
L(k)=T-floor(k/2)+2,                       k>=5.
```

Thus `110<=P(17)<=113`, not an exact value. The terminal repair gains once
at odd `k`; its six-width gain is `12k+25`, not the target `12k+26`.
An arbitrary-width target-count lower family is still missing. Current bounds:

| Side | Formal lower | Global upper |
|---:|---:|---:|
| 17 | 110 | 113 |
| 20 | 149 | 154 |
| 23 | 195 | 200 |
| 26 | 246 | 253 |
| 29 | 304 | 312 |
| 32 | 367 | 376 |

The current upper at side 35 is 447.

The main full strict build passed **9,049 jobs, zero warnings/errors, exit 0**
on Lean/mathlib 4.33.1. Inventory: **342 modules / 100,477 lines**, plus the
**188-line root: 343 files / 100,665 lines total**. The **40 new modules /
5,850 lines** range from **31 to 521 lines**, all below 1,000; the 11 old
oversized modules are untouched. All 40 are root-reachable: the verifier added
the otherwise unused valid `BoundarySix.Connected.RingEndpoint` root import
before the snapshot; EndpointUpper was already imported. The full command also
covers the original five outside the root. RingEndpoint's old implications
have impossible endpoint premises, not an open branch.

Audits reran all **441** previous declarations and checked **202 new/changed
exports** (200 from new modules plus both existing Symmetry exports). One old
Symmetry theorem, `exists_top_gap_pullback`, overlaps, so **441+202-1=642 unique
public declarations**, comprising **584 theorems + 50 definitions + 3
abbreviations + 5 structures**, not 642 theorems. Dependencies are subsets of
`{propext, Classical.choice, Quot.sound}`, possibly empty, with no `sorryAx`
or native proof axiom in coverage. This is
**not a whole-library axiom audit**: six legacy `native_decide` uses in three
separately built counterexample tests remain outside coverage. Generated
constructors/projections/recursors are not extra named source entries; private
helpers are checked transitively where used.

Exact logs recorded by Lean EVIDENCE:

- `/tmp/opencode/endpoint-upper-final-full-build.log`
- `/tmp/opencode/endpoint-upper-final-TotalCurrentAudit.log`
- `/tmp/opencode/endpoint-upper-final-AnnulusThreeCarrierAudit.log`
- `/tmp/opencode/endpoint-upper-final-endpoint-upper-final-Audit.log`
- `/tmp/opencode/endpoint-upper-final-inventory.log`
- `/tmp/opencode/endpoint-upper-final-post-audit-check.log`
- `/tmp/opencode/endpoint-upper-final-verification-summary.log`

The new driver is `/tmp/opencode/endpoint-upper-final-Audit.lean`; the old
`TotalCurrentAudit.lean` and `AnnulusThreeCarrierAudit.lean` were both rerun.
All three import only `GridGraphs`. The reported targeted build passed 8,882
jobs, separate from the full count. Source/root/configuration fingerprints,
including all tests, stayed unchanged through verification. All **300 old
non-Regression/Symmetry modules** match the prior Annulus/ThreeCarrier snapshot;
Symmetry intentionally adds its isometry export while retaining the old theorem
statement. This is not a whole-workspace or mathlib hash. Regression checked the
uniform interval, P(23)<=200, P(32)<=376, and unchanged older specializations.
No build is active. See the handoff and Lean STATUS/EVIDENCE/README for commands
and coverage. These are recorded results, not reruns for this docs-only update.
No Python files changed and no Python or optimization searches ran. Earlier
bounded capacity experiments used coordinates at most 13; the historical
23 Python tests were not rerun.

## Endpoint Resolution

The following proofs exclude the OLD k%3=1 score `T+floor((2k+1)/3)`.

1. **Connected boundary five, `(r,c,b)=(k+5,1,5)`.**
   `BoundaryFive/CornerPacket/Upper.lean` combines two actual short carriers
   with annulus losses. The square-isometry profile transport preserves r/c/b
   and positions only the gap; it does not canonicalize the other corner holes.
   The stronger checked `CornerPacket.connected_boundary_five_components_ge`
   gives r>=k+6 for b=5,c=1,k>=7 without a score or residue premise. It does
   not rule out every b=5,c=1 feasible set.
2. **Two-component boundary five, `(k+4,2,5)`.**
   `Rootless/AmbientEndpoint.lean` derives the actual ambient-to-rooted-deep
   bridge, not merely a conditional smaller-grid certificate. The gap singleton
   obstruction forces z=(2,2) into U and w=(1,2) is an ambient isolate.
   Ambient and annulus budgets prove deep rooting, unique boundary roots, and
   four deep corners in U. The exact ledger gives q=k. Four distinct corner-root
   carriers force all rods long; nonreused missing triples contradict total
   deficit. Reciprocal and cyclic endpoint orientations are fully handled.
3. **Connected boundary six, `(k+4,1,6)`.**
   `BoundarySix/Connected/Upper.lean` closes E=1 and E=0 with an outer corner
   in U using the connected-annulus deep bridge and the same rooted endpoint
   obstruction. In E=0 with all outer corners in F, two distinct actual gaps
   force two deep corners in F. If neither is a singleton, two literal five-edge
   packets violate the physical perimeter forest edge count. The resulting
   singleton plus summed annulus deficits contradicts endpoint capacity. The
   proof does not assume the two corners belong to distinct carriers.

`Rootless.strict_carrier_cap` proves the strict m-1 cap under
`UniqueBoundaryRoots` on the smaller actual grid (m>=2). The ambient bridge proves these hypotheses at the
endpoint, not for generic ambient b=5 sets. There is no generic ambient n-5
carrier cap or `f<=(n-5)r+11` theorem claimed. Endpoint reciprocal/cyclic
packing closure is not closure for all rooted forests. The b=6,E=1 position-3
residual is closed at the old endpoint: the earlier position-2-only conjecture
was wrong, and the code handles the third position without a false near-only
classification. Earlier two-profile and RingEndpoint reductions remain valid
with impossible old-endpoint premises.

## Missing-Side Resolution

The unchanged missing-side proof does **not** finish the old deep-only strip
argument by adding more missing-side loops or a separate top-row equality classification.

**W2, enlarged nonpure strip.** `ThreeCarrier/CostTwoRectangle.lean` identifies
the actual nonpure vertices in a rectangle including the missing-side roots,
root spokes, and next ring as well as the deep vertices. Its row indexing runs
from 1 through 3k, with 3k-1 vertical steps. Former top deep-row rods are now
interior rows, including the old length-4/7 cases. Actual horizontal edge rows
inject into at most three horizontal nonpure carriers; no rod list or spacing
between their rows is assumed. `CostTwoMixedBound.lean` uses mixed interior-row
shadows and `MixedPacking.rectangular_three_rod_edge_bound`, a height-independent
joint three-rod inequality. Nearby rows are handled together, not by adding
overlapping per-rod losses. The result is

```text
V+H <= (k-1)(3k-1).
```

`NonpureForest.lean` counts actual nonpure vertices and FF edges. Combined
with the pure mass and counterexample component budget, `CostTwoClosure.lean`
obtains `f<=10k+4+(k-1)(3k-1)=T-k+5<=T`, including k=5. No top-position,
mixed-row, or equality exception remains. The auxiliary W2 capacity results
also prove the root-shadow and shallow-slack inequalities; the final proof
does not rely on the old sufficient deep-only certificate succeeding.

**W3, two joint defects.** `CostThreeRectangle.lean` leaves the extra off-side
hole unclassified. `CostThreeDefect.lean` maps bad vertical edges and bottom
horizontal edges jointly to the **two incident boundary edges at that same
physical hole**. Their combined defect is **<=2, not <=1**. It is not two
independent allowances for the two edge families. After separating these
defects, the same mixed packing gives

```text
V+H <= (k-1)(3k-1)+2,
f <= 10k+4+(k-1)(3k-1) = T-k+5 <= T,     k>=5.
```

The W3 pure mass/component allowance pays for the extra two edges.
The eight-case extra-hole adjacency classification is **unused, unformalized,
and unnecessary**. No one-edge defect premise, canonical extra-hole location,
or new k=5 equality contradiction is needed.

**W4 and unrestricted closure.** Global d>=k from `Annulus/Counterexamples.lean`
and the connected shallow-carrier argument close W4 in `CostThreeReduction.lean`.
Connectedness is derived in that profile, not assumed globally.
`ThreeCarrier/Closure.lean` then combines W2/W3/W4 with the previously closed
FourCarrier branch to prove f<=T for any missing side, with no p/W assumptions.

## Historical W2 Geometry (Closed)

**HISTORICAL, CLOSED:** the following records the earlier paper approach, not
the final proof or a live task list. Its deep-only sufficient certificates and
equality analysis are not asserted to have been formalized verbatim. W2 denotes
the off-side weighted cost-two subcase of the former `p=3`, `f=T+1` program.
Orient the missing
side as the top. The paper geometry gives all corners in `F`, only two
off-side holes (the far-side near-corner holes), a frame on the other three
sides consisting of three pure carriers, and no off-side next-ring `F`.
The later ThreeCarrier geometry derives its own inputs; none should be
silently imported as a consequence of FourCarrierClosure alone.

Let `q` count roots on the missing side, `h` count actual shallow nonpure
carriers (no deep vertices), and `d` count actual deep carriers. Use
`gamma=c-1`, reserving `d` for deep carriers rather than the handoff's
component slack. The historical paper derivation was

```text
q=k-m,   z=r-q-3,   gamma=c-1,
z+gamma=3,   m>=1,   z>=m,   h<=z-m,
d=r-3-h=k-m+z-h.
```

In particular `1<=m<=3`. The final chain proves its own exact profile and
`cost_two_shallow_slack` in `CostTwoCapacity.lean` proves h+m<=z with actual W2
premises. Do not replace that proof with a saturation-only isolate argument
or charge shared inward witnesses as distinct carriers.

## Historical Mixed/Top Accounting (Closed)

**Historical deep-only argument, not the final enlarged-strip proof.** Index deep rows by
`1,...,N`, where `N=n-4=3k-2`. Let `Z` count deep preserved vertices,
`V` vertical deep FF edges, and `H` horizontal deep FF edges. Here `H` is
an edge count, not the forced graph. With the paper identification of the
deep induced components with the `d` deep carriers, the forest identity is

```text
Z=d+V+H.
```

At the step between rows `t,t+1`, `1<=t<=N-1`, eligible vertical-edge
columns are `A=[3,3k-2]`, an interval of length `3(k-1)-1`. The paper
spacing obstruction gives separation at least three, hence, with `Q=k-1`,

```text
v_t<=Q,   Delta=sum_t(Q-v_t),
Z=Q(N-1)+d+H-Delta.
```

The historical task was to pay for horizontal edges by **actual vertical-edge
deficit**, not by adding incompatible carrier or hole budgets.

A horizontal deep rod occupying columns `[a,b]`, of length `L=b-a+1>=2`
in row `y`, excludes vertical-edge columns in the expanded interval
`[a-1,b+1]`, clipped to `A`, on the valid steps in
`{y-2,y-1,y,y+1}`. Each affected step loses at least
`ceil((L-1)/3)` of the baseline capacity `Q` in this paper argument.

If there are at most three horizontal rods, all in rows `2,...,N-1`,
and their rows are pairwise separated by at least three, assign each rod
three disjoint affected steps. Use `[y-2,y]` by default; if the first row
is `2`, shift its initial chain of rows spaced exactly three apart one
step forward. Since `N>=13`, at most three such rods fit before the upper
step limit. Consequently

```text
Delta >= sum_rods 3 ceil((L-1)/3) >= sum_rods (L-1) = H,
Z <= Q(N-1)+d = (k-1)(3k-3)+k-m+z-h.
```

This recovers the all-vertical **numerical bound** for the stated mixed
configuration, not automatic `k=5` equality closure. If `Delta=H`, every
rod must satisfy `L=1 mod 3`; equality also requires all other capacity
inequalities to be tight. This old approach left a rigidity contradiction;
the enlarged-strip proof above closes the branch without it.

Top deep-row (`y=1`) rods have fewer affected steps. They avoid the root
three-column blocks, giving the paper bound `L<=3m-2`: respectively
`1,4,7` for `m=1,2,3`. Thus a nontrivial top-row rod is impossible for
`m=1`; lengths `4` and `7` were top-row equality exceptions not covered by
the old three-step assignment. They are now interior cases of the enlarged
strip bound, not remaining proof obligations.

## Overlap And Guardrails

For distinct rods the paper bounds on expanded-column-shadow overlap are:
at most one column in the same row, at most one in adjacent rows, and at
most three at row distance two. These bounds do not license independent
addition of their losses.

The joint-capacity certificate uses, for each step `t`, the **physical union**
`S_t` of all expanded shadows affecting it, clipped to `A`. If the surviving
intervals in `A\S_t` have lengths `ell_i`, set

```text
kappa_t = sum_i ceil(ell_i/3),
v_t <= kappa_t <= Q.
```

Indeed an excluded interval separates successive surviving intervals by
at least three columns, so their independent spacing capacities are
compatible with the baseline spacing bound. The sufficient certificate
`H<=sum_t(Q-kappa_t)` implies `Delta>=H` and the numerical bound above.
**This historical certificate is not asserted to always succeed.** Nearby
clusters were its bottleneck, now bypassed by the formal joint interior-row
packing on the enlarged strip. A failed sufficient certificate is not a
feasible counterexample, and no missing-side gap follows from its failure.

Root-tail losses use the **maximum** of incident barrier weights for a
given tail, not their sum. Do not add a root-tail loss to edge deficit when
both count the same holes. Any combined certificate needs an explicit
disjoint-resource partition or a single joint capacity calculation.

The proposed local three-column-strip `L/2` occupancy bound is **false**:
a vertical left spine of length `L` with separated right singleton teeth
has `L+ceil(L/3)` preserved vertices, while its forced graph is a tree
(the intervening vertices attach the teeth). Thus forced acyclicity alone
does not imply that local strip bound; it cannot be used to pay for rods.

## All-Covered Program

This is the **only remaining sharp upper branch**, now restricted to
`f=T+e, 1<=e<=floor(2k/3)`. All positive-excess
counterexamples are all-covered, with p>=4, r>=k+4, d>=k and
b+c+3e<=2k+8. Use actual pure-carrier mass P (not the maximum P(n)),
nonpure contacts, annulus occupancy, and actual deep capacity. Reserve M here
for the number of full deep rods. Keep shared physical shadows as unions.

For the full two-layer annulus A, selected set S, annulus induced/ambient
components rA/cA, and selected inner/outer corner counts i/o, `Annulus/Cap.lean`
proves the exact cubic ledger and its global consequences:

```text
2|S|+rA+cA+i = |A|+o,
B+E <= 4n-9,    K=4n-4-B-E >= 5,    rA+cA+4 <= 2K,    n>=9.
```

`Annulus/Bridges.lean` restricts the actual forced forest to the annulus and
M full deep rods. Disjoint literal longitudinal packets add n-3 edges for
each n-4 deep vertices, giving **M+1<=cA**, including annulus isolates.
Additional lateral attachments are allowed; no quotient/contact forest is
assumed. `Annulus/Deficit.lean` gives d<=M+D and p+h<=rA, hence

```text
D=(n-4)d-|F_deep|,    r+5 <= 2K+D.
```

This is total deep deficit, not the older pure-mass shortfall named D.
The active task is to strengthen this physical inequality in all-covered
lower-excess configurations, not reopen missing-side cases or any of the three
excluded old k%3=1 endpoints. The global endpoint refinement still allows
positive excess, including at b>=7; it does not prove sharp T.

Seek quantitative general corner-packet, long-rod, and frame-budget losses.
Endpoint arguments used saturation and actual rooted-deep bridges; those
premises must be derived anew or replaced when slack is available. Any general
packing bound must retain actual components, annulus isolates, and nonreuse.
No proposed route is asserted sufficient to reach sharpness.

For the following old weak shadow certificate, S denotes the boundary shadow
union, not the annulus selected set:
`|S|+2p+b+2c>=6k+19` is not a route to the unresolved low-budget `p=4`
case: since `|S|<=b`, it forces `b+c>=3k+6`, already inside the old
sufficient branch `b+c>=2k+8`. Repackaging it is not new progress.
Seek a strictly stronger joint boundary/contact/deep-deficit inequality,
with explicit handling of shared witnesses and corner exceptions.

The actual two-short corner packets and endpoint rooting/packing proofs are
checked, not future targets. Generic ambient `b=5` strict cap `n-5` and
`f<=(n-5)r+11` are not checked consequences of the conditional smaller-grid
cap. Broader quantitative arguments require their own geometry, real inward
spokes, and nonreuse, not assumed canonical normalization or generic rooting.

## Roles And Next Targets

Review each new all-covered paper argument before formalizing it. Keep its
actual premises, rather than assuming the desired unconditional corollary.
The historical missing-side roles are closed, not waiting for another loop.

1. **Upper, all-covered lower excess:** organize `1<=e<=floor(2k/3)` by
   actual boundary/component slack, then strengthen r+5<=2K+D using mass,
   contacts, full-rod packets, and deep deficits. Retain annulus isolates
   and shared-resource unions. Do not assume a quotient forest or reuse the
   dominated shadow budget as new progress.
2. **Upper, quantitative geometry:** extend corner-packet, long-rod, and
   frame-budget losses beyond endpoint saturation, deriving any rooting
   premises from the actual ambient set. The old three profiles and their
   reciprocal/cyclic and position-3 residuals are closed, not next goals.
   Avoid generic ambient cap claims, weak-certificate repackaging, and promises
   that this research route must reach sharp T.
3. **Lower, accumulating repair:** retain the checked `L(k)` family as the
   baseline; seek a repeatable `k -> k+2` construction gaining `12k+26`,
   compatible with both seed branches. Track deletions, boundary deficiency,
   and the actual incoming/outgoing component partition; rootless components
   are allowed. Neither the one-time terminal repair nor a matching seed
   budget proves a pump.

Paper review should check every geometric premise, clipped endpoint, resource
overlap, and equality case before a Lean target is assigned. Completion still
requires all-covered sharp upper control and a target-count lower family;
the entire missing-side proof is complete, but no full sharp formula is claimed.
