# Astra Roadmap: Exact Square-Grid Optimum

Updated: 2026-11-24.

## Active Checkpoint

**Lean:** `GridGraphs.PitchCut.pitch_upper_verified` checks the physical
residue-one upper bound on either kind of pitch line for every `k≥5`,
including boundary lines. The [physical trace and bill proof](UNIFORM_PITCH_CAP_PRICE.md#lean-replay-and-the-physical-cut)
uses no cap witnesses in the theorem statement. With the checked comb,
`exact_of_no_pitch_verified` leaves the no-pitch maximizer bound as
the remaining stable residue-one formalization obligation.

**Exact for all positive square sizes:** the [square formula and
certificate replay](EXACT_SQUARE_FORMULA.md) combine the uniform pitch
induction, a transported exact no-pitch dual and the physical comb.
The following branch and interval records describe earlier stages.

**All residue-one widths, pitch class:** a [stationary slit-language
certificate](UNIFORM_PITCH_CAP_PRICE.md) now gives the comb upper for
every `k≥5` in the presence of a pitch line. The induction closes at
25 triples (24 with vertex arrows), independent of cap height.

**Side 103 is exact: `P(103,103)=3646`.** The
[arbitrary-height directed-slit cap proof](FINITE_CAP_SLIT_PRICE_103.md)
excludes score 3647 at any pitch cut. The [free-count face/line
dual](FREE_FACE_LEDGER_103.md) excludes it without a pitch cut, and
the comb physically attains 3646. These certificates supersede the
earlier branch restrictions below; the cap proof is at fixed width.

**Residue two:** the [odd-fan speed proof](ODD_FAN_SPEED.md) closes
the final exceptional tail. The table of [fourteen progressions](RESIDUE_TWO_CLASSIFICATION.md)
now has matching constructions and unrestricted bounds in every cell.
Residue one was the last obstruction to an eventual square formula.

At side 103, the [segment/face certificate](SEGMENT_FACE_EXCLUSION.md)
excludes every no-pitch 3647 candidate with exactly 43 off-skeleton
marks. The [line/face word certificates](RANK44_FACE_PRICE.md) also
exclude exactly 44. Their [three-component extension](RANK45_FACE_PRICE.md)
excludes exactly 45, and the [four-component extension](RANK46_FACE_PRICE.md)
excludes exactly 46 and the whole zero-slack boundary. Any remaining
no-pitch candidate now has slack at least two by the
[one-slack certificate](RANK47_FACE_PRICE.md) and at least 49 off-skeleton
marks by the [weighted row certificate](RANK48_FACE_PRICE.md). The
[F=49 certificates and slack transport](RANK49_FACE_PRICE.md) strengthen
these necessary conditions to at least 51 off-skeleton marks and slack at least six. The
historical interval at that stage was 3646–3647.

**Residue one:** [unrestricted cheap separators](RESIDUE_ONE_CHEAP_SEPARATORS.md)
give many cuts with at most five intervals in each direction.
Crossing these cuts forces a [physical pitch frame](RESIDUE_ONE_PITCH_FRAME.md)
of linear dimensions with an exact interior mark bound.
The [joint aligned frame price](JOINT_ALIGNED_FRAME.md) handles both
three-column side wings and the two caps with their shared contacts.
The [unrestricted boundary interface debit](BOUNDARY_INTERFACE_DEBIT.md)
charges aligned-strip defects at every length and propagates boundary
omissions through depth. A [crossing cut exchange](INTERIOR_PHASE_LENGTH_EXCHANGE.md)
prices mixed orientations by comparison to the solved residue-two family.
The [sparse component exchange](SPARSE_COMPONENT_EXCHANGE.md) restores
separated side holes without loss, using the actual interior component
rank, and gives a constant loss bound for nonconsecutive holes.
The [end-band rank exchange](END_BAND_RANK.md) prices correction of
arbitrary end words against the actual joint exterior partition.
The [four-layer collar cap and crop reduction](COLLAR_PEEL.md) bound
arbitrary four-layer markings by `8n-40` and transfer to a smaller
residue-one square with a quantified saving.
The [crop/end coupling](CROP_END_COUPLING.md) measures which leftover
donors can pay for an end repair and gives a bounded-gap family that
defeats both fixed-depth tests.
The [blocked-rim exchange](BLOCKED_RIM_EXCHANGE.md) pays that family's
crop excess by releasing the interior blockers. Its port-rank bound
uses the discarded collar without assuming the smaller square's wiring.
The [arbitrary six-layer comparison](ARBITRARY_SIX_COLLAR.md) gives
a `16n-170` ten-layer cap and bounds net crop cost with free refill
words. Mixed collars defeat even optimal four-layer restoration.
The [retained-core envelope](RETAINED_CORE_ENVELOPE.md) transfers
actual boundary components to the two solved residues. An
arbitrary-length interface inequality excludes the extensive mixed
regime even without observing any deeper core marks.
The [dense collar price](DENSE_COLLAR_PRICE.md) couples a closed
four-layer sweep to the core component ledger; a rank bound on eight
seams gives a comb-increment reduction by 18 for dense pitch-ended arms.
The [movable-cut sweep](MOVABLE_DENSE_CUT.md) removes the pitch
requirement altogether when depth-nine holes are three apart on
each straight arm. Its no-pitch case uses equality on the same square
viewed from several different cuts.
The complementary [nine-deep bar-and-teeth frame](NINE_DEEP_FRAME.md)
has a direct all-length comb upper. An [unrestricted radial component
ledger](RADIAL_COMPONENT_LEDGER.md) keeps the actual boundary join
budget when iterating through arbitrarily many nested squares.
[Multiscale cap cuts](MULTISCALE_CAP_CUTS.md) split the outer collars
into straight-profile rectangles with total artificial side length `o(n)`.
The [wired pitch cap theorem](WIRED_ENDPOINT_PRICE.md) proves the sharp
`1/10` per-column bonus at arbitrary height and the partial-wiring price
`3/4` per independent terminal join.
A [spanning pitch separator](WIRED_PITCH_SEPARATOR.md) wired on one
side now gives a uniform two-mark error, or the comb upper if its
two ends have at least three vacancy runs in total.
[Shifted-profile prices](SHIFTED_PROFILE_SEAM.md) handle exact opposing
phases and a single moving slip; the [rim tariff](RESIDUE_ONE_RIM_TARIFF.md)
limits a canonical maximizer on the `103+9t` upper branch to at most
six missing perimeter edges. [Column colors and corner charges](PITCH_RUN_COLOR.md)
exclude all combinations of the recurrent nine-layer arm modes at 103;
changes of mode within a straight arm remain open.

**Side 581:** **P(581,581)=113,071**. The [ledger](../analysis/research_program/exceptional_287_ledger.py)
replays five one-gap certificates covering all 191 isolate distances on each axis
and verifies a physical spanning tree with 337,560 edges. Replay with
`PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.exceptional_287_ledger --581 --drat`.

**Side 539:** the [proof ledger](../analysis/research_program/exceptional_287_ledger.py)
gives **P(539,539)=97,351**. Run `PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.exceptional_287_ledger --539 --drat`
to verify the five one-gap exclusions and replay the spanning tree.

**Side 497:** [the one-gap certificates and tree replay](EXCEPTIONAL_497.md)
give **P(497,497)=82,807**.

**Side 455:** [the one-gap certificates and tree replay](EXCEPTIONAL_455.md)
give **P(455,455)=69,439**.

**Side 413:** [the enlarged core and rooted-tile proofs](EXCEPTIONAL_413.md)
give **P(413,413)=57,247**.
The [413 core transfer](CORE_413_UNIFORM.md) handles row insertions
and excludes north exits within 305 of either end for all larger sides.
At 581 the two required corner distances would sum to at least 616,
but the side spans only 580 edges.

**Side 371:** [the shared-edge full-board and rooted-tile proofs](EXCEPTIONAL_371.md)
give **P(371,371)=46,231**.

**Side 329:** [the ordinary-bridge and rooted-tile exclusions](EXCEPTIONAL_329.md)
give **P(329,329)=36,391**.
The [exit-window transfer](TWO_GAP_EXIT_TRANSFER.md) excludes the
tangential deep axis and both 104-site end ranges for `0011` uniformly.
At 371 only 53 normal-axis exit columns remain in that case.

**Side 287 and the exceptional tail:** [the equality-case audit](EXCEPTIONAL_287.md)
proves **P(287,287)=27,727**. Throughout the open tail a two-gap
witness, if it exists, may be put in the single frame `0011` and the
inter-arc bridge must attach at ordinary teeth.

**Side 245:** the [bulk-axis theorem](BULK_AXIS.md)
gives one common direction for all deep marked-center adjacencies,
and a checked full-board proof eliminates every two-gap case at 245.
The [frame-exchange lemma](ONE_GAP_FRAME_EXCHANGE.md) reduces the
remaining existence test to a single perimeter. The [rooted-tile
certificates](TILE_CASES_245.md) exhaust all 32 remaining distances
and both axes. **P(245,245)=20,239.**

**`P(161,161)=8791`.** Both gap counts have checked full-board
exclusions. A [seven-layer L certificate](ODD_SINGLE_DEFECT.md#seven-layers-exclude-the-one-gap-patch-case-on-the-whole-open-tail)
now excludes the entire one-gap patch case on every remaining tail
side, including defects outside the L. A one-gap target must instead
spend its charge on a north- or west-side depth-two star.

**Two-gap meeting test:** [the two arms can meet through the center](ODD_SINGLE_DEFECT.md#the-two-arms-can-meet-in-a-zero-charge-neighborhood-through-the-center)
with locally zero interior charges and correct edge directions for
all four corner roots in every remaining frame. A 21-column transfer
on each half-corridor gives this result uniformly on `119+42s`;
extension to the untested quadrants remains open.

**Two-gap interior connector:** [checked common-path tests](ODD_SINGLE_DEFECT.md#depth-of-the-connector-and-the-full-board-test-at-203)
force the connector beyond the width-eight annulus on every open tail
size. At side 203, a separate full-board proof excludes all ten remaining
two-gap classes with no depth restriction. Only a one-gap witness could
raise the rail score from 13927 to 13928.

**Uniform two-gap progress:** the [joined annulus transfer](ODD_SINGLE_DEFECT.md#joining-the-strips-eliminates-five-two-gap-classes-on-the-whole-tail)
excludes five of the fifteen two-gap frame classes at every
`119+42s`. The ten surviving classes are rim-feasible, not whole-grid
witnesses.

**Side 119 is exact:** `P(119,119)=4831`. [Checked full-board
exclusions](ODD_SINGLE_DEFECT.md#full-board-decision-test-for-the-remaining-eight-one-gap-frames-at-119)
cover both perimeter gap counts at 4832. The new 42-column strip
test restricts exit phases uniformly but does not exclude two-gap
frames on the whole tail.

**Residue one, diagonal sectors:** [a rational upper valid for every
`k>=14`](DIAGONAL_SECTOR_UPPER.md) gives
`P(3k+1,3k+1) <= 3k²+5k+floor(k/3)-1`. This changes the linear
coefficient and narrows the asymptotic gap to `k/30+O(1)`. The deeper
chart gives `floor(3k²+16k/3−7/6)` for `k>=18`, hence
**4077–4078** at side 109. New exact scores are 1066 at 55,
1182 at 58 (checked UNSAT above), and 1433 at 64.

**Residue two, open odd tail:** [exact charge-profile exclusions and a
parity test](ODD_SINGLE_DEFECT.md) show that every `35+42t` forest
attaining the upper floor must have one 72-unit defect, with all other
physical stencil charges zero. Existence on this tail is still open
beyond the finite exclusions at 35 and 77.

**Residue one:** [uniform nine-row pricing](CAP_PERIOD_UPPER_BARRIER.md#uniform-nine-row-upper-for-residue-one)
proves `P(3k+1,3k+1) <= 3k²+6k−9` for every `k>=36`.
At side 109 the [joint fifteen-row dual excludes 4092](CAP_PERIOD_UPPER_BARRIER.md#fifteen-rows-exclude-4092);
the whole-grid interval is **4077–4091**.

**Side 109, fourteen rows:** [the exact joint-strip dual excludes 4093](CAP_PERIOD_UPPER_BARRIER.md#fourteen-rows-fixed-point-test-and-pricing).
The whole-grid interval is now 4077–4092.

**Side 109, thirteen rows:** [an exact dual excludes 4094 even after redistribution](CAP_PERIOD_UPPER_BARRIER.md#thirteen-rows-the-fixed-support-dies-inside-the-left-boundary).
The verified whole-grid interval is 4077–4093.

**Side 109, twelve rows:** [redistribution preserves the fractional score `12283/3`](CAP_PERIOD_UPPER_BARRIER.md#twelve-rows-preserve-the-score-but-not-the-eleven-row-point).
The integer upper remains 4094.

**Side 109:** [eleven joint rows exclude 4095](CAP_PERIOD_UPPER_BARRIER.md#eleven-rows-the-first-vertical-bulk-patch).
The whole-grid interval is 4077–4094.

[Residue-two classification](RESIDUE_TWO_CLASSIFICATION.md): thirteen
sharp tails grouped by construction and by the two phases `k mod 7`
and `k mod 2`. The side-119 unrestricted matching run reached its
2 GiB proof limit without a checked exclusion; the interval remains
4831–4832.

**Residue-two target refuted for the tail (computer-assisted, not Lean):**
[period-three overlap dual](UNRESTRICTED_PERIOD_THREE_UPPER.md) gives the
unrestricted bound `P(3k+2) <= T(k)+floor((23-2k)/14)` for `k>=6`.
In particular no family can attain the old target `T=3k²+7k` for
`k>=12`. The physical verifier replays the rational stencil on all 3,549
local atom/type orbits; boundary counts give an exact polynomial in k.
The older checkpoints below predate this result. The exact tail optimum
and a matching replacement lower family are not determined.

**2026-09-15 autonomous batch003 completed:**
[Batch report](research_batches/BATCH_003.md) and
[reviews](research_batches/BATCH_003_REVIEWS.md) record reviewed
[bilateral payment](PAPER_BILATERAL_FRONT_PAYMENT.md) without common
roots when each actual bank level has a carrier spanning[3,A-3]. The
2,424-state/22,508-edge certificate combines with existing payments as
`sum D <= R_used+6N_e+11N_m+16N_b`, with R_used<=R_av. The uncovered
debt still has only R_av-R_used available. This is not width-only coverage.
[Nested renewal](PAPER_NESTED_RENEWAL_OBSTRUCTION.md) proves the forced
crop deficit2k-1 and excludes literal or bounded-cardinality-edit constant-
gap nesting for the current cores. A25->75 gap-one step is verified, but
its delete-only template cannot continue from any eligible75 n14 seed.
Global and Lean bounds are unchanged. Batch003 is paused; batch004 has
not begun.

**2026-09-14 autonomous batch002 completed:**
[Batch report](research_batches/BATCH_002.md) and
[reviews](research_batches/BATCH_002_REVIEWS.md) record the reviewed
[rooted mixed-front payment](PAPER_MIXED_FRONT_PAYMENT.md). A104-state/
300-edge certificate pays arbitrary endpoint mixtures using actual
singletons and protected whole supplier-bank units; simultaneous
allocation is `sum D <= R_av+6N_exposed+11N_mixed`. The first restricted
invoice was refuted by an actual periodic family, not hidden by a revised
definition. Common-root localization and global coverage remain open.
[Renewal tests](PAPER_RENEWAL_ANNULUS_TEST.md) give the restricted solver
result M_3(4)=75 (no independently checked UNSAT trace) and prove guarded
pendant conversion cannot itself remove cap cycle rank. Global and Lean
bounds are unchanged. Batch002 is paused; batch003 has not started.

**2026-09-14 autonomous batch001 completed:**
[Program charter](RESEARCH_PROGRAM.md), [batch report](research_batches/BATCH_001.md),
and [independent reviews](research_batches/BATCH_001_REVIEWS.md) record the
new reviewed [stopped-front payment](PAPER_STOPPED_FRONT_PAYMENT.md).
Whole banks stopped at depth three are paid at zero additive error from
original isolates and side-labelled boundary holes, WITHOUT a boundary
spine or common roots. Their invoices do not reuse each other or existing
exposed-bank coupons, yielding `sum D <= R_av+6N_exposed` for the selected
disjoint wide-bank classes. Mixed/variable-depth coverage is still open;
the unconditional global and Lean bounds below are unchanged. Both
implementations completely checked1,703,936 bounded masks. Batch001 is
paused at its three-cycle checkpoint; batch002 has not begun.

**Rust experiment and 17-square evidence:**
[RUST_CERTIFICATE_CORPUS.md](RUST_CERTIFICATE_CORPUS.md) records the new bounded
Rust sampler, independent primal checker, and finite inequality checker.
The historical mirrored and unmirrored exhaustive records claim P(17)=110;
the Lean interval [110,113] is a separate verification level. The unmirrored
source still matches its recorded hash, and the 110 witness passes independent
primal replay. This audit found no correctness bug but did not reproduce the
large historical negative computation or its missing early checkpoint.

**Current paper continuation:**
[clean metric research](PAPER_CLEAN_METRIC_CLOSURE.md) pays all narrow banks
and reduces every hypothetical K=r+b+c<n configuration to at most thirteen
wide banks. Exposed banks have a reviewed simultaneous boundary payment;
an explicit full-height moving-seam skeleton has f<=T+10, including arbitrary
feasible additions. Neither theorem covers arbitrary partial bank terminals.
[Clean allocation](PAPER_CLEAN_ALLOCATION.md) removes all duplicate rectangle
capacity and preserves exact fragment refunds, but the remaining weighted
terminal demand is not paid. A bounded front count or unweighted front length
does not imply a constant excess.

[Maximum-specific research](PAPER_MAXIMUM_CLEAN_UPPER.md) proves a precise
translation alternative, not a boundary-exposure normalization.
[Terminal transport](PAPER_TERMINAL_TRANSPORT.md) retains the longitudinal
cost even on an actual connected carrier. These four complete notes received
independent paper review. The unconditional bound remains unchanged; no Lean
work or optimization ran in this continuation, and explicit grid checks
stayed within side 14.

**Latest paper continuation:** [isolate routing](PAPER_ISOLATE_ROUTING_UPPER.md)
now pays arbitrary isolate-induced routing relative to its conservative
clean certificate, with no O(z) error. It proves T+6 when all clean through
strands have at least five pairs, regardless of isolate count. The remaining
global obligation is clean short-strand payment, not a second independent
isolate budget. [Cap payment](PAPER_GLOBAL_CAP_PAYMENT.md) adds backed-fold
and specified flat-packet cases. An overbroad arbitrary-isolate flat-packet
transfer failed review and is withdrawn; its corrected outer-J_3 version
passed re-review. [Metric research](PAPER_GLOBAL_METRIC_UPPER.md) gives
non-reusing rail-width charges but no global exposure theorem.
All three notes received independent paper review. The unconditional paper
upper remains T+floor(k/2)+1; no Lean result changed. Bounded examples and
strip work stayed within dimension 15.

**Upper-only continuation:** [planar-dual research](PAPER_DUAL_UPPER_RESEARCH.md)
now proves reviewed paper bounds T+3 or T+6 in several geometric classes,
including isolate-free configurations with arbitrarily many junctions and
long through strands. The no-junction, no-through, long-strand, eligible-end,
and cap-inset hypotheses are stated separately in that note. They do not
cover every feasible set. The general proof still lacks a joint payment for
surviving interior caps and clean short strands. The unconditional paper
and Lean bounds below remain unchanged.

[Contact charging](PAPER_CONTACT_CHARGING_RESEARCH.md) retains the component
credits needed for the exact excess target. [Projection research](PAPER_PROJECTION_UPPER_RESEARCH.md)
and [nested-cycle research](PAPER_NESTED_CYCLE_UPPER_RESEARCH.md) record precise
obstructions to disjoint boxes, local cycle charges, and bounded-error peeling;
none refutes the global target. The dual, contact, and projection deductions
received independent paper review. No Lean build or optimization was run in
this upper-only pass; its literal examples have side at most 14.

**Latest paper research, not a new Lean milestone:**
[the half-coefficient proof](PAPER_HALF_COEFFICIENT_UPPER.md) now proves on
paper `P(3k+2)<=T+floor(k/2)+1` for every k>=3. The fixed residue schedule
and nonempty middle-boundary path argument remove the earlier orientation,
row-count, and all-covered hypotheses. The checked bound below is unchanged.

The latest [positive-loss analysis](PAPER_POSITIVE_LOSS_UPPER.md) retains exact
boundary/contact corrections but does not close the global constant gap. Its
original universal nonnegative contact-loss bound is REFUTED by a low-score
feasible family; the positive-excess-only version remains open. Actual hole
vertices have at most two forced neighbors, so the canonical contact count is
explicit and excess contacts must not be silently discarded.

[Fault-line analysis](PAPER_FAULT_LINE_ANALYSIS.md) now proves a constant
upper excess of four for its specified interrupted-rail family, independent
of the number of interruptions. A complete 58-state strip certificate passed
independent paper review. This is not a theorem for arbitrary fault networks.

[Packing stability](PAPER_PACKING_STABILITY.md) records exact nonnegative
packing and boundary reserves. Their signed-excess identity is
`4(f-T)+c+h+K+Lambda+Omega=2k+11`. A constant upper excess still needs a
geometric lower bound of `2k-O(1)` on the reserve, not this identity alone.
The [endpoint strip](PAPER_ENDPOINT_STRIP.md) is now closed by an explicit
finite-state potential, and [zero-loss upper analysis](PAPER_ZERO_LOSS_UPPER.md)
handles mixed saturated configurations as well. Independent paper reviews
support `Lambda=0 => f<=T+3` for k>=3 and `f<=T+1` for k>=5. These are not
Lean theorems or a global constant-gap bound: positive-loss stability remains
open. The fourth-step continuation budget in the stability note controls
interior terminal events, not the multiplicity of physical fan mergers.

[Constant-gap lower research](PAPER_CONSTANT_GAP_LOWER.md) gives an exact
nested-frame class obstruction and a moving-phase interior with target count
growth. Its proposed cap creates k+1 cycles, so it is NOT a feasible lower
family. [Moving-phase cap research](PAPER_MOVING_PHASE_CAP.md) now allows
arbitrary top-boundary and next-ring replacement but still finds a linear
loss in that fixed-interior class. No `T-O(1)` construction is claimed.
The paper continuations leave Lean unchanged. Their notes distinguish
bounded strip/cap computations from uniform paper arguments; no Lean build
or optimization above side 15 was performed.

[Distributed lower repair](PAPER_DISTRIBUTED_LOWER_REPAIR.md) preserves the
GOOD-edge count while moving paired endpoints. Its proposed isolated-star
promotions are nevertheless blocked by a connection through four rods and
the frame. The restricted family does not improve the source staircase.
The new bounded experiment and three focused tests are under
`analysis/searches/distributed_lower_repair.py` and its mirrored test module;
the main-agent run passed those tests plus the seven layout tests (10 total).
No global constant-gap lower construction or new Lean bound is claimed.

**Latest EndpointUpper milestone:** `P(3k+2)<=T+floor(2k/3)` for ALL k>=5,
with no b/c/r or coverage premises, where `T=3k^2+7k`.
`GridGraphs.maxPreserved_residueTwo_le_endpoint_refinement` in
`Accounting/EndpointUpper.lean` is the public maximum theorem;
`GridGraphs.forced_card_le_endpoint_refinement` applies to every feasible set.
All three old k%3=1 endpoint profiles are closed. The missing-side sharp T
closure and RailRepair lower bound are unchanged. Only the all-covered sharp
upper and accumulating lower pump remain open. Full strict verification passed
9,049 jobs, zero warnings/errors; the audit covers 642 unique public declarations,
including 584 theorems. These are recorded results, not reruns for this docs update.

Read [the U1/U3/L2 handoff](HANDOFF_U1_U3_L2.md) before continuing. Earlier milestones checked the
boundary-six next-ring theorem, a stronger stable upper bound
`P(3k+2)<=3k^2+7k+floor((2k+2)/3)`, global U3 carrier-layer restrictions,
and the actual component budgets of the n11/n14 lower seeds. The previous milestone
proved that ANY missing open side implies f<=T+1 and b>=2k+3 for k>=5,
independently of p. Missing means no pure boundary carrier meets that side,
not zero preserved occupancy. No maximality or connectivity assumption beyond
forced-graph acyclicity is required. In particular p<=3 implies f<=T+1.
The last two-excess profile is excluded; f>=T+2 requires four distinct actual
pure carriers covering all four open sides. Those results remain valid.

The previous milestone strictly compiled five new modules: CarrierLayers
`OneExcessSeparated.lean`, `CoveredBoundary.lean`, and
`Constructions/ResidueTwo/RailRepair/{Geometry,Forest,Score}.lean`.
The terminal repair now has a uniform Lean forest and score theorem:
`L(k)=3k^2+6k+3+floor((k-1)/2)`, k>=3. With the existing upper-route notation
`T=3k^2+7k`, this is `T-floor(k/2)+2` for k>=5.
It gains one over the staircase at odd k and agrees at even k. Full strict
verification passed with 8,939 jobs and 147 public axiom audits (72+31+44).

The preceding pass added `CarrierLayers/ConcentratedGaps.lean` (7 public theorems,
297 lines) and `CoveredDeficit.lean` (9 public theorems, 244 lines). Full strict
verification passed 8,941 jobs and 163 public theorem audits (147 rerun + 16 new).

The preceding pass added five CarrierLayers modules: `GapGlobalCapacity.lean`,
`GapGlobalExclusion.lean`, `GapGlobalMinimal.lean`,
`CoveredGlobalMissingSides.lean`, and `GlobalUpperProfiles.lean`.
For every feasible counterexample f>=T+1, k>=5, there is at most one missing
open side, at least three covered sides, p>=3 (formerly k>=7), and r>=k+3
(formerly k+2). The entire p=3, r=k+2 branch is excluded for ANY c.
That milestone improved the b>=6 branch to `f<=T+floor((2k+1)/3)`, while its
global upper remained `T+floor((2k+2)/3)`. Its historical full strict
aggregate verification passed 8,946 jobs, zero warnings/errors;
183 public theorems plus the separately audited definition `nextRingCarriers`
give 184 dependency reports, not 184 theorems.

The preceding milestone added `Accounting/BoundaryFive/Upper.lean` and
`Accounting/CarrierLayers/FourCarrier/Closure.lean` with their dependencies:
**32 then-new modules**. That milestone's checked global upper was
`P(3k+2)<=T+floor((2k+1)/3)` for **every k>=5 and all boundary budgets**,
not just b>=6. The old endpoint at k%3=2, with `(r,c,b)=(k+4,1,5)`, is
**excluded in that old-maximum context**; this does not exclude all b=5,c=1 sets.

The boundary-five proof derives the generic four-Near-plus-one-Second hole
pattern, then uses a square isometry to position only the gap at `(0,1)-(0,2)`.
Only cardinality and forced acyclicity are transported. Reapplying the old
endpoint profile to the mapped set supplies b=5 and c=1; the actual oriented
perimeter path and inward spokes force a nonpure singleton at `z=(2,2)`.
The singleton capacity bound `f+n<=(n-4)r+12` contradicts endpoint capacity.
The other corner-hole orientations are not assumed canonical. At that milestone
the second-short corner packet was not formalized; it is now checked below.
There is still no generic ambient b=5 strict deep-carrier cap n-5 theorem.

FourCarrier formalizes the off-side path bound `p<=u+1`, where u counts
ordinary off-side holes including corners. It closes the entire p=4 missing-side
branch with f<=T for all k>=5, including k=5. At that milestone every remaining
missing-side counterexample had exactly p=3 and f=T+1; those premises are now
impossible. Its historical full strict verification passed **8,978 jobs, zero warnings/errors**;
**273 public theorems + 4 public definitions = 277 audited reports**.

**Previous Annulus/ThreeCarrier milestone (unchanged):**
`GridGraphs.CarrierLayers.ThreeCarrier.card_le_target_of_missing_side` in
`ThreeCarrier/Closure.lean` proves **f<=T for the ENTIRE missing-side branch,
k>=5, without p or off-side cost W assumptions**. W2 counts an enlarged nonpure
strip including roots and the next ring. Mixed interior-row shadows and the
height-independent joint three-rod bound give `V+H<=(k-1)(3k-1)`.
W3 leaves the extra off-side hole unclassified and maps bad vertical and bottom
horizontal edges jointly to its two incident boundary edges. The defect is
**at most two, not one**: `V+H<=(k-1)(3k-1)+2` yields
`f<=T-k+5<=T`, including k=5. W4 uses global d>=k and connected shallow
carriers. FourCarrier was closed previously. **No W2/W3/W4, mixed/top, or
equality gap remains here.** The eight-case extra-hole adjacency classification
is unused, unformalized, and unnecessary.

Every stable counterexample f>=T+1 now has **all four sides covered**, p>=4,
r>=k+4, and d=r-p-h>=k, where h counts actual shallow nonpure carriers.
`stable_excess_budget` in `AllCoveredCounterexamples.lean` (namespace
`GridGraphs.CarrierLayers`) gives `b+c+3e<=2k+8` for **every e>=1** and
f>=T+e, with no coverage premise. There is no missing-side proof work left.

The global annulus cap is `B+E<=4n-9` for n>=9, with
`K=4n-4-B-E>=5`. For the full two-layer annulus A and selected set S,
`2|S|+rA+cA+i=|A|+o`, including inner/outer corner corrections i/o,
gives `rA+cA+4<=2K`. Literal full-deep-rod edge packets prove
`M+1<=cA`, counting annulus isolates and assuming no quotient/contact forest.
For total deep deficit `D=(n-4)d-|F_deep|`, this gives `r+5<=2K+D`.
The earlier b>=7 bound was `f<=T+floor(2k/3)`. EndpointUpper now makes this
global, including P(23)<=200 and P(32)<=376. All three profiles at the old
k%3=1 endpoint `T+floor((2k+1)/3)` are excluded:

- `(r,c,b)=(k+5,1,5)`: CornerPacket supplies two actual short carriers and
  annulus losses. Square-isometry transport preserves r/c/b and positions only
  the gap, leaving other corner-hole choices free.
- `(k+4,2,5)`: Rootless proves the actual ambient-to-rooted-deep bridge,
  unique boundary roots, four deep corners in U, and q=k. Four distinct
  corner-root carriers force all rods long; nonreused missing triples contradict
  total deficit, including reciprocal and cyclic endpoint orientations.
- `(k+4,1,6)`: the E=1 branch and E=0 with an outer corner in U use the
  connected-annulus deep bridge and rooted endpoint obstruction. For E=0 with
  all outer corners in F, two distinct gaps force two deep corners in F.
  Unless one is a singleton, two literal five-edge packets violate the perimeter
  forest edge count. Singleton capacity then excludes the endpoint, without
  assuming distinct corner carriers.

`CornerPacket.connected_boundary_five_components_ge` proves r>=k+6 for
b=5,c=1,k>=7 with no score or residue premise, not generic b=5,c=1 impossibility.
`Rootless.strict_carrier_cap` proves the strict m-1 cap under
`UniqueBoundaryRoots` on the smaller grid (m>=2); the actual ambient bridge establishes those premises at the
endpoint, not for arbitrary ambient b=5 sets. Reciprocal/cyclic packing is
fully closed at the endpoint, not for all rooted forests. The b=6,E=1
position-3 residual is closed there too: the earlier position-2-only conjecture
was wrong, and no near-only classification is needed.

Next goals: all-covered lower excess `f=T+e, 1<=e<=floor(2k/3)`, quantitative
corner-packet/long-rod/frame-budget losses, and an accumulating lower
repair. [Paper Upper Program](PAPER_UPPER_PROGRAM.md) records the completed
missing-side resolution and retains failed certificates as guardrails.
**PROOF NOT FINISHED:** the all-covered sharp upper and target lower pump
remain open. No remaining excess level is asserted feasible or excluded in
general. The global upper improved; formal L(k) is unchanged.

The following missing-side reductions are historical infrastructure. Their
one-excess premises are now impossible, not remaining research obligations.

The previous milestone's five leaves under `Accounting/CarrierLayers/` are `MissingSide.lean`,
`MissingSideSharp.lean`, `RadialNearTightBoundary.lean`,
`RadialNearTightExclusion.lean`, and `RadialOneExcess.lean`, all strictly audited.
The earlier RadialTight exclusion left the unique numerical profile
`(r,c,b)=(k+2,1,2k+3)`; that was a historical intermediate result. Now, writing
q for roots on a missing side, physical root/pure-carrier nonreuse gives
q+p<=r and the near-tight bounds force p=3, q=k-1. An empty boundary triple
forces an inward F witness because c=1 forbids an ambient isolate at its middle.
Its new carrier gives r>=q+p+1=k+3, contradicting r=k+2. MissingSideSharp
extends the exclusion to any missing side, regardless of p.

For k>=5, p<=3, f>=T+1, the exact one-excess profile is
`f=T+1, r=k+2+a, c=1+d, b=2k+3+e`, with natural `a+d+e=3`.
For missing-side root deficit m=k-q, `m<=e+1` and `p<=a+m+2`.
At saturation `r=q+p`, equivalently `p=a+m+2`, distinct empty-block middles
are ambient isolates, giving `c>=m+1` and `m<=d`. Outside saturation,
inward witnesses may share a horizontal carrier; do NOT claim general nonreuse.
These earlier necessary conditions alone did not exclude one excess; Closure now does.

The earlier GapGlobal bound forced p=3 and a>=1 here, removing all four old a=0
types (d,e)=(0,3),(1,2),(2,1),(3,0). Setting A=a-1 gives
`r=k+3+A, c=1+d, b=2k+3+e, A+d+e=2` at p=3. This is derived
algebra, not a new named Lean API. In particular e<=2 and c<=3.

Write h for `|nextRingCarriers F|`: actual nonpure carriers with no deep
vertices, allowing boundary endpoints. With B/E denoting preserved boundary/
next-ring occupancy, the new global capacity bounds are
`f<=B+E+(n-4)*(r-p-h)` for n>=5 and
`f<=4n-4+(n-4)*(r-p-h)` for n>=7 (natural subtraction).
Each shallow carrier loses deep capacity ONCE, even if many holes reuse it;
the one-excess profile gives h<=a. At h=0, partitioning the boundary-injection
image on/off a chosen open side gives `B+E+H_s<=4n-4+(r-p)`, where H_s
counts that side's actual holes. A missing side has H_s>=2k; at p=3,
r=k+2 this contradicts f>=T+1 for every k>=5, independently of c or corner holes.

`OneExcessSeparated` now proves `q+p+|S|+1<=r+c` for actual root-separated
hole middles S, without root saturation. An intervening preserved root proves
the needed inward-carrier nonreuse; holes in a shared root-free gap may still
reuse a horizontal carrier. For a missing side, k>=5 and `p+|S|>=7` give
the conditional sharp bound f<=T. No theorem guarantees such an S.

`CoveredBoundary` uses actual pure boundary mass P, not the maximum P(n).
Each nonpure carrier has at most two boundary contacts, giving
`B<=P+2(r-p)`; also `B<=P+E` for n>=5. For n>=7,
`4n-4<=P+2b` and `4n-4<=P+b+2(r-p)`. Here B/E are boundary/next-ring
preserved occupancy. These charge the SAME resources and cannot be added as
independent budgets. Neither upper front yields a new unconditional upper bound.

`ConcentratedGaps` proves that, for k>=5, p<=3, f>=T+1, every inclusive
root-free interval on a missing open side has `L<=16` and `L+6k<=3b-2`.
Shared inward-carrier witnesses force the intervening interval to be root-free,
so inclusive spans >=17 are excluded in this branch. Independently, a preserved
interval of length L forces at least `floor(L/2)` actual holes two rows away,
even for arbitrary disconnected preserved occupancy on that row. This local
loss is not globally addable without overlap control. Bounded gaps do not
reduce the whole proof to finite-board search: distant component identifications remain.

Combining `L+6k<=3b-2` with the now-derived e<=2 gives `L<=13` in
the same one-excess branch. The old named L<=16 theorem remains valid;
L<=13 is a derived consequence, not a new named API or finite-board reduction.

`CoveredDeficit` defines the shadow union S of actual boundary holes, counting
shared witnesses once (not the earlier selected root-separated middles).
Write P for pure boundary mass and `D=n*p-P`. For n>=7, p=4 gives
`D>=|S|+4`; all-side coverage gives `D>=n*(p-4)+|S|+4`.
A top next-ring segment of length L>=2, with endpoints in one actual carrier
and columns in [1,n-2], casts L+2 contiguous holes (n>=5), hence `D>=L+6`
for n>=7, p=4. For k>=5, `|S|+2p+b+2c>=6k+19` suffices for f<=T,
but is NOT guaranteed. Importantly, `|S|<=b` makes this certificate at p=4
force `b+c>=3k+6`, already stronger than the old sufficient `b+c>=2k+8`.
It is not a new sharp branch solution; the new value is the physical shadow/length link.

For L2, [the fixed-rail pocket note](L2_FIXED_RAIL_POCKET.md) gives a scoped paper argument:
repacking only the bottom two deep rows while keeping the frame and rails fixed
cannot beat the existing count. This is not yet a Lean theorem and does not
rule out a pump that changes a rail, an attachment, or another region.

[Terminal rail repair research](L2_RAIL_REPAIR_RESEARCH.md) gives a uniform
forest proof, now backed by uniform Lean theorems, with
`G(s)=3s^2+12s+12+floor(s/2)`, s>=2, n=3s+5.
It gains one over the staircase for even s and is count-neutral for odd s,
but still gains only 12s+37 per six-width step, not 12s+38. It is not an
accumulating pump: in k=s+1 notation the gain is 12k+25, not 12k+26. The module
`analysis.searches.l2_rail_repair_research` searched only n=11/14; with the
original frame and earlier rows fixed, last-four-deep-row repacking has finite
restricted-class maxima 49/76, not global optima. The historical packaging pass
passed three focused repair tests and seven layout tests without searches
during tests. An actual propagating repair must change the attachments that
cause the attempted repeated motif's component collision. The previous main-agent
test run passed 13 tests (three terminal, three propagating, seven layout),
without searches. The [propagating-interface alternative](L2_PROPAGATING_INTERFACE.md)
remains a paper forest argument for an unsuccessful actual-gain candidate,
not the verified single terminal repair or a target pump.

The [two-rail/notch follow-up](L2_TWO_RAIL_INTERFACE.md#notch-follow-up) gives
restricted n11/n14 maxima 49/76 unrestricted, 48/75 rootless, and 47/75
joined-rootless. All six notch searches were capped at 100,000 nodes and
finished exhaustively within their restricted windows, not as global bounds.
Explicit independent joined outputs exist, but the unchanged extra continuation
closes a cycle; deleting the obstructing tail center makes the extension
count-neutral. The next step either meets another tail square or consumes
independence through the frame. That main-agent run passed 19 tests,
with no searches during tests. This finite/paper evidence is not Lean-formalized
and establishes neither a recurring gain nor a target pump.

[Terminal tail interface](L2_TERMINAL_TAIL_INTERFACE.md) now gives a 76-center
n=14 forest with an actual 43-vertex rootless output and a separate frame-attached
cap. Its paper family still gains only 12k+25, not an accumulating pump.
Ten bounded searches ran only at n=11/14: nine were exhaustive in their windows;
the n=14 joint joined-output search hit 100,000 nodes, so its 76 is a lower
bound, NOT a maximum. The historical main-agent run passed 23 tests without
optimization searches during tests (fixed replays and one-node cutoff checks).
This is finite/paper evidence, not a new Lean lower theorem. No Python application
files were changed and those 23 tests were not rerun. Earlier bounded finite-capacity
certificate experiments used coordinates at most 13, not a full-grid optimizer.
No Python search or tests were run in the recorded verification pass or this docs update.

## Research Route Labels

These are the canonical meanings of U1/U2/U3/L1/L2/L3 from the latest plan.
Older planning documents sometimes used these labels differently. Use the
definitions here going forward. They are research routes, not six completed
theorems or a mandatory sequential pipeline. U means upper bound; L means
lower bound.

For n=3k+2, write `T(k)=3k^2+7k` (the conjectured value for k>=5). Here b is complementary
boundary deficiency, r counts induced preserved components, and c counts all
forced-graph components, including isolates. A pure boundary carrier is an
induced preserved component lying entirely on the outer boundary; p counts them.

| Label | Route | Goal and current position |
|---|---|---|
| **U1** | **Boundary-six control** | Global `P(3k+2)<=T+floor(2k/3)`, all k>=5, no b/c/r/coverage premises. The old b=6 endpoint, including E=1 position 3 and E=0 corner cases, is closed. All-covered sharpness remains open. |
| **U2** | **Boundary-five attachment rigidity** | Both old k%3=1 b=5 endpoints are closed by actual corner packets and the rooted-deep bridge; the old k%3=2 endpoint stays closed. Generic b=5,c=1 gives r>=k+6 for k>=7 without a score premise, not impossibility. Strict cap is checked under UniqueBoundaryRoots, not as a generic ambient n-5 cap or `f<=(n-5)r+11` theorem. |
| **U3** | **Global near-extremal packing** | Missing-side f<=T is closed for k>=5 without p/W assumptions. Remaining `f=T+e`, `1<=e<=floor(2k/3)` is all-covered, p>=4, r>=k+4, d>=k, with b+c+3e<=2k+8. Seek quantitative nonreused losses, not the three excluded old endpoints. |
| **L1** | **Relayout and absorb uncovered vertices** | Rearrange the staircase's rails and attachments so that more uncovered vertices become legal promotion sites. Prove actual coordinates and attachments. The terminal parity repair is now checked, but a target-count relayout is not known. Disconnected forced forests and unrooted components are allowed. |
| **L2** | **Six-width pump from the small seeds** | Construct an actual `k -> k+2` operation gaining `12k+26`, with compatible 11x11/14x14 seeds (historical staircase scores 48/76 and budgets are checked). Formal L(k) and the new paper tail/cap family still gain only `12k+25`. The 76-center n14 rootless output is progress on the interface, not an accumulating pump. Actual six-width closure remains open. |
| **L3** | **Alternative boundary or direct dual construction** | Leave the staircase architecture if necessary. Either choose another controlled boundary pattern, such as b=6, and pay its full component budget, or construct an unpreserved set U of size `6k^2+5k+4` with connected U-U dual. Actual coordinates and connectivity must give the target lower bound. No exact arbitrary-width alternative family is known. |

The selected emphasis is **U1 and L2, pushing into U3**. U2 supplies useful
attachment geometry; L1 and L3 remain alternatives rather than requirements.

Upper-route completion means an unconditional bound on every feasible set,
not merely an exclusion inside a chosen construction class. Lower-route
completion means a feasible target-count family at every required width.
Matching the two proves the optimum. A seed budget or a count recurrence alone
does not complete a lower route.

Source layout: the 342 Lean modules under `GridGraphs/` are grouped under `Core`, `Forests`,
`Geometry`, `Accounting`, `Routing`, `Surgery`, `Constructions`, `Results`,
and `Tests`. Construction families have their own subfolders. Public theorem
namespaces and the `import GridGraphs` entry point are unchanged; module
imports and live path references have been updated. See `lean/README.md` for
navigation. The reorganized source tree has passed a fresh full strict build,
including the five modules outside the aggregate import closure.

Python layout: the 283 former flat analysis sources now live in eight subject
packages with mirrored tests. Run them with `python3 -m analysis.<area>.<module>`
from the repository root. `analysis/README.md` documents the layout, bounded
checks, and historical provenance policy. Existing result artifacts were not
regenerated; source snapshots and an explicit before/after migration ledger
preserve their provenance. The smoke/layout suite and six targeted provenance
checks historically passed (29 tests total), with no optimization searches.

## Verification Status

Lean and mathlib are pinned to `v4.33.1`. The reorganized project passed full
verification with **zero errors and zero warnings**: 9,049 jobs, exit 0.
The command, run from `lean/`, was:

```bash
LEAN_NUM_THREADS=2 lake --no-cache --wfail build GridGraphs \
  GridGraphs.Tests.FourCropBoundaryCounterexample \
  GridGraphs.Tests.GroupedAlternatingClosureCounterexample \
  GridGraphs.Tests.InsertionReflexCounterexample \
  GridGraphs.Constructions.ResidueZero.ResidueZeroPersistentEnds \
  GridGraphs.Results.SmallDiagonal
```

This covers all **342 source modules**, including the original five outside
the aggregate closure, reusing cached mathlib dependencies rather than running
a separate mathlib-wide verification. The completed log is
`/tmp/opencode/endpoint-upper-final-full-build.log` (same-stem `.exit` is 0).
There are **100,477 lines under GridGraphs**, plus the **188-line root:
343 library files and 100,665 lines total**. The reported targeted
EndpointUpper/Regression build passed 8,882 jobs, separate from this full
strict count. No build is active.

The unchanged external `TotalCurrentAudit.lean` and `AnnulusThreeCarrierAudit.lean`
reran all **441** previously audited declarations. The generated
`/tmp/opencode/endpoint-upper-final-Audit.lean` checked **202 new/changed exports**:
200 from new files plus both exports of existing Symmetry. The old Symmetry
theorem `exists_top_gap_pullback` is the only overlap, so **441+202-1=642
unique public declarations**, comprising **584 theorems + 50 definitions +
3 abbreviations + 5 structures**. All three drivers import only `GridGraphs`.
Kinds, unique names, and coverage were checked independently. Dependencies
are subsets of `{propext, Classical.choice, Quot.sound}`, possibly empty;
no `sorryAx` or native proof axiom occurs in this audit. Generated constructors,
projections, and recursors are not extra source entries; private helpers are
covered transitively where used.

Exact current logs, as recorded in [Lean EVIDENCE](../lean/EVIDENCE.md):

- `/tmp/opencode/endpoint-upper-final-TotalCurrentAudit.log`
- `/tmp/opencode/endpoint-upper-final-AnnulusThreeCarrierAudit.log`
- `/tmp/opencode/endpoint-upper-final-endpoint-upper-final-Audit.log`
- `/tmp/opencode/endpoint-upper-final-inventory.log`
- `/tmp/opencode/endpoint-upper-final-post-audit-check.log`
- `/tmp/opencode/endpoint-upper-final-verification-summary.log`

Source/root/configuration fingerprints, including every test, stayed unchanged
through build and audit. All **300 old non-Regression/Symmetry modules** match
the prior Annulus/ThreeCarrier snapshot. Existing Symmetry intentionally adds
the isometry export while preserving its old theorem statement. This is not
a whole-workspace or mathlib hash.

| New group under `Accounting/` | Modules | Lines | Theorems | Definitions | Abbreviations | Structures |
|---|---:|---:|---:|---:|---:|---:|
| `BoundaryFive/CornerPacket/` | 6 | 1,196 | 30 | 0 | 0 | 0 |
| `BoundaryFive/Rootless/` | 15 | 2,206 | 69 | 12 | 0 | 2 |
| `BoundarySix/Connected/` | 18 | 2,402 | 73 | 10 | 1 | 1 |
| `EndpointUpper.lean` | 1 | 46 | 2 | 0 | 0 | 0 |
| **Total** | **40** | **5,850** | **174** | **22** | **1** | **3** |

All new modules are **31-521 lines**, below 1,000. All 11 pre-existing oversized
modules listed in [Lean STATUS](../lean/STATUS.md) are untouched. All 40 new
modules are root-reachable: the verifier added the otherwise unused valid
`BoundarySix.Connected.RingEndpoint` root import before the snapshot;
EndpointUpper was already imported. RingEndpoint's old necessary conditions
now have impossible endpoint premises, not a remaining branch.
Regression passed the uniform refined interval, unconditional P(23)<=200 and
P(32)<=376, and the unchanged checks at sides 17, 20, 26, 29, and 35, alongside
the missing-side and older component tests. No Regression repair was needed.

This is **not a whole-library axiom audit**: six legacy `native_decide` uses in
three separately built counterexample tests remain outside coverage. See
[README](../lean/README.md) and [EVIDENCE](../lean/EVIDENCE.md) for commands and
inventory. These are recorded verification results, not a Lean/Python rerun for
this docs-only update. No Python application files changed and no Python or
optimization searches ran. Earlier bounded capacity experiments used coordinates
at most 13, not a full-grid optimizer; the historical 23 Python tests were not rerun.

Migration fixes preserve theorem statements and certificate data. Existing
finite certificates now use efficient kernel-checked fixed-entry replay, not
new searches or native proof axioms. Linter warnings were removed rather than
suppressed. No proof placeholders or global backward-compatibility flags were
added. The staircase construction, boundary-stratified upper bound, and exact
`P(7)=22` and `P(10)=42` results are included in this verified build.

This is the working roadmap. Historical roadmaps and analysis notes retain
the previous programs, evidence, and failed approaches for reference. Their
task ordering is not binding. Reuse valid mathematics, not accumulated workflow.

**Updated residue-zero result:** [exact for every positive multiple of three](EXACT_RESIDUE_ZERO.md).
**Side 109, tenth row:** [a redistributed joint flow scores `28667/7`](CAP_PERIOD_UPPER_BARRIER.md#ten-rows-retain-the-integer-upper-of-4095);
the integer upper remains 4095.
**Side 109, ninth row:** [exact dual excludes 4096 after redistribution](CAP_PERIOD_UPPER_BARRIER.md#nine-rows-exclude-4096).
The whole-grid interval is now 4077–4095.
**Side 109, eighth row:** [the seven-row point fails to lift, but a redistributed flow scores `12289/3`](CAP_PERIOD_UPPER_BARRIER.md#eight-rows-retain-the-integer-upper-of-4096).
The complete eight-row relaxation still has integer floor 4096.
**Side 109:** [the complete seven-row strip excludes 4097](CAP_PERIOD_UPPER_BARRIER.md#seven-rows-exclude-4097-even-after-redistribution);
its certified integer floor is 4096. The grid interval is now 4077–4096.
**Side 119:** the rail replay gives 4831 full-degree vertices and the
unrestricted dual gives `67649/14`, hence an integer upper of 4832.
`python3 -B -m analysis.research_program.side119` also constructs trees
with exactly 4754 and 4753 full-degree vertices. For the upper candidate
4832 a DRAT-checked exclusion applies if the central 79×79 marked pattern
is fixed to the rail construction, with the entire 20-site boundary strip
free. Regenerate that restricted CNF with `tight_corner_sat --side 119
--roots 1 --matching --free-rail-margin 20`; it has 348311 variables and
2424497 clauses. This exclusion does not rule out changing the center.
**Residue two, alternating bands:** [exact at every `56+42t`](ALTERNATING_ZIPPER.md),
including 1097 at side 56 and 3293 at side 98. This settles the remaining
even-`k` progression; only `n ≡ 35 (mod 42)` lacks a tail formula.
**Residue two, even `k`:** [delayed right-front construction](DELAYED_RIGHT_ZIPPER.md)
is sharp on the six tails beginning at 38, 44, 50, 62, 68, and 74 modulo
42. Together with the odd-`k` results this settles twelve of fourteen
tail progressions; the exceptions are sides 14 and 35 modulo 42.
**Residue-two one-waiting-row repair:** [exact on `71+42t`](REPAIRED_ZIPPER_PROGRESSION.md#one-waiting-row-the-progression-beginning-at-71),
including 1746 at 71 and 4362 at 113.
**Side-109 complete six-row test:** [exact primal and dual bracket](CAP_PERIOD_UPPER_BARRIER.md#complete-six-row-transfer-the-integer-upper-stays-at-4097)
proves that the integer upper remains 4097 even with the full joint six-row strip.
**Side 109:** [complete four-row top-strip transfer](CAP_PERIOD_UPPER_BARRIER.md#complete-top-strip-transfer-at-109)
lowers the verified integer upper to 4097 (construction 4077).
**Residue-one upper update:** [all pinned single-bit agreements](CAP_PERIOD_UPPER_BARRIER.md#enforcing-all-single-site-agreements-on-pinned-neighboring-patches)
give `P(3k+1,3k+1)<=3k²+6k−6` for `k>=8`.
**Residue-one repeating upper search:** [period-30 test and fractional barrier](CAP_PERIOD_UPPER_BARRIER.md);
for `k=16+10j`, the unpooled square-patch LP cannot certify the cap target from `j=2` onward.
**Finite closures:** [P(49,49)=851](FOUR_ROW_COMB_CAP.md#exact-side-49)
by unpooled dual replay; [P(77,77)=2047](SIDE_77_TEST.md) by checked
infeasibility of the corner-rooted matching model at 2048.
**Four-row cap:** [P(46,46)=753 and a period-ten growing lower correction](FOUR_ROW_COMB_CAP.md).
**Residue-one finite result:** [P(43,43)=660](RESIDUE_ONE_WITNESS_EXTENSION.md#side-43-the-upper-rounds-to-661-but-661-is-impossible);
the unpooled upper permits 661, excluded by a checked SAT certificate.
**Residue-two waiting-row repair:** [exact on all sides `47+42t`](REPAIRED_ZIPPER_PROGRESSION.md#two-waiting-rows-the-progression-beginning-at-47),
including 779 at 47 and 2723 at 89.
**Residue-two transition:** [P(35,35)=439 and P(38,38)=515](UNRESTRICTED_PERIOD_THREE_UPPER.md#replay).
The former uses a checked SAT exclusion; the latter attains the repeating
upper's integer floor with an explicit forced forest.
**Sharp residue-two subprogression:** [a seven-row rail transition](RESIDUE_TWO_ZIPPER.md)
also has [sharp five- and six-row endings at all `23+42t` and `41+42t`](PARTIAL_BAND_PROGRESSIONS.md).
and the [repaired-prefix induction for all `53+42t`](REPAIRED_ZIPPER_PROGRESSION.md)
and its [upper-left repair at 53](RESIDUE_TWO_ZIPPER.md#side-53-the-last-band-cannot-fix-the-deficit-but-the-opposite-corner-can)
gives `P(41,41)=597` and attains the certified tail upper at every
`n=59+42t`, `t>=0` (computer-assisted construction proof).
**Updated residue-one counterexample:** [P(28,28)=289, not 288](RESIDUE_ONE_STRIP_CUT.md#exact-optimum-at-side-28-the-larger-value-is-attained).
The [repeatable witness extension](RESIDUE_ONE_WITNESS_EXTENSION.md) proves a
one-vertex improvement for every `k>=9`, with `P(31,31)=351` exact.
At [side 34](RESIDUE_ONE_WITNESS_EXTENSION.md#side-34-the-unpooled-patch-lp-crosses-the-next-integer),
a different forest gives `P(34,34)=420`, one above that family.
Its [repeatable extension](RESIDUE_ONE_WITNESS_EXTENSION.md#extending-the-side-34-rails)
gives `P(37,37)=494` and `P(3k+1,3k+1)>=3k²+5k+2` for every `k>=11`.
The previously conjectural upper half now has a rational certificate.

## 1. Goal And Completion Criterion

For a spanning tree of the n by n grid, a preserved vertex retains its full
grid degree. Let `P(n)=maxPreserved n n`.

The conjectured formula, for n >= 3, is

```text
P(3k)   = 3k^2+3k-2,     k >= 1,
P(3k+1) = 3k^2+5k,       k >= 1,
P(3k+2) = 3k^2+7k+1,     1 <= k <= 4,
P(3k+2) = 3k^2+7k,       k >= 5.
```

The active research focus is residue two. A solution requires an unconditional
upper bound and a feasible construction attaining it. Conditional assembly,
an abstract tree with the right count, and finite examples are not solutions.
The formula itself remains open to revision if mathematics contradicts it.

### Completion Chains

Lower, using the optional canonical b=5 construction:

1. **Checked:** construct the actual outer frame, prove its support is one tree,
   and identify the unattached next-ring vertex.
2. **Checked:** prove the exact inner attachment iff and count the extension
   as `4n-9+|A|`, with a theorem transferring that score to `maxPreserved`.
3. **Open mathematics:** construct A uniformly for k>=7, inside the twice-cropped
   square, with `|A|=3k^2-5k+1`, acyclic incident-edge graph, and no inner path
   between distinct frame-attachment vertices. No such target family is known.
4. Verify its coordinates and attachment invariant in Lean, then combine the
   resulting tail with the existing finite and other-residue constructions.

Upper, via the common budget inequality:

1. **Open mathematics:** prove `B>=n+4` for every feasible F.
2. **Open mathematics:** at n=3k+2, exclude `B=3k+6`, giving `B>=3k+9`.
3. **Open mathematics:** for k>=5 also exclude `B=3k+9`, giving `B>=3k+12`.
4. Apply the exact ledger to obtain all three residue upper bounds. The common
   bound suffices arithmetically for residues zero and one.

A direct stable proof `B>=3k+12` may replace the first three steps in that
range. Neither the upper strategy nor the lower b=5 subclass is mandatory.
Completing the checked lower reduction does not prove existence of its input
and does not establish an upper bound for b>=6.

## 2. What Is Actually Available

| Result | Status |
|---|---|
| Maximum preserved vertices equals maximum feasible forced-set size | Established in Lean |
| Exact component and boundary ledgers | Established in Lean |
| Exact values P(3)=4, P(4)=8, P(5)=11, P(7)=22, P(10)=42 | Established in Lean |
| Residue-zero and residue-one matching lower constructions | Established in Lean |
| Residue-two target-score lower witnesses through n=20 | Established in Lean |
| Previous uniform affine residue-two lower bound `3k^2+6k+5`, k>=5 | Established in Lean; still valid |
| Previous staircase lower family `3k^2+6k+2+floor(k/2)`, k>=3 | Unconditionally proved in Lean: `ResidueTwoStaircaseForest.lean`; current RailRepair improves odd k |
| Stable residue-two upper bound `P(3k+2)<=T(k)+floor(2k/3)`, k>=5 | Established in Lean: `EndpointUpper.lean`, no b/c/r/coverage premises; supersedes BoundaryFive floor `(2k+1)/3` |
| Any missing open side gives f<=T, k>=5, independent of p/W | Established in Lean: `ThreeCarrier/Closure.lean`; entire branch closed, including mixed/top/equality cases |
| Exact p<=3 one-excess slack and saturated-root isolate bounds | Historical checked reductions in `RadialOneExcess.lean`; one-excess premises now impossible |
| Root-separated holes and covered-boundary pure mass | Established in Lean: `OneExcessSeparated.lean`, `CoveredBoundary.lean`; conditional sharpness only, no new global upper |
| Concentrated gaps and covered shadows | Established in Lean: `ConcentratedGaps.lean`, `CoveredDeficit.lean`; scoped gap bound, local row loss, and physical shadow/length link, not a new numerical bound |
| Global shallow capacity and coverage | Established in the preceding five CarrierLayers modules: k>=5, f>=T+1 implies at most one missing side, covered>=3, p>=3, r>=k+3; all p=3, r=k+2 excluded for any c |
| Refined upper profiles and endpoint exclusion | Historical `GlobalUpperProfiles.lean` classifies the k%3=2 old endpoint as `(r,c,b)=(k+4,1,5)`; `BoundaryFive/Upper.lean` now excludes that endpoint, not all b=5,c=1 sets |
| Off-side path and four-carrier closure | Previously established in `FourCarrier/OffsidePath.lean` and `Closure.lean`: p<=u+1 for ordinary off-side holes including corners; p=4 missing-side f<=T for every k>=5; the subsequent ThreeCarrier closure removes the last p=3 case |
| Annulus cap, physical bridges, and deficit | Established in `Annulus/{Cap,Bridges,Deficit}.lean`: B+E<=4n-9, K>=5, rA+cA+4<=2K, M+1<=cA, r+5<=2K+D, n>=9 |
| Global stable counterexamples | Established in `AllCoveredCounterexamples.lean` and `Annulus/Counterexamples.lean`: all-covered, p>=4, r>=k+4, d>=k; b+c+3e<=2k+8 for every positive excess |
| Endpoint profile closure | All three old k%3=1 profiles from `Annulus/Upper.lean` excluded by CornerPacket, Rootless.AmbientEndpoint, and BoundarySix.Connected.Upper; their necessary-profile implications remain valid with impossible premises |
| Terminal rail repair L(k) | Uniform formal lower `3k^2+6k+3+floor((k-1)/2)`, k>=3, in `RailRepair/Score.lean`; not an accumulating pump |
| Propagating-interface alternative J(s) | Paper-only forest argument; actual score fails the target pump gain |
| General sharp square upper bounds | Still open |
| Carrier-length upper bound `P(n)<=n*(n*n+4*n-6)/(3*n+1)`, n>=5 | Unconditionally proved in Lean; division rounds down |
| Stronger boundary-stratified upper bound `P(n)<=n*(n*n+4*n-7)/(3*n+1)`, n>=7 | Unconditionally proved in Lean |
| Residue-two counterexample budget restrictions | Checked necessary conditions, not exclusions of all counterexamples |
| Horizontal carriers two rows apart overlap in at most one column | Checked local packing theorem |
| Residue-two target lower family for k>=7, starting at n=23 | Still open |
| Five-unit boundary bound and target component obstruction | Established in Lean: `BoundaryFiveBudget.lean` |
| Boundary-five corners, boundary count, and unique gap | Established in Lean: `BoundaryFiveEquality.lean` |
| Entire next ring unpreserved at b=5, n>=7 | Established in Lean: `BoundaryFiveEquality.lean` |
| Canonical outer-tree and exact support/spoke decomposition | Established in Lean: `BoundaryFiveFrame.lean` |
| Canonical inner attachment necessity and sufficiency | Established in Lean: `BoundaryFiveAttachment.lean` |
| Concrete extension count and transfer to maxPreserved | Established in Lean: `BoundaryFiveConstruction.lean`, conditional on an inner input |
| Arbitrary b=5 normalization and deep-square Q reformulation | Still partly paper-level |
| Full formula assembly | Established only conditionally |

Residues zero and one are complete on the construction side, not yet as
unconditional arbitrary-width exact formulas. A residue-two-specific proof
need not wait for the common upper theorem; a full diagonal result still
needs the other residues' upper bounds.

The new boundary and staircase axiom audits contain only `propext`,
`Classical.choice`, and `Quot.sound`. The verified improved lower bound is not
the conjectured optimum; the open upper/lower obligations above remain open.

## 3. The Central Model

For any set F of grid vertices, put `U=V\F` and let H contain every grid
edge incident to F, on the full grid vertex set. Then

```text
F feasible <=> H acyclic.
P(n) = max_(F feasible) |F|.
```

A feasible H need not be connected: it extends to a spanning tree. Define

```text
f = |F|,
r = number of components of grid[F],
c = number of components of H, INCLUDING isolated U vertices,
b = sum_(u in U) (4-deg_grid(u)),
B = r+c+b.
```

Corners in U contribute twice to b. The established component ledger gives

```text
3f+B = n^2+4n.
```

For n=3k+2 the entire residue-two conjecture becomes

```text
min_(F feasible) B = 3k+9,    1 <= k <= 4,
min_(F feasible) B = 3k+12,   k >= 5.
```

This is an exact reformulation, not an upper-bound proof. It puts construction
and obstruction on the same accounting system and permits a direct proof
instead of making the historical contour-routing pipeline mandatory.

## 4. New Deductions

Detailed paper proofs and qualifications are in
`analysis/RESIDUE_TWO_COMPONENT_BUDGET.md`. The boundary lower bound and
component obstructions now also have unconditional Lean proofs.

### Boundary Budget

Every feasible F on a square of side n>=5 satisfies `b>=5`.

At each corner, its two boundary neighbors cannot both be F: they would force
the corner unit-cell cycle. The four disjoint pairs therefore require four
noncorner boundary U vertices. If b<=4, these are the only boundary U vertices
and none are adjacent when n>=5. Every perimeter edge would then be forced,
again a cycle. This proves the fifth unit is necessary.

For n>=6, equality b=5 forces exactly one perimeter UU edge. This uniqueness
is now checked in Lean, as are preservation of all corners and the count of
five complementary boundary vertices. The oriented actual perimeter-path and
spoke geometry used by BoundaryFive.Upper is now checked; the full arbitrary
attachment/Q decomposition remains partly paper-level. None of these results proves
that optimal constructions must have b=5.

### Component Obstruction

At stable target size `f=3k^2+7k`, the ledger and `c>=1,b>=5` imply

```text
r+c+b = 3k+12,
r <= 3k+6.
```

Consequences:

- The proposed counter skeleton with `4k+1` distinct maximal preserved
  components is impossible for k>=6, hence throughout its intended k>=7 range.
- Retaining `4k` distinct components at target count is impossible for k>=7.
- At n=23 the target permits at most 27 components. The counter proposal has
  29, and the audited affine architecture has 28.
- The average maximal preserved interval length at target is at least
  `(3k^2+7k)/(3k+6)>k`. A bounded-island construction cannot work uniformly;
  tile segments must concatenate into long components if tiles are used.

The abstract counter tree and its summed lengths remain arithmetically valid.
Their intended grid realization does not. Merging labeled intervals changes
the skeleton; overlapping them requires recounting the preserved set.

### Successor Budget

The uniform affine score has `B=6k-3`. The stable target has `B=3k+12`.
Thus the affine deficit is k-5 preserved vertices, or `3(k-5)` budget units.

```text
Exact successor:  Delta f=6k+10, Delta B=3.
Affine successor: Delta f=6k+9,  Delta B=6.
```

A viable new successor must address component/boundary growth, not just add
one more preserved vertex to an unchanged incidence architecture.

## 5. Formal Milestone And Next Gate

Completed in `lean/GridGraphs/Accounting/BoundaryFiveBudget.lean`:

1. `five_le_boundaryDeficiencySum_compl`: `b>=5` for every feasible F and n>=5.
2. `induced_components_le_three_mul_add_six`: `r<=3k+6` at target count.
3. `not_feasible_target_of_four_mul_le_components`: rules out `r>=4k`, k>=7.
4. `not_feasible_target_of_four_mul_add_one_le_components`: rules out
   `r>=4k+1`, k>=6.

These are statements about actual grid sets. Two symbolic regression examples
specialize the obstructions to sides 23 and 20, without enumerating grids.
The proof reuses the existing unit-cell unforced-edge theorem and forest
extension/perimeter theorem; no new general routing framework was needed.

Also completed in `lean/GridGraphs/Accounting/BoundaryFiveEquality.lean`:

1. `boundaryDeficiencySum_compl_eq_five_corners_and_card`: all corners in F
   and exactly five complementary boundary vertices, n>=6.
2. `boundaryDeficiencySum_compl_eq_five_witness_decomposition`: four independent
   corner witnesses plus one extra boundary vertex, with at most one neighbor
   among those witnesses.
3. `boundaryDeficiencySum_compl_eq_five_unique_perimeter_edge`: existence and
   uniqueness as an unordered `Sym2` edge, not a directed-edge count.
4. `boundaryDeficiencySum_compl_eq_five_no_boundary_distance_two`: same-side
   vertices two grid steps apart cannot both be complementary, n>=7.
5. `boundaryDeficiencySum_compl_eq_five_next_ring_notMem`: the entire boundary
   of the once-cropped square is unpreserved, n>=7.

The equality module and regression tests pass on Lean 4.33.1. Tests instantiate
gap uniqueness at side 8 and next-ring exclusion at the threshold side 7,
without enumeration. Axiom audits report only `propext`, `Classical.choice`,
and `Quot.sound`.

The normalized frame and attachment gates are now checked:

- `BoundaryFiveFrame.Houter_isAcyclic` and `support_isTree` prove the actual
  canonical frame is a forest with one nonisolated component, unconditionally.
- `BoundaryFiveFrame.support_eq`, `w_no_neighbor`, and the unique-spoke
  theorems identify precisely its outer-two-ring support and exceptional vertex.
- `BoundaryFiveAttachment.Houter_sup_isAcyclic_iff` proves that an inner graph
  J whose edges stay in the once-cropped square can be attached iff J is a
  forest and no J-component connects two distinct frame-attachment vertices.
- `BoundaryFiveConstruction.Ffull_isAcyclic_iff` instantiates this for the actual
  union of the boundary centers with a deep input A. `Ffull_card` proves the
  exact count, and `residueTwo_le_maxPreserved` gives the conditional target.

These modules and tests pass on 4.33.1, with only the standard logical axioms.
They do not assume all inner components are rooted. The primary remaining
lower research gate is now the explicit input A, not another frame-gluing API.
Normalization of every arbitrary b=5 configuration and the equivalent Q
description on a smaller vertex type are separate remaining formal obligations,
not dependencies of the canonical lower construction.

## 6. Lower Track: Geometry With The Right Budget

The next research deliverable is a coordinate-defined target family or a
coordinate-defined successor with a provable invariant. Design coordinates
and topology together. Do not require an abstract skeleton to be completed first.

Every candidate must specify and justify f, r, c, b. Reject it immediately if
the ledger fails. Track isolated U vertices explicitly: an interval-incidence
tree may be connected while H has many isolated vertices.

Allow nonlocal rearrangement, deletion or merging of old components, and a
growing interface of ordered interval identities and attachment ancestry.
There is no requirement that every old interval remain a distinct successor
node. A merger that closes an old attachment path must identify the physical
connection removed or rerouted. A parent label alone does not establish this.

An optional sharply specified design class is

```text
b=5, c=1, r=3k+6, f=3k^2+7k.
```

Here H itself is a spanning tree. Its boundary contains the perimeter path
from the equality lemma. If u_j counts U vertices with j F-neighbors, then

```text
u_0=0, u_2=3k+5, u_1=6k^2+2k-1.
```

Its successor would have `Delta r=3`, `Delta u_2=3`, and `Delta u_1=12k+8`.
This is a conjectural sufficient class. No base in it is asserted to exist.
Failure of this class is not failure of the formula: permit other c,b splits
with the same total budget.

### Exact Boundary-Five Peeling

There is a two-way paper reduction, independently audited, in
`analysis/BOUNDARY_FIVE_PEELING.md`. Its unique-gap and next-ring ingredients,
canonical frame, and canonical attachment equivalence are now formalized.
The full arbitrary-configuration normalization is not. For n>=7 and b=5,
normalize the unique perimeter UU edge to `(1,2)--(1,3)` in coordinates 1..n. Then:

- The entire next ring is U, forced by unit-cell obstructions.
- The outer two rings form one forced tree T and one unattached U vertex
  `w=(2,3)`.
- On the deep square D of side m=n-4, H_D must be a forest, its three corners
  other than the designated corner z must be U, and each H_D component may
  contain at most one preserved boundary vertex.
- These conditions are sufficient as well: each rooted inner component
  attaches once to T, and z, if preserved, picks up w as a leaf.

Let Q(m) maximize the inner preserved count subject to those conditions. Then

```text
max_(F feasible, b(F)=5) |F| = 4n-9+Q(n-4).
```

Do not replace Q by unrestricted P. The one-root-per-component condition is
exactly what prevents cycles through the outer tree.

At n=3k+2, the new concrete lower target is a Q-family on side `3k-2`
with `3k^2-5k+1` preserved vertices. It need not be fully rooted. In the
optional c=1 subclass, z is preserved and EVERY H_D component has exactly
one preserved boundary root, including all isolated vertices in the accounting.
Then the induced inner F has `3k+2` components.

The arbitrary-b=5 Q reformulation is not yet fully formalized, and Q has not
been evaluated. The checked construction API instead uses A in ambient
zero-based coordinates `2<=row,col<=n-3` and counts its actual forced edges
and attachments. This is already sufficient to build the lower family if A
is supplied. For the
fully rooted subclass there is also a paper obstruction: any horizontal
preserved interval on row 3 has length at most five, with rotated versions
on the other tracks two steps from a side. A long rail there cannot be fixed
by assigning it a remote root; the boundary vertices above it need domination.

### Historical Staircase Family

Section 8 of `analysis/BOUNDARY_FIVE_PEELING.md` gives actual coordinates
and the proof of score `3k^2+6k+2+floor(k/2)`, k>=3, now formalized in
`ResidueTwoStaircase.lean` and `ResidueTwoStaircaseForest.lean`. A staircase
of opposing intervals is extended by alternating bottom-boundary singleton
stars and interior stars attached to its last left interval. Every attachment
is identified physically, and the count is a symbolic sum.

This strictly improves the affine family for k>=8. Its remaining stable gap is
`floor((k-1)/2)-1`; it does not solve the target. Lean proves the actual center
count, placement, support intersections, and unconditional forced acyclicity
by two finite gluing inductions. `residueTwo_le_maxPreserved` has only the
arithmetic assumption k>=3, not an unproved forest or attachment hypothesis.
The proof works directly in ambient coordinates without the full arbitrary-b=5
Q equivalence. No search, including at large widths, was used.

### Current Terminal Repair

`RailRepair/Geometry.lean`, `Forest.lean`, and `Score.lean` formalize the
single terminal surgery described in the research note, including nonempty
alternating pockets at arbitrary width. The unconditional endpoint is
`GridGraphs.RailRepair.residueTwo_le_maxPreserved`, with L(k) as above.
The staircase remains valid historical infrastructure; L(k) supersedes its
score at odd k. The repair's six-width gain remains 12k+25, not 12k+26.

Completion gates:

1. Attempt the explicit Q-family above, allowing unrooted components if useful;
   if this class fails, return to b>=6 rather than declare the conjecture false.
2. Explicit coordinates for all sufficiently large k, with any omitted finite
   bases supplied separately; no interpolation from a few witnesses.
3. Exact cardinality and component/boundary accounting.
4. Uniform forced acyclicity or complementary dual connectivity, with actual
   grid attachments and no accidental cycles or reused physical connectors.
5. Lean construction and discharge of `RemainingMatchingDiagonalConstructions`.

## 7. Upper Track: Prove The Minimum

### Current Unconditional Upper Bound

The current stable residue-two bound, from `Accounting/EndpointUpper.lean`, is
`P(3k+2)<=T(k)+floor(2k/3)` for **all k>=5**, without b/c/r or coverage
premises. The public endpoints are `GridGraphs.forced_card_le_endpoint_refinement`
and `GridGraphs.maxPreserved_residueTwo_le_endpoint_refinement`. This improves
the previous BoundaryFive floor `(2k+1)/3` by one when k%3=1.
The three old endpoint exclusions are described in the active checkpoint above.

`GlobalUpperProfiles.lean` supplied the b>=6 bound and classified the old
k%3=2 endpoint as `(r,c,b)=(k+4,1,5)`. BoundaryFive now excludes it:
generic Near/Second holes locate the gap, square symmetry transports only size
and acyclicity, and the old profile is reapplied to the mapped set for b=5,c=1.
The oriented actual perimeter path and spokes force the nonpure singleton
`z=(2,2)`; `f+n<=(n-4)r+12` contradicts the endpoint. No canonical positions
for the other holes are assumed. At n=17, the former f=114 endpoint is impossible
and the global upper is 113. This is not an exclusion of all b=5,c=1 sets.
The second-short corner packet is now checked. The strict cap is checked under
`Rootless.UniqueBoundaryRoots`, not as a generic ambient b=5 n-5 cap or
`f<=(n-5)r+11` theorem; those broader claims do not follow from endpoint closure.
The following boundary-stratified result is an earlier milestone, still valid
over its broader range.

`Accounting/BoundaryStratifiedCarrierBound.lean` proves, for every n>=7,

```text
P(n) <= floor(n*(n*n+4*n-7)/(3*n+1)).
```

This improves the earlier numerator-minus-six carrier bound, which remains
available for n>=5. The new proof covers every feasible set, without assuming
that an optimum has b=5:

- If b>=6, the original carrier estimate and c>=1 already pay seven units.
- If b=5 and n>=10, the empty next ring separates induced preserved components
  into boundary carriers and deep carriers. The boundary contains exactly
  `4n-9` preserved vertices and needs at least four carriers; each deep carrier
  has length at most n-4. Consequently `|F|<=(n-4)*r+7`.
- Combining this refined length estimate with the ledger gives the stronger
  bound. The cases n=7,8,9 follow by arithmetic from the earlier estimate.

In residue two, that earlier milestone's checked polynomial form is

```text
P(3k+2) <= 3k^2+7k+floor((2k+3)/3),    k>=2.
```

There is no universal-waste assumption. The improvement does not change the
linear asymptotic coefficient of the earlier bound, and the sharp stable
target `3k^2+7k` remains open.

| Side | Proved lower | Proved upper |
|---:|---:|---:|
| 7 | 22 | 22 |
| 10 | 42 | 42 |
| 14 | 77 | 79 |
| 17 | 110 | 113 |
| 20 | 149 | 154 |
| 23 | 195 | 200 |
| 26 | 246 | 253 |
| 29 | 304 | 312 |
| 32 | 367 | 376 |

The current upper at side 35 is 447.

The current uniform repair gives the displayed lower bounds from side 17
onward. In particular 110 matches the existing finite lower witness at side
17, but **P(17) is not proved exact**: its current interval is [110,113].

The new equality at side 10 is `maxPreserved_ten_ten` in
`Results/SmallDiagonalExact/Ten.lean`, using the existing residue-one lower
construction. These examples specialize structural theorems; no grid searches
were run.

### Checked Counterexample Restrictions

`Accounting/ResidueTwoCounterexampleProfile.lean` proves that a feasible set on
side 3k+2 with `|F|>=3k^2+7k+excess`, k>=1 and excess>=1, must satisfy

```text
r >= k+2,
b+c+3*excess <= 2k+10.
```

Historically this gave b+c<=2k+7 for a stable counterexample and b+c<=2k+4
for a counterexample to the early target. The branch b+c>=2k+8 already satisfies the stable target.
For stable counterexamples with b=5, the refined geometry additionally proves
r>=k+3 and c<=2k+1. These narrow the open profiles; they do not prove that
those profiles are impossible.

For the current stable range k>=5, `AllCoveredCounterexamples.lean` strengthens
these to `r>=k+4` and `b+c+3*excess<=2k+8` whenever excess>=1 and
f>=T+excess. Such sets are all-covered with p>=4 and d>=k. In particular
b+c<=2k+5 above T, so b+c>=2k+6 suffices for f<=T. The older
GlobalUpperProfiles bound 2k+9 and broader-range APIs remain valid.

`Geometry/CarrierPacking.lean` independently proves the six-cycle obstruction
and the bound `length(C1)+length(C2)<=n+1` for wholly preserved horizontal
intervals two rows apart. The newer mixed packing controls nearby edge shadows
jointly in the enlarged nonpure strip; it is not an independent sum of all
such local carrier-length bounds for the all-covered problem.

`FourCarrier/Closure.lean` proves p=4 missing-side f<=T for every k>=5.
The physical image budget handles k>=6; at k=5, shallow preimages force a
second-position root and deep equality fills its radial axis, contradicting the
boundary six-cycle. ThreeCarrier.Closure now closes p=3 as well, and proves
f<=T with no p/W assumption. No missing-side proof obligations remain.

Next upper gates: all-covered lower-excess geometry for
`f=T+e, 1<=e<=floor(2k/3)`. The global bound is now T+floor(2k/3);
all three old k%3=1 endpoint profiles are excluded, not next targets.
Develop quantitative corner-packet, long-rod, and frame-budget losses without
assuming endpoint rooting or saturation throughout the remaining range.
[Paper Upper Program](PAPER_UPPER_PROGRAM.md) explains the actual enlarged-strip
and two-defect resolution; its old mixed/top program is historical and closed.
Use genuine joint capacity rather than the sufficient-only shadow certificate.
Next lower gate: make the terminal tail/cap improvement accumulate while retaining
an independent output and paying for all deletions and Delta b. Compatible seeds,
gain 12k+26, and uniform six-width closure remain required; the new paper family
still gains 12k+25 and supplies no pump.

### Sharp Upper Obligations

The direct targets are `B>=3k+9` for 1<=k<=4 and `B>=3k+12` for k>=5,
for every feasible F. The known lower witnesses then close the early range
and k=5,6; the lower track must close the remaining tail.

There are two live routes, with no predetermined winner:

**Direct interval geometry.** Contract maximal preserved intervals. Each U
connector joins at most two intervals, through opposite grid neighbors.
Retain physical connectors and any parallel edges when testing a candidate:
two connectors between the same intervals are already a cycle.

For an interval J, let N(J) be its neighbors in U and put `q(J)=|N(J)|-1`.
For a subfamily A define integer slack

```text
delta(A)=|union_(J in A) N(J)|-sum_(J in A) q(J).
```

For candidates with straight maximal components, feasibility is equivalent
to `delta(A)>=1` for every nonempty A. Equivalently, interval tokens admit a
matching after any one chosen U vertex is forbidden. The matching may depend
on that vertex. Tight overlapping families have an exact uncrossing rule.

These are forest sparsity identities, not the missing inequality. The actual
research gate is a grid-geometric argument forcing a deficient family at a
forbidden score, or a geometric classification of low-budget feasible sets.
In particular, the all-covered k=5 threshold still needs an explanation;
the missing-side k=5 case is already closed.

The new peeling theorem handles only b=5. Even a sharp Q bound would not
exclude better configurations with b>=6. No normal-form theorem putting an
optimum in b=5 is known; do not silently assume one.

**Global contour exchange.** Retain the existing occurrence-preserving
physical exchange route as an alternative. Prove the missing expansion,
instantiate `UniversalPrimalContourRouting`, obtain universal waste, and then
prove the two residue-two exclusions. Do not assume the disproved regional
first-ownership certificate or count repeated contacts as new resources.

A direct proof of the budget minimum can bypass this route. Conversely, a
valid contour proof need not be rewritten in interval language. More generic
Hall or routing interfaces without new grid geometry are not a milestone.

## 8. What Is Superseded

- The counter subdivision is no longer an active uniform realization candidate.
- Abstract target length plus an abstract tree is not an adequate lower gate.
- A fixed injective old-interval embedding is not a construction requirement.
- Connected incidence is not necessary for forced-set feasibility.
- The historical regional first-ownership theorem is false in general, not an
  unfinished lemma to assume or complete unchanged.
- Exhausted local grammars do not forbid nonlocal constructions, arbitrary
  other periods, or new arguments. Their counterexamples retain their stated
  scope; no global impossibility follows merely from accumulated failed searches.
- New paper deductions are not formal theorems until checked in Lean.

## 9. Laptop And Verification Rules

- Before extending a Lean file over 1,000 lines, split it into focused modules.
  Use sub-subfolders where helpful, preserve public theorem names, and keep
  new modules below that limit. Do not hide the old proof in an oversized helper.
- Address every project linter warning; do not silence linters to obtain a clean
  build. Verify changed modules and the full source set with warnings as errors.

The previous 2,420-line `Results/SmallDiagonalExact.lean` has been split into
`Three`, `BoundaryFive`, `LedgerFive`, `AttachmentFive`, `AttachmentCasesFive`,
and `Five` under `Results/SmallDiagonalExact/`. The largest is 708 lines. The
original entry module now aggregates these results and the `Seven` and `Ten` theorems;
all 17 prior public declaration names are preserved.

This work runs on a laptop with 32 GB RAM and a short interactive time budget.

- No new exact-grid optimization, exhaustive enumeration, SAT/SMT, or expanding
  state-product search above 15x15. Reuse existing larger results.
- Being at most 15x15 is not permission for a long run. A proposed search needs
  a precise falsification question, explicit time/memory caps, and approval.
- Prefer symbolic reasoning. No optimization was needed for the new deductions.
- Polynomial replay of an explicit witness is different from finding an
  optimum. Keep even those checks short and purpose-specific. Finite replay
  is debugging evidence, not an arbitrary-width proof.
- Do not add another solver or generic proof framework without a concrete need.
- Preserve concurrent worktree changes. Do not infer verification from a clean
  file or an old status document.
- User authorization overrides the previous full-build time cap: project-library
  verification may run in the background without a time limit. Keep its log and
  exit status observable, reuse mathlib caches, and avoid competing full builds.

During formal development, run the affected module from `lean/`:

```bash
lake env lean GridGraphs/NewModule.lean
```

Before reporting a formal milestone, run `lake build` from `lean/` and
`git diff --check` from the repository root. Audit new proofs for `sorry`,
`admit`, additional axioms, and computational proof dependencies. Report any
build or resource blocker explicitly. Documentation-only updates do not require
a full Lean build and must not be reported as one.

## 10. Minimal Navigation

| File | Role |
|---|---|
| `docs/HANDOFF_U1_U3_L2.md` | EndpointUpper closure, unchanged missing-side/lower results, verification, remaining lower-excess goals |
| `docs/L2_FIXED_RAIL_POCKET.md` | Paper-only obstruction with frame and rails fixed |
| `docs/L2_RAIL_REPAIR_RESEARCH.md` | Now-formal terminal repair, historical finite searches, and scoped propagation obstruction |
| `docs/L2_PROPAGATING_INTERFACE.md` | Separate paper alternative with unsuccessful actual target gain |
| `docs/L2_TWO_RAIL_INTERFACE.md` | Two-rail/notch restricted searches, independent outputs, count-neutral continuation, and remaining tail/frame gate |
| `docs/L2_TERMINAL_TAIL_INTERFACE.md` | 76-center n14 rootless output, scoped search cutoff, paper tail/cap family without accumulating gain |
| `docs/PAPER_UPPER_PROGRAM.md` | Closed endpoint and missing-side proofs, guardrails, and quantitative all-covered lower-excess program |
| `lean/GridGraphs/Accounting/EndpointUpper.lean` | Current global `T+floor(2k/3)`, every k>=5, no b/c/r/coverage premises |
| `lean/GridGraphs/Accounting/BoundaryFive/Upper.lean` | Previous global `T+floor((2k+1)/3)` via the old k%3=2 endpoint singleton contradiction |
| `lean/GridGraphs/Accounting/CarrierLayers/FourCarrier/Closure.lean` | Prior full p=4 missing-side closure including k=5; historical p=3 reduction now has impossible counterexample premises |
| `lean/GridGraphs/Accounting/CarrierLayers/ThreeCarrier/Closure.lean` | Entire missing-side f<=T, k>=5, no p/W assumptions; every stable counterexample all-covered |
| `lean/GridGraphs/Accounting/CarrierLayers/Annulus/Cap.lean` | Global B+E<=4n-9, K>=5, cubic ledger and annulus component budget |
| `lean/GridGraphs/Accounting/CarrierLayers/Annulus/Bridges.lean` | Literal full-rod edge packets give M+1<=cA, including isolates, without a quotient-forest assumption |
| `lean/GridGraphs/Accounting/CarrierLayers/Annulus/Deficit.lean` | Total deep deficit gives r+5<=2K+D |
| `lean/GridGraphs/Accounting/CarrierLayers/Annulus/Counterexamples.lean` | Global d>=k in stable counterexamples |
| `lean/GridGraphs/Accounting/CarrierLayers/Annulus/Upper.lean` | b>=7 upper T+floor(2k/3); old k%3=1 necessary profiles now all excluded |
| `lean/GridGraphs/Accounting/CarrierLayers/AllCoveredCounterexamples.lean` | Global p>=4, r>=k+4 and b+c+3e<=2k+8 for every positive excess |
| `lean/GridGraphs/Accounting/CarrierLayers/GapGlobalCapacity.lean` | Once-per-shallow-carrier deep-capacity loss and h<=a |
| `lean/GridGraphs/Accounting/CarrierLayers/GapGlobalExclusion.lean` | Shared inward carriers and initial connected minimal-induced exclusion |
| `lean/GridGraphs/Accounting/CarrierLayers/GapGlobalMinimal.lean` | Boundary-image partition and entire p=3, r=k+2 exclusion for any c |
| `lean/GridGraphs/Accounting/CarrierLayers/CoveredGlobalMissingSides.lean` | Global k>=5 coverage, p>=3, and r>=k+3 |
| `lean/GridGraphs/Accounting/CarrierLayers/GlobalUpperProfiles.lean` | Improved counterbudget, b>=6 bound, and historical old-endpoint profile now excluded by BoundaryFive |
| `lean/GridGraphs/Accounting/CarrierLayers/ConcentratedGaps.lean` | Scoped root-free gap bound and local two-row capacity loss |
| `lean/GridGraphs/Accounting/CarrierLayers/CoveredDeficit.lean` | Actual shadow union, carrier-length shortfall, and sufficient-only certificate |
| `lean/GridGraphs/Constructions/ResidueTwo/RailRepair/Score.lean` | Current uniform formal lower bound and insufficient six-width gain |
| `lean/GridGraphs/Accounting/CarrierLayers/OneExcessSeparated.lean` | Root-separated hole charge without saturation; conditional sharp bound |
| `lean/GridGraphs/Accounting/CarrierLayers/CoveredBoundary.lean` | Actual pure mass and shared physical boundary budgets |
| `lean/GridGraphs/Accounting/CarrierLayers/MissingSideSharp.lean` | Uniform missing-side bound and four distinct side-covering pure carriers |
| `lean/GridGraphs/Accounting/CarrierLayers/RadialOneExcess.lean` | Exact one-excess slack and saturation-only isolate bounds |
| `analysis/RESIDUE_TWO_COMPONENT_BUDGET.md` | New paper proofs, exact qualifications, analytic gates |
| `analysis/BOUNDARY_FIVE_PEELING.md` | Exact paper reduction to an inner boundary-rooted forest |
| `lean/GridGraphs/Accounting/BoundaryFiveBudget.lean` | Checked boundary bound and target component obstructions |
| `lean/GridGraphs/Accounting/BoundaryFiveEquality.lean` | Checked equality geometry, unique gap, and next-ring exclusion |
| `lean/GridGraphs/Accounting/CarrierLengthBound.lean` | Unconditional square upper bound from component lengths |
| `lean/GridGraphs/Accounting/BoundaryStratifiedCarrierBound.lean` | Stronger all-configuration upper bound using the b=5/b>=6 split |
| `lean/GridGraphs/Accounting/ResidueTwoCounterexampleProfile.lean` | Necessary low-budget profiles and the solved high-budget branch |
| `lean/GridGraphs/Geometry/CarrierPacking.lean` | Six-cycle and two-row interval-overlap restrictions |
| `lean/GridGraphs/Constructions/BoundaryFive/BoundaryFiveFrame.lean` | Actual canonical frame, support tree, and spokes |
| `lean/GridGraphs/Constructions/BoundaryFive/BoundaryFiveAttachment.lean` | Exact canonical inner-attachment iff |
| `lean/GridGraphs/Constructions/BoundaryFive/BoundaryFiveConstruction.lean` | Counted concrete extension and lower-bound transfer |
| `lean/GridGraphs/Constructions/ResidueTwo/ResidueTwoStaircase.lean` | Improved family's coordinates, placement, and exact count |
| `lean/GridGraphs/Constructions/ResidueTwo/ResidueTwoStaircaseForest.lean` | Improved family's support geometry and unconditional lower bound |
| `lean/GridGraphs/Core/ForcedMaximum.lean` | Exact optimization equivalence |
| `lean/GridGraphs/Accounting/ComponentReduction.lean` | Existing exact ledger |
| `lean/GridGraphs/Results/SmallDiagonalExact.lean` | Aggregate for modular exact 3x3, 5x5, 7x7, and 10x10 proofs |
| `lean/GridGraphs/Constructions/ResidueTwo/ResidueTwoAffineMax.lean` | Uniform near-target lower bound and exact deficit |
| `lean/GridGraphs/Constructions/IntervalStarGluing.lean` | Reusable lower-bound acyclicity interface |
| `lean/GridGraphs/Routing/UniversalPrimalContourRouting.lean` | Alternative upper-bound endpoint |
| `lean/GridGraphs/Results/DiagonalUpperResidue.lean` | Precise open upper hypotheses and adapters |
| `lean/GridGraphs/Results/DiagonalFormula.lean` | Remaining construction obligation and conditional assembly |
| `lean/STATUS.md`, `lean/EVIDENCE.md` | Detailed source/evidence indexes, not substitutes for fresh verification |

Start with these files. Consult historical notes only when their specific
construction, obstruction, or interface becomes relevant; do not survey the
entire experiment collection.
