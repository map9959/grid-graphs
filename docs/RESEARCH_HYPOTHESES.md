# Live research hypothesis register

## Hypotheses and current status

### H001 — Repair foundations

Finite multigraph partition coarsening costs at most 2q optional F labels
when the coarse baseline is a forest. The exact maximized penalty is
|X|-2rho(X). Clearing a free core that separates tree terminals admits a
separator deleting at most two F labels.

Status: independent mathematical review found central proofs sound;
finite-board/rank and frozen-label wording clarified in this batch.

### H002 — Neutral depth-three exposure

Against a full boundary spine, extend stopped three-spaced rails at
guarded interior levels while deleting the opposite boundary F vertices.
Two private isolates per level make the exchange neutral and simultaneous,
with (Delta r,Delta b,Delta c,Delta z)=(t,t,-2t,-2t).

Status: REVIEWED PAPER PROOF, `PAPER_GUARDED_FRONT_PAYMENT.md` Lemma2.
Complete finite tests and independent Rust audit:393,216 masks,208 feasible
extensions, all five deltas checked. Root connectivity is required only
for rooted exposure afterward, not exchange safety. This is not a pump.

### H003 — Direct unrooted guarded-bank payment

If EVERY level of an actual positive-height bank ends at depth three with
the specified back FF edge and a full opposing boundary spine, its full
rectangle demand D_B is paid by 2(a_B-1) original isolates plus two units.
Guarded witnesses are disjoint across selected banks and from existing
exposed-window depth-one witnesses. Combine with the direct-K account.

Status: REVIEWED PAPER PROOF, superseded for direct payment by H005.
Removes root connectivity for this subclass; the neutral-surgery result
remains useful under its guards. The existing low-K reduction, not
experiments, supplies thirteen WIDE banks.

### H004 — Renewable construction

Find an actual renewable k->k+2 extension with controlled caps and gain
12k+26 (lower route) or 12k+27 (falsification). Status: open. H002 preserves
score and consumes two isolates per level; it is not a pump. Batch002
established the stronger rank-neutrality obstruction and the restricted
annulus result H008. Batch003 resolved literal/bounded-edit nesting and
one finite C=1 step through H010. A construction allowing coordinated
O(k) annular rewriting remains open under H012.

### H005 — Spine-free stopped-front payment

Every level of an actual positive-height bank has back FF at depth three
and its depth-two endpoint is U. Arbitrary outer labels and roots allowed.
Every off-level supplies either an original global isolate or a distinct
side-labelled boundary-hole unit. There are2a_B units, paying D_B with
ZERO additive error. Stopped invoices are mutually non-reusing and do not
reuse the existing exposed-bank invoices.

Status: REVIEWED PAPER PROOF, `PAPER_STOPPED_FRONT_PAYMENT.md`.
Independent Python/Rust complete test:1,310,720 masks,26,089 feasible
exteriors;4,461 corner-hole cases. Mixed wide-bank allocation:

    sum_(exposed or stopped) D_B <= R_av+6N_exposed.

Theorem covers whole stopped fronts, not mixed stopped/extended levels,
variable depths, or incomplete front runs. No global coverage is inferred.

### H006 — Mixed depth-two/depth-three whole fronts

Status: REVIEWED PAPER PROOF under actual common-root connectivity behind
the back FF cut; `PAPER_MIXED_FRONT_PAYMENT.md`. The original invoice was
refuted by H007. The revised104-state/300-edge certificate charges actual
S-singletons and one protected unit per interior whole supplier-dimer bank.
Full-bank allowance10; simultaneous mixed/exposed deduplication gives

    sum_(E union S union M)D_B <= R_av+6N_e+11N_m.

Root localization, unrooted mixed fronts and variable depths remain open.

### H007 — Restricted mixed invoice (refuted)

Claim: boundary holes, two depths of isolates and pure boundary carriers
pay arbitrary rooted mixed fronts with O(1) error. REFUTED by the actual
n=9L+5 family with marked P-word F,F,U. Its actual main-bank demand minus
that window invoice is L-3-42L/A. There are no singleton F carriers;
adding only r_1 therefore also fails. The missing units belong to protected
nonpure supplier banks. K=45L+27>n: not a global low-K counterexample.

### H008 — Frozen-core renewal annulus

Recorded restricted exact solver result M_3(4)=75: verified75 witness,
solver UNSAT at76 with no independently checked UNSAT proof trace. At
k=2 a26 witness exists. The numerical optimal-deficit step worsens;
no nesting or renewable construction follows from separate SAT witnesses.
Guarded pendant exchanges preserve beta under full-graph local conditions,
so they alone cannot remove the old cap's k+1 cycles.

### H009 — Two-sided payment without a common root

Status: REVIEWED PAPER PROOF for banks having one carrier containing
[3,A-3] on EVERY level; extra fragments permitted. No common root is
needed. A2,424-state/22,508-edge certificate has endpoint loss2. After
supplier-chain endpoints and whole-bank allowance, the local error is14;
two side-window incidences give simultaneous coefficient16 per bilateral
bank. Full width alone does not imply the common-interval hypothesis.
See `PAPER_BILATERAL_FRONT_PAYMENT.md`.

### H010 — Literal or bounded-edit renewal of the frozen cores

REFUTED by a REVIEWED uniform crop/count argument. The required old-board
pattern is Q_k with3k²+5k+1=T(k)-(2k-1) centers. Literal nested chains
gain12k+22, not12k+26. A T-C seed must undergo at least2k-1-C net old-
label deletions. A fixed-width band with O(k) edits is not excluded.

Finite cycle certificates show that allowed forest supersets of Q_2 and
Q_4 have exact maxima25 and71, respectively. The unique n8 gap-one
superset adds the two corners. Deleting those corners and attaching the
recorded n14 annulus gives a genuine25->75 step, but a75 n14 seed cannot
contain Q_4, so the delete-extras-only template cannot continue.
See `PAPER_NESTED_RENEWAL_OBSTRUCTION.md`.

### H011 — Scale-aware payment of the uncovered residual

OPEN. Current paid classes leave unselected wide banks with signed actual
debt sum[3X_B/A-(v_B-q_B)], to be compared with R_av-R_used. The next
target must tie varying front depth/common-interval failure to this actual
debt and retained resources. Another fixed-depth subclass alone is not
sufficient; preserve artificial cut cost2L and height weights.

### H012 — Annular rewrites with growing edit count

OPEN. In the current frozen-core class, a gap-C filling requires14k-3-C
annular F vertices. Seek a uniform rewrite/attachment rule meeting this
rate with bounded cap loss, allowing O(k) old-band changes. First derive
the actual core-boundary component signature; separate SAT witnesses or
the52-center frame of the first step are not a renewable invariant.
