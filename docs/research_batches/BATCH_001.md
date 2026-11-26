# Batch 001 — Boundary coupling to original-resource payment

Started 2026-09-14. Three-cycle autonomous batch. Success criterion:
a uniform non-reusing payment for an uncovered interface subclass, with
the complement explicitly stated. No local result is global closure.

## Cycle 1: foundations and hypothesis selection

An independent reviewer checked the repair/separator proofs; central
arguments survived. Clarifications: finite ambient graph, cycle rank
with loops and multiplicity, physical edge provenance, and terminal
labels frozen during refilling but changed at the final promotion.

A separate adviser selected the pendant-root depth-three front in
`PAPER_MAXIMUM_CLEAN_UPPER.md`. Its gap extensions are cyclic, but
coupled boundary deletions may compensate. Promotions add multiple new
edges, so one-edge graphic rank is not a promotion-count formula here.

The geometry suggested a stronger direction: private isolates needed for
the exchange already pay the original bank demand. Direct payment avoids
a needless maximum-normalization/root assumption.

## Cycle 2: protocol fixed before execution

Reconstruct the source's side14 pendant-root witness, checking
(f,r,b,c)=(46,7,36,71). Test the three marked-row exchanges simultaneously
as a positive control. Enumerate every extension in a near-front 5x5
patch, retaining the skeleton, and test the guarded middle row on every
feasible extension. Also construct a side15 four-rail fixture with two
guarded interior levels, checking genuinely simultaneous changes.
The side15 fixture tests local geometry, not the residue-two allocation.

Record exact patch coordinates before running. Independently audit graph
feasibility and all ledger changes. No heuristic cutoffs, unrecorded failed
cases, or optimization above side15. Finite success does not prove the
arbitrary-size assertion.

Fixed executable protocol: source-rooted14 middle patch [9,13]x[5,9]
(17 optional labels); rooted14 and rootless14 cap patch [8,12]x[10,13]
(16 each); rooted15 cap patch [9,13]x[10,14] (17). Mandatory source F
labels and the stopped endpoint U labels remain fixed. Total 393,216
subsets. Selected guarded rows are {7} in the 14-squares and {4,7} in
the 15-square. The latter is a two-level simultaneous test. Actual rootless
teeth belong to three distinct H components. All-row unguarded endpoints
are used only in the original side14 positive control, not the uniform claim.

## Cycle 3: uniform proof and payment gate

Prove/refute H002 and H003, commission final independent mathematical
review, and reconcile resource ownership. Candidate direct payment:
D_B<=|Z_B|+2 without root connectivity. Combine with exposed payments
only after proving nonreuse. Stop the exchange-only branch if it gives
no original-resource payment.

Outcome: **completed**, including the stronger spine-free refinement below.
See the final decision and review record at the end of this report.

### Cycle-3 refinement and its pre-run falsification protocol

The original isolate proof extends to EVERY off-level between rails:
all neighbours of u=(A-2,y) except s=(A-1,y) are U. Either s is U and
u is isolated, or s is F and the boundary vertex (A,y+1) must be U.
The injective map y->y+1 supplies a boundary deficiency unit. Thus a
stopped bank has 2a original isolate/hole coupons WITHOUT a boundary
spine and WITHOUT roots. Candidate H005: zero-error direct payment.

Before accepting this stronger statement, enumerate arbitrary labels in
the two outside columns of two residue-two fixtures: n11, rail levels
{2,5,8}, exterior rows1..9 (18 variables); n14, levels{4,7,10,13}, exterior
rows4..13 (20 variables). Rails occupy x=0..A-3, all other nonvariable
vertices are U. Total1,310,720 subsets. The n14 fixture exercises a corner
deficiency unit. These are exact tests of the same cycle-3 payment target,
not a fourth autonomous research cycle. Independently review the new
same-side/cross-side resource ownership before combining with old payment.

## Batch decision report

### What was proved

1. **H002, reviewed:** a simultaneous neutral boundary exchange on guarded
   depth-three fronts, with exact changes (Delta r,Delta b,Delta c,Delta z)
   =(t,t,-2t,-2t), valid with arbitrary actual root identities.
2. **H003, reviewed:** private original isolates pay a whole guarded bank
   up to two units, without root connectivity. This was an intermediate
   payment, subsequently strengthened.
3. **H005, reviewed:** a whole stopped depth-three bank needs neither a
   preserved boundary spine nor common roots. Its2a_B off-level positions
   provide2a_B distinct original isolate/boundary-hole units, paying its
   full rectangle demand with ZERO additive error. The invoices are
   non-reusing across banks and across all four sides, including corners.

The strongest statement combines with the old exposed-bank payment:

    sum_(exposed or stopped) D_B <= R_av+6N_exposed.

See `../PAPER_STOPPED_FRONT_PAYMENT.md` for hypotheses and full proof.

### Which global obligation became smaller

Entire banks uniformly stopped at depth three now require no common-root
localization and no boundary normalization. Their height-weighted demand
is paid directly at coefficient2a_B. Only the exposed banks contribute
the inherited constant error. This is a genuine additional covered class
in the existing sufficient comparison, not merely a new safe move.

Global coverage remains open: mixed stopped/extended levels, varying
depths and incomplete front runs are not covered. The reviewed global
upper is still T+floor(k/2)+1. No lower construction or Lean bound changed.

### Exact checks

| Experiment | Masks independently enumerated in both languages | Feasible |
| --- | ---: | ---: |
| Guarded exchange extensions | 393,216 | 208 |
| Spine-free two-column exteriors | 1,310,720 | 26,089 |
| Total | 1,703,936 | 26,297 |

The second study includes4,461 corner-hole cases and invoices ranging
from entirely isolates to entirely boundary holes. There are no cutoffs.
These are complete specified fixtures, not exhaustive global geometry.

Both release audit binaries built and ran successfully. Final library
tests:49 passed, one pre-existing expensive test ignored. The new Python
regression test passed. Rustfmt initially requested formatting of the new
audit binaries; formatting was applied and checks then passed. Whitespace
checks passed. No Lean build or optimization above side15 ran.

### Independent review and corrections

`BATCH_001_REVIEWS.md` records the scopes. A separate final mathematical
reviewer checked both new written proofs and their allocation dependencies.
The guarded note needed an explicit WIDE-bank restriction before applying
the thirteen-bank count; this was corrected and rechecked. The stronger
stopped-front note passed full independent review without mathematical
findings. Computational audits were separately implemented and executed.

### Branch decisions

* **Continue direct payment:** H005 removes the need to find neutral
  normalization in this class.
* **Park exchange-only exploration:** H002 is useful structure, but its
  post-surgery coupons are not extra payment. No sampler campaign follows.
* **Reject rank-as-money:** the tested promotion bundles add multiple edges;
  rank alone neither counts gained F labels nor prices metric displacement.
* **Keep the construction counterprogram:** H002 is not a pump, since it
  preserves f and consumes original isolates. No renewable extension was
  constructed in this batch. Reserve the third cycle of batch002 for H004.

### Next three cycles (batch002, not yet executed)

1. **Mixed marked levels:** retain the common depth-three back FF edge,
   but allow both U and F at the depth-two endpoint. Derive an exact
   invoice for the surviving stopped contributions and identify the
   unpaid extended contributions with actual root/port data. H005 and
   the rooted exposed theorem are endpoint cases, not a proof of the mix.
2. **Uniform mixed payment or counterexample:** test complete small
   interfaces and seek a one-account rule for those unpaid contributions.
   Stop if it merely introduces a constant error per unbounded run/root.
   An actual counterexample must state whether it satisfies proposed
   low-K or maximum-specific hypotheses.
3. **Renewal falsification:** revisit one moving-phase/cap extension with
   explicit physical interface renewal, exact net count and closure cost.
   Require symbolic all-size feasibility for any asymptotic claim. Bounded
   searches remain within15; no n11->n17 optimization. Review both routes
   and issue the next batch decision.

No resource-limit or objective change is requested. Pause here for the
authorized three-cycle checkpoint.

## Artifacts and reproduction

SHA256:

* `data/guarded_fronts_batch001.json`:
  `4d75f5b3eeaab8b81bdbcca073148e20debfa9d8a4107ae82c898e4ded8b88c4`
* `data/guarded_fronts_batch001.rust_audit.json`:
  `966089a5f7f2b7c608b00b36eefc02e18f3c778726b812f8fb242e5e508e0082`
* `data/stopped_fronts_batch001.json`:
  `e0cb7691cf5642e0d89adcea5ff0c1b8b7e11e0793b98446051fa21cbbf6f639`
* `data/stopped_fronts_batch001.rust_audit.json`:
  `0ae48ba1ffc3693cbf5dec10515609633a74e47cc2866cdfa6cca81d3518b848`

Fresh output paths are required:

```bash
python3 -m analysis.research_program.guarded_fronts /tmp/opencode/guarded.json
python3 -m analysis.research_program.stopped_fronts /tmp/opencode/stopped.json
CARGO_BUILD_JOBS=2 cargo build --release --bin audit_guarded_fronts --bin audit_stopped_fronts
target/release/audit_guarded_fronts /tmp/opencode/guarded.json /tmp/opencode/guarded.audit.json
target/release/audit_stopped_fronts /tmp/opencode/stopped.json /tmp/opencode/stopped.audit.json
```
