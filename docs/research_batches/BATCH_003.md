# Batch003 — Bilateral payment and literal renewal

Started2026-09-15 under the three-cycle autonomous charter. Inspect only
repository files; no installed-package/cache/registry inspection.

## Cycle1: fixed bilateral target

On every transverse level of one ACTUAL bank, require a filled central
carrier interval[3,A-3], A=n-1. Its P endpoints at2,A-2 may be F or U.
This common interval is an additional geometric hypothesis, not a
consequence of a bank's bounding width. No common root across levels
is assumed. For the global allocation use n=3k+2>=11 and all bank levels.

Retain the three columns at each side, locally named(P,S,boundary), and
replace each marked actual central path by one edge P_left--P_right.
There is no persistent root. Off-level central supports are pendant;
P is forced U on both sides. Omit arbitrary caps for a necessary-condition
forest relaxation, keeping the joint six-vertex frontier partition.

Charge both sides' hole/pure-carrier/isolate/singleton/dimer-bank-start
resources from batch002, but subtract ONE demand per off-row (2a total).
Use four dimer-history bits. The question is whether an integer potential
exists without any extra component-closure coupons. If it fails, extract
and realize the obstruction before charging forgotten components as c.

## Cycle2: certificate and ownership gate

Generate all reachable states/transitions, then independently regenerate
the graph and verify any potential or negative cycle. Computational
guards:20,000 states,1,000,000 edges; potential search180 seconds. A limit
is inconclusive, not a negative theorem. Strip width is six; no large-board
optimization is implied by a symbolic arbitrary-length certificate.

If a potential exists, account for at most eight boundary dimer chains,
at most two omitted bank levels, and TWO side-window incidences per bank.
Establish global nonreuse separately. If component-closure resources are
needed, certify global closure and cap ownership first.

## Cycle3: actual nested compatibility

Under a(+3,+3) embedding, the whole old board becomes frozen in the next
moving-phase-core class. Derive the forced crop Q_k symbolically, compare
it with near-target seeds, and prove or refute bounded-edit renewal.

Use only n8 andn14 materializations. At n8 test every pair of allowed
old-annulus holes in Q_2:38 candidates,703 pairs, not all41 U positions
(three are old deep fixed U). If a25-center superset exists, delete its
two extra labels and compose with the recorded75 n14 annulus. Check the
actual central crop, not only scores. Also exhaust every compatible
superset of Q_2,Q_4 after the sound single-promotion eligibility filter,
provided the eligible pool has at most20 vertices; otherwise report a
cutoff. No n20 board is constructed or optimized.

Status: all three cycles completed. Results and the next decisions follow.

## Final batch decision

### Cycle1/2: reviewed bilateral payment

The six-column graph completed without hitting its state/edge/time guards:
2,424 states,22,508 edges, potential range[-3,0], endpoint error2.
It requires neither a persistent common root nor any coupon for a component
that disappears behind the frontier. The actual central carrier paths
join the two side interfaces separately on each marked level.

After accounting for eight possible boundary supplier chains, omitted
nonregular levels and TWO side-window incidences, a bilateral bank has
local allowance14 and simultaneous coefficient16. For disjoint selected
wide-bank classes E(exposed),S(stopped),M(rooted mixed),B(bilateral):

    sum D_selected <= R_used+6N_e+11N_m+16N_b,
    R_used <= R_av.

Independent mathematical review accepted the proof and requested clear
suppression order, the correct one-spanning-carrier-per-level scope, and
same-side versus cross-side ownership wording. All were corrected and
rechecked. An explicit n11 three-rail example satisfies the bilateral
condition but neither one-sided exposed/mixed root condition, so the
coverage extension is genuine.

The common-central-interval hypothesis is still substantial. Width alone
does not imply it. The remaining signed bank debt must be paid from
R_av-R_used; the at-most208 selected-payment error does not close that gap.
Full proof: `../PAPER_BILATERAL_FRONT_PAYMENT.md`.

### Cycle3: uniform renewal obstruction and a verified finite step

Under a(+3,+3) enlargement, every old vertex becomes frozen. Its forced
crop is Q_k with

    |Q_k|=3k²+5k+1=T(k)-(2k-1).

The Q_k are actual feasible nested forests, but their six-width increment
is12k+22, four below target. Literal nesting therefore cannot yield a
constant-gap family in these classes. More generally, a T(k)-C seed must
undergo at least2k-1-C net old-label deletions before the new frame is
attached. A uniformly bounded NUMBER of old edits is impossible; a fixed-
width band containing O(k) edits remains allowed.

Exact finite tests give:

| n | Forced crop F | Allowed old-band holes | Eligible additions | Exact maximum forest superset |
| --- | ---: | ---: | --- | ---: |
| 8 | 23 | 38 | two opposite corners | 25 |
| 14 | 69 | 86 | two opposite corners | 71 |

All703 n8 pairs were tested; exactly the corner pair gives25. There is
a real minimum-old-rewrite gap-one step:

    seed25 -> delete2 -> Q_2(23) -> embed -> add52 -> final75.

Both implementations verified all56 stages. The frame's apparent52-center
gain is offset by the two old deletions, leaving the required net50.
This template cannot continue by deleting extras only: no feasible75
n14 seed in the old frozen-core class contains Q_4. The recorded75 seed
needs18 deletions and12 additions to become Q_4 (not claimed minimal over
other seeds). Full proof/scope: `../PAPER_NESTED_RENEWAL_OBSTRUCTION.md`.

The finite superset upper exclusions have120 explicit simple-cycle
certificates, independent of the earlier SAT UNSAT result. No n20 board
was materialized or optimized. A general O(k)-rewrite annulus construction
and the global constant-gap lower remain open.

### What became smaller

* Common-root localization is no longer needed for whole banks with the
  stated central interval on every level; the two physical fronts pay
  jointly with original resources.
* Literal and bounded-cardinality nesting of the current frozen-core
  family are ruled out uniformly. Future renewal work must track actual
  band rewrites and attain annular count14k-3-C, not extrapolate scores.

No unconditional upper/lower bound or Lean result changed. The reviewed
upper remains T+floor(k/2)+1.

### Branch decisions and next three cycles (batch004, not started)

1. **Global residual bridge:** prioritize the unselected-bank term
   sum[3X_B/A-(v_B-q_B)] against R_av-R_used. Formulate a scale-aware
   gluing/transport statement for a genuinely uncovered variable-depth
   or incomplete front. Retain the artificial2L cut price and the actual
   height weights. Do not merely add another fixed-depth certificate.
2. **Falsify or prove that bridge:** choose exact bounded interfaces that
   test its missing implication, then review both geometry and ownership.
   A new subclass is not enough unless its complement is explicitly paid
   or normalized. Any use of low K must be symbolic; absence of small
   low-K witnesses is not an asymptotic argument.
3. **Rewrite-band renewal:** derive the actual core-boundary component
   signature for coordinated O(k) edits and a candidate annulus rule.
   The required asymptotic annular rate is14 F per increment of k, with
   bounded cap loss. First justify any finite-state renewal signature,
   including contacts to U core-boundary vertices; then test one rule.

Park literal/bounded-edit renewal and further exchange-only polishing.
Retain the successful finite step as a compatibility control, not a pump.
Pause at this agreed three-cycle checkpoint; no limit change is requested.

## Verification and provenance

`BATCH_003_REVIEWS.md` records the independent reviews and corrected scope
findings. The bilateral graph was independently regenerated via adjacency
components, checking155,136 candidate transitions,22,508 accepted edges,
292,604 charge terms and44,160 initial/terminal bound pairs.

All1,048,576 physical n11 assignments were checked against full primal
traversal, direct suppression and frontier acceptance;36,608 were feasible.
The independent nested audit checked124 singleton promotions,120 rejection
cycles,703 pairs,8 eligible-pool subsets and56 composition stages.

Final validation:49 library tests passed, one pre-existing expensive test
ignored;12 Python research-program tests passed. Both new Rust audit
binaries built and ran, and their test targets compiled. Formatting and
whitespace checks passed. No package/cache/registry inspection or
optimization above15 was performed.

SHA256:

* `data/bilateral_fronts_batch003.json`:
  `5c96dce052e4e2f0b8060824f49f4230fc15df26c4f0b756c3b3550cd712deb2`
* `data/bilateral_fronts_batch003.rust_audit.json`:
  `ecee79c1d68fbf19706ef2fcdfa99e80b0e19aea040c205ea91e7ee79f5574db`
* `data/nested_renewal_batch003_cycle3.json`:
  `81c8c8fc9c9ecf15d90e0aa5e0fd9ee9cf9a385275efec91def1a2d47c9b711d`
* `data/nested_renewal_batch003_cycle3.rust_audit.json`:
  `3049bde537f07f68bb6ab920e690305a1260c21f5e22cc7e17ce5ea5925829eb`

The nested primary artifact records its source hashes and uses F/U display
rows with explicit center IDs. All native checks reconstruct actual boards
from those IDs. Source/outputs are kept separate; no frozen output was
overwritten.

Reproduction requires fresh repository-local outputs:

```bash
python3 -m analysis.research_program.bilateral_fronts data/bilateral_reproduction.json
target/release/audit_bilateral_fronts data/bilateral_reproduction.json data/bilateral_reproduction.audit.json
python3 -B -m analysis.research_program.nested_renewal --output data/nested_reproduction.json
```

The nested Rust auditor is intentionally tied to the frozen batch003
artifact and its named prior inputs; invoke it with a fresh `--output`.
