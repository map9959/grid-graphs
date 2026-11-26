# Batch002 — Mixed fronts and renewal rank

Started 2026-09-14; three cycles authorized after batch001 checkpoint.

## Cycle1: fixed mixed-front target

Every level y_j=y0+3j has back FF(A-4,y_j),(A-3,y_j); the depth-two
vertex p_j=(A-2,y_j) is now either F or U. For a whole-bank payment,
these must exhaust the actual bank's levels. Let epsilon_j indicate F.
The stopped invoice survives at exactly

    2a-m,  m=epsilon_0+epsilon_a+2 sum_(0<j<a)epsilon_j

off-levels. The problem is payment of m, not the already-paid remainder.
For the first uniform target assume the displayed q_j=(A-3,y_j) have
one ACTUAL common component in H[x<=A-3]. This is a scoped hypothesis,
not a conclusion of low K or bank membership.

Test a three-column frontier automaton with that persistent root. It
retains row labels and actual frontier partitions, permits closed
components, and rejects every genuine forced cycle. Unlike the old
marked-boundary-F shortcut, it includes attachments with p U and s F.

Charge resources jointly rather than counting a stopped hole twice:
all boundary holes once, actual depth-two and depth-one off-level
isolates, and pure boundary F-run starts. Subtract one demand unit per
off-level row. Seek a bounded potential on the complete reachable graph.
Initial/final marked rows and regular-window guards determine the endpoint
constant; no potential reset at changes of epsilon is allowed.

## Cycle2: certificate and nonreuse gate

Construct the exact finite graph, search for a negative cycle or a
potential, and independently regenerate/check it. Then review the
geometric soundness and cross-bank resource ownership. A positive
certificate proves only the common-root mixed-front class. A negative
cycle is initially only an obstruction to the relaxed certificate;
grid realization is a separate obligation.

## Cycle3: construction/cap test

Investigate the stronger rank-neutrality of guarded pendant surgery:
when its full-graph leaf/isolate hypotheses hold, Delta E=2t and
Delta c=-2t, hence Delta beta=0, even on an initially cyclic graph.
The conditions must be verified directly there, not deduced from forest
feasibility. Such moves alone cannot remove a k+1 cap rank.

Also test a broader repair family: arbitrary changes on ALL four sides
to depth two, fixing exactly the moving-phase F core at depth>=3 and
fixing every other deep vertex U. Instances n8 andn14 only, threshold
f>=T (26 and76), at most60 seconds and10,000 SAT/cycle-separation rounds
per instance. The exact SAT edge model has e_uv iff(F_u orF_v), and each
discovered actual cycle is excluded by a sound cycle-edge clause.
Timeout/round limit is inconclusive; solver UNSAT is restricted and has
no independently checked proof trace. Every claimed witness is independently
replayed. No optimization above15 or inferred asymptotic pump.

The geometry adviser initially misstated the n14 frozen count as27;
coordinate counting and tests corrected it to23 BEFORE execution.
The annulus therefore needs53 centers at n14, not49. The n8 core has1
center and needs25 annular centers.

Batch status: **completed**; results, reviews and the next checkpoint plan
are recorded below. Batch003 has not started.

### Cycle2 revision, fixed before supplier-certificate computation

The original59-state/171-edge graph has a negative cycle with row word
`1,4,4,5,4,4,0,6,0` (bitsP,S,boundary), weight-1 per nine rows. A
physical common-root realization was derived. The missing resource is
an off-level horizontal FF dimer, not a singleton; adding only r_1 cannot
fix this cycle. Its separate bank has a retained Q_roots unit.

Revise the graph to charge actual S-singletons and ONE unit per maximal
three-spaced off-level dimer chain, not one per dimer. Two phase bits
remember whether the preceding same-phase row had a dimer. Chain portions
touching the window ends require an explicit constant allowance; interior
chains must be proved whole width-one banks before charging Q_roots.
This is a new candidate certificate, not yet an accepted global allocation.

### Cycle3 posthoc threshold refinement

The C=0 runs found an n8 forest with26 centers after33 cuts, while n14
returned restricted solver UNSAT after107 cuts. No proof trace was emitted.
Before claiming an exact restricted optimum, test n14 at C=1, and only
if needed at C=2,3, stopping at the first verified witness. Keep the same
60-second/10,000-round cap, exclusive outputs and fixed-core geometry.
This does not change or overwrite the original C=0 experiment.

## Final batch decision

### Cycle1 outcome: the first mixed invoice is refuted

The complete59-state/171-edge graph has a negative cycle of weight-1
per nine-row period. The pattern has an ACTUAL common-root realization
on n=9L+5, not merely an abstract port partition. Its actual main-bank
demand minus the restricted hole/isolate/pure-carrier invoice grows as
L-3-42L/A. There are no singleton F carriers, so singleton-only repair
fails too. The missing supplier is a nonpure FF dimer bank with a genuine
protected Q_roots unit. K=45L+27>n, so this is not a low-K counterexample.

### Cycle2 outcome: a reviewed rooted mixed-bank theorem

The revised graph charges S-singletons and ONE protected supplier unit
per maximal three-spaced dimer chain, not per dimer. Its complete graph
has104 states/300 edges and an integer potential in[-3,0]. The exact
endpoint allowance is2. Up to four window-end chains are discarded
rather than assigned unverified bank coupons. Interior chains are proved
whole width-one banks. The regular-window allowance is6 and the whole-
bank allowance10.

Independent mathematical review accepted the proof and the global
nonreuse argument. For disjoint selected wide-bank classes E(exposed),
S(stopped), M(rooted mixed), with one assigned side/method per bank:

    sum_(E union S union M)D_B <= R_av+6N_e+11N_m.

This removes dependence on the number of changes in the endpoint F/U
word. Actual common back roots remain a hypothesis for M. See
`../PAPER_MIXED_FRONT_PAYMENT.md` for the complete statement and proof.

Both graphs were independently regenerated by a Rust adjacency-based
checker. For each version, the same131,072 physical n11 assignments were
also checked against full primal traversal and direct strip contraction;
4,464 were feasible. All300 potential inequalities passed. The negative
family has a separate literal n14 replay; larger members were only treated
symbolically in the reviewed proof.

### Cycle3 outcome: rank obstruction and exact restricted annulus result

Guarded pendant surgery preserves primal cycle rank under its verified
full-graph edge/leaf/isolate hypotheses, even on cyclic inputs. It cannot
remove the moving-phase cap's k+1 cycles alone. A literal cyclic n14
control changes(E,c,beta)=(128,70,2) to(130,68,2).

The broader all-side depth-two annulus SAT tests completed within their
60-second limits:

| n | Required f | Outcome | Sound cycle cuts |
| --- | ---: | --- | ---: |
| 8 | 26 | independently replayed26 witness | 33 |
| 14 | 76 | restricted solver UNSAT | 107 |
| 14 | 75 | independently replayed75 witness | 69 |

Thus M_3(4)=75 is a recorded restricted exact solver result. The upper
step has NO independently checked UNSAT proof trace; it is not formal or
cross-solver certified. A further adjacency audit verified all209 cycle
cuts, model hashes, both positive witnesses and the successful cap repair.
The75 witness deletes5 and inserts2 relative to the cyclic78 candidate;
its deletion sequence reduces beta 5->4->3->2->2->0. It uses genuine
rank-changing edits rather than only pendant exchanges.

The optimal frozen-core deficit worsens between the tested sizes, but
separate SAT witnesses do not constitute a nested extension. This does
not exclude a constant-gap-one family or changes to the frozen core.
See `../PAPER_RENEWAL_ANNULUS_TEST.md` for the exact scope.

### What became smaller, and what did not

Rooted mixed whole fronts are now paid with one constant per bank, without
a cost per alternating run or a charge per supplier dimer. Together with
batch001, the account covers unrooted stopped fronts, rooted mixed fronts
and the older exposed class. Unrooted mixed roots, variable depths and
incomplete front runs remain uncovered. The unconditional upper is still
T+floor(k/2)+1. No Lean theorem or global lower bound changed.

### Branch decisions

* Stop the restricted mixed invoice and its singleton-only variant:
  a reviewed actual counterfamily defeats both.
* Accept the supplier-BANK revision, including all endpoint and ownership
  qualifications. Do not collapse it to a free per-carrier charge.
* Stop guarded pendant conversion as a cap-rank repair mechanism.
* Park zero-gap completion of the tested frozen n14 core. Retain the C=1
  witness only as a seed for a real renewal analysis, not a construction.

### Next three cycles: proposed batch003

1. **Two-sided physical interfaces:** ask whether unrooted debt at one
   front can be paid at the opposite front of the SAME actual carriers.
   Specify a geometry and coupled boundary-state model, retaining carrier
   paths rather than assuming the entire bank connected. This targets
   the remaining root-localization obligation.
2. **Certificate or counterexample:** test the two-sided payment, account
   for supplier banks and height weights once, and review the simultaneous
   nonreuse/coverage statement. Reject any inference that independent
   local payments automatically compose through arbitrary banks.
3. **C=1 renewal compatibility:** examine actual nesting of the n8 andn14
   core/annulus signatures before proposing a repeated extension. The
   current75 witness has only23 F in its central8x8 crop; it is not an
   extension of the independently found26 witness with that crop fixed.
   Test one explicit geometric repair/renewal rule, including all cap costs.

Pause at this three-cycle checkpoint. No compute-limit or objective change
is requested. The user-imposed repository-only inspection/package-directory
restriction is now part of the charter and reviewer instructions.

## Review and validation

`BATCH_002_REVIEWS.md` records discovery scrutiny, independent computational
checks and independent final mathematical/model reviews. No mathematical
finding remains outstanding on the accepted mixed-front theorem or the
qualified annulus/rank conclusions.

Final tests:49 Rust library tests passed with one pre-existing expensive
test ignored; the new Rust SAT-cycle test passed;5 Python research-program
tests passed. Relevant release binaries built and ran successfully.
Formatting and whitespace checks passed. No package/cache contents were
inspected in the final reviews, and no optimization above15 was performed.

## Artifact hashes and reproduction

SHA256:

* `data/mixed_fronts_batch002.json`:
  `7e4a7e8a16d7c6b11fd326a552ac1b5b1a6928227714fb5efd91af48f1547750`
* `data/mixed_fronts_batch002.rust_audit.json`:
  `87531350ecb81190a15d85a225773131532ab7d3e95e8280e405e9f0dab0accb`
* `data/mixed_fronts_suppliers_batch002.json`:
  `ceb7c7a607833cac4bf4fb62c752a1aafd26b0dff1da0b4b4fd027ba08890cbb`
* `data/mixed_fronts_suppliers_batch002.rust_audit.json`:
  `4e0c72864bcd437a4540b477365786af1e7959f1d9bde4466ca7e71b0e3e8941`
* `data/mixed_counterexample_batch002.json`:
  `84137a0d8c9d54d16e2ede8074b47db7587f25c47647734048b868fa75ddabd3`
* `data/renewal_annulus_n8_batch002.json`:
  `c17ceb51a653baf749f7ee60805db3116f429f93f9ed351a2322c00bd29dc8fb`
* `data/renewal_annulus_n14_batch002.json`:
  `9e75a9d1f8fc89f0ee69e6368d7ede45e606bd70730fb33ec20a836b0d37c02e`
* `data/renewal_annulus_n14_gap1_batch002.json`:
  `3fd0d216890126f4f084ba7fd3a6218f5228f21034554e5c6d831051f5ba2864`
* `data/renewal_annulus_batch002.audit.json`:
  `1b8e14918a86dad47099c6dca0b1f3a51d6874db38e135dde6848943fcb13efa`

Keep the three accompanying `.progress.jsonl` files: they contain all
actual cycle clauses used by the annulus decisions. They are journals,
not resumable SAT states or UNSAT proof traces.

Use fresh output paths inside the repository, for example:

```bash
python3 -m analysis.research_program.mixed_fronts data/mixed_reproduction.json --suppliers
target/release/audit_mixed_fronts data/mixed_reproduction.json data/mixed_reproduction.audit.json
python3 -B -m analysis.research_program.renewal_annulus --n 14 --gap 1 --seconds 60 --max-rounds 10000 --output data/annulus_reproduction.json
```
