# Renewal annulus: a restricted optimum and a rank obstruction

Batch002, 2026-09-14. The model and rank argument received independent
repository-only mathematical/source review. This note makes no all-size
lower-bound claim and no independently certified UNSAT claim.

## 1. Guarded resource conversion cannot remove cycle rank

For any finite graph retaining all vertices, let beta=E-V+c. Suppose a
candidate guarded exchange has its actual full-graph local conditions
verified directly: deleting d removes only the pendant edge d--b; p
already has its old attachment; u-,u+ are isolates; promoting p adds
exactly its edges to b,u-,u+. Different selected levels do not interfere.

Per level the deletion has (Delta E,Delta c)=(-1,+1), and the three
isolated attachments have (+3,-3). Therefore

    Delta E=2, Delta c=-2, Delta beta=0.

This holds even when an unchanged component already contains cycles.
It does NOT permit inferring the guards from the forest-only diagonal
argument on a cyclic input; the changed-edge list and leaf/isolate
conditions must actually hold. A sequence of such checked operations,
or checked inverse operations, preserves beta. It therefore cannot turn
the moving-phase candidate's beta=k+1 into zero by itself.

Mobile leaf terminals can change component identity, so no assertion of
invariance for every named terminal partition is made.

A literal n14 cyclic control confirms the distinction: add F at column5,row1
to the old rooted fixture, then apply its remote guarded row7 exchange.
The graph changes from (f,E,c,beta)=(47,128,70,2) to(47,130,68,2).
The exact one removed and three added edges were independently checked.
This is a finite illustration of the graph proof, not its justification.

## 2. A broader, precisely fixed repair class

Use row,column coordinates, n=3k+2, and depth
d(r,c)=min(r,c,n-1-r,n-1-c). The moving-phase nonboundary centers are

    A_i=[2,3i] x {3i+1},        1<=i<=k-1,
    B_i=[3i+5,3k-1] x {3i+3},  0<=i<=k-2,
    x_a=(3a+2,3a+2),           0<=a<=k-1.

Fix their union at depth>=3 to F; fix EVERY other vertex at depth>=3
to U. All vertices at depth<=2, on all four sides including corners,
are free. Let M_3(k) be the maximum F count in this class.

This is broader than the previous top-two-row repair or fixed five-hole
frame: it releases all sides, one more layer and the contact pattern.
It remains a restricted frozen-core class, not all boards.

The concrete dimensions are:

| n | Deep F | Deep U | Free annulus | Target T |
| --- | ---: | ---: | ---: | ---: |
| 8 | 1 | 3 | 60 | 26 |
| 14 | 23 | 41 | 132 | 76 |

The adviser initially counted27 deep F at n14; coordinate tests corrected
this to23 before execution. The contributions are12 from A rods,9 from
B rods and2 diagonal centers. The n8 case is a diagnostic k=2 extension;
the source's uniform interior proof was stated for k>=3.

## 3. Exact SAT decision model and caps

Each primal edge has a Boolean variable e_uv equivalent in BOTH directions
to F_u OR F_v. Deep labels are fixed as above. An exact unary threshold
recurrence encodes the required number of free centers. Static unit-square
clauses exclude those cycles. Every SAT model is reconstructed on the
FULL primal graph; an actual detected cycle C gives the sound clause
OR_(e in C) not e. This excludes no feasible forest.

Runs have an external60-second limit and at most10,000 cycle cuts.
Cutoff/round limit is inconclusive. SAT requires an independently replayed
physical witness. Completed solver UNSAT is restricted to this class and
threshold; there is no emitted independently checked UNSAT proof trace.

## 4. Results

| n | Required f | Outcome | Completed cuts |
| --- | ---: | --- | ---: |
| 8 | 26 | verified forest with26 F | 33 |
| 14 | 76 | restricted solver UNSAT | 107 |
| 14 | 75 | verified forest with75 F | 69 |

All runs completed before their caps. The lower threshold at n14 was a
separate declared posthoc run; it did not overwrite the C=0 result.
The n8 witness has(f,r,b,c,z)=(26,9,8,1,0). The n14 witness has
(75,15,7,5,4).

**Recorded restricted exact solver result: M_3(4)=75.** The lower bound
has a directly checkable witness; the upper bound relies on the solver's
UNSAT answer with no independent proof-trace certification. This is not
a Lean theorem, a cross-solver proof or literal enumeration of2^132 cases.

An additional adjacency-based audit checked all209 recorded cycle cuts:
each uses actual forced edges forming a connected simple cycle. It also
reconstructed the models' hashes and both SAT witnesses. It did not
certify the solver's internal UNSAT derivation.

## 5. What changed to repair the cap

The original n14 T+2 candidate has78 F and cycle rank5. The recorded75
witness differs by deleting

    (0,7), (11,6), (11,9), (12,0), (13,11)

and adding

    (11,8), (13,1).

Deleting in that order changes beta as

    5 -> 4 -> 3 -> 2 -> 2 -> 0.

Both subsequent additions preserve beta0. Thus the successful repair
contains genuinely rank-changing deletions; it is not a sequence of
guarded pendant conversions. One deletion destroys two remaining cycles.
The entire trace was reconstructed on the full primal graph.

## 6. Consequences for renewal

The two sizes show M_3(2)>=26 and the recorded M_3(4)=75, hence

    M_3(4)-M_3(2)<=49 < T(4)-T(2)=50.

The OPTIMAL deficit of this frozen-core class therefore worsens by at
least one at this step. This rejects an exact-T completion at n14 and
a nonincreasing optimal-deficit step between these two instances.

It does not reject a constant-gap-one construction starting with a
deliberately lower-score seed, an eventual bounded deficit, or a repair
that changes the frozen core. No invariant interface or all-size capped
construction has been supplied. The75 witness is a finite diagnostic,
not an asymptotic lower family.

## Files and verification

Sources: `analysis/research_program/renewal_annulus.py`,
`src/bin/renewal_annulus.rs`, `analysis/research_program/renewal_audit.py`.
Artifacts: `data/renewal_annulus_n8_batch002.json`,
`data/renewal_annulus_n14_batch002.json`,
`data/renewal_annulus_n14_gap1_batch002.json`, their progress JSONL files,
and `data/renewal_annulus_batch002.audit.json`.

Independent source review checked the geometry, exact cardinality
recurrence, edge equivalences, static/dynamic cuts, termination handling
and rank-neutrality scope. Review inspected repository files only and
did not run another solver. Four Python tests and the Rust cycle-extraction
test passed before execution.
