# Guarded depth-three fronts: direct unrooted payment

Batch001, 2026-09-14. This note targets an uncovered interface class in
the existing metric program. It does not prove the global constant-gap
bound. Independent final review found the proofs sound and requested an
explicit wide-bank restriction for the thirteen-bank deduction; that
restriction is included below. This is reviewed paper mathematics, not Lean.

Cycle-3 continuation: `PAPER_STOPPED_FRONT_PAYMENT.md` removes the boundary
spine from DIRECT PAYMENT and removes the two-unit per-bank allowance.
The guarded neutral-exchange theorem below retains its original hypotheses.

## 1. Fixed model and guarded geometry

Work on a finite n-square, coordinates 0,...,A with A=n-1. The forced
graph H(F) keeps all vertices and every primal edge incident to F. Assume
H(F) is a forest. Two diagonally adjacent F vertices are impossible,
because they force a unit-square cycle. Local statements below need n>=8.

Orient the target side as x=A. Let

    y_j=y_0+3j, j=0,...,a,   a>=1,   0<=y_0<y_a<=A.

Assume, on EVERY displayed level,

    (A-4,y_j),(A-3,y_j) are F;  p_j=(A-2,y_j) is U,       (G1)

and assume the physical boundary is entirely F on the run:

    (A,y) is F for y_0<=y<=y_a.                         (G2)

No root-connectivity hypothesis is imposed. Arbitrary additional labels
are allowed elsewhere, provided the full forced graph remains a forest.

For a BANK payment, additionally require that y_0,...,y_a are all the
transverse levels of one actual horizontal bank B, and that its displayed
back FF edges belong to B. Other fragments on its levels are permitted.
Without this whole-bank condition the local lemmas still hold, but their
witness count need not pay the entire bank's demand.

## 2. Global isolate witnesses

For every interior level j=1,...,a-1 define

    u_j^-=(A-2,y_j-1),   u_j^+=(A-2,y_j+1),
    Z_B={u_j^-,u_j^+:1<=j<=a-1}.

**Lemma 1.** These are distinct global isolates and |Z_B|=2(a-1).

Proof. Each u_j^epsilon is U by diagonal exclusion against (A-3,y_j).
Its four neighbours are all U:

* the left neighbour is diagonally adjacent to (A-4,y_j) in F;
* the right neighbour is diagonally adjacent to (A,y_j) in F;
* the neighbour toward row y_j is the stipulated hole p_j;
* the other longitudinal neighbour (A-2,y_j+2epsilon) is diagonally
  adjacent to (A-3,y_(j+epsilon)) in F.

Both guard levels exist because j is interior. This exhausts every
possible supplier, including exterior attachments. The coordinates obey
2<=y_j+epsilon<=A-2; all witnesses lie in {2,...,A-2}². Three-spaced
levels have distinct +/-1 positions. For a=1 the assertion is empty. QED.

## 3. Simultaneous neutral boundary exchange

Choose any subset I of the interior levels, with |I|=t. Delete
d_j=(A,y_j) from F and insert p_j for each j in I.

**Lemma 2.** The resulting set F' is feasible, with exactly

    Delta f=0, Delta r=t, Delta b=t,
    Delta c=-2t, Delta z=-2t, Delta K=0.                 (1)

Proof. Let b_j=(A-1,y_j), q_j=(A-3,y_j). Initially p_j is a leaf
attached to q_j. The vertex b_j is U by a diagonal F neighbour on the
boundary. Its vertical neighbours are U by diagonal exclusion against
d_j; its remaining neighbours are p_j (U) and d_j (F). Thus b_j is a
leaf attached to d_j. The two vertical neighbours of d_j are retained F.

Deleting d_j therefore removes exactly d_j--b_j; its vertical edges stay
forced. This makes b_j isolated. Promoting p_j adds exactly the three
edges from p_j to b_j,u_j^-,u_j^+. Each attaches a distinct isolated
vertex to an existing tree. Across selected levels all attachment
vertices are distinct and none is another selected p_j or d_j. Hence the
entire simultaneous operation is a forest, regardless of root identities.

It has net edge gain 2t and unchanged vertex count, so Delta c=-2t.
Only the two original isolates per level cease being isolated, giving
Delta z=-2t. In G[F], each deleted d_j has degree two and each inserted
p_j has exactly one preserved neighbour; the nonadjacent deletions split
the boundary carrier t times, giving Delta r=t. Each deleted d_j is an
open-side boundary vertex, while inserted p_j is interior, so Delta b=t.
Cardinality is neutral and the ledger is conserved. QED.

If the q_j of a consecutive selected run are connected in H[x<=A-3],
that connecting subgraph survives. The new FF edges q_j--p_j supply the
rooted-window hypothesis of metric-closure (28). This exposes the selected
run, not necessarily the whole bank: unpromoted outer levels remain.
Equation (1) permits no additional K credit. In particular one cannot
retain the old isolate coupons alongside new boundary/carrier coupons.

## 4. Direct payment needs no surgery and no roots

Now use the paper's residue-two setting n=3k+2, k>=3, and its actual-bank
parameters: a=a_B, v=v_B, W=W_B, s=v-a-1, q=max(1,p_B), with p_B the
number of nonsingleton pure-boundary carriers in B. The existing protected
allocation proves q-1<=s. Also W<=A. The full rectangle demand is

    D_B=max(0,3aW/A-a-s+(q-1)) <= 2a.                  (2)

**Theorem 3.** For a positive-height guarded bank,

    D_B <= |Z_B|+2.                                    (3)

This follows immediately from (2) and Lemma1. Since D_B pays the full
rectangle demand, it pays the actual packet demand as well. All coupons
are original globally isolated vertices in F. No maximum hypothesis,
common root, boundary exposure, or post-replacement allocation is needed.
The +2 is an additive error allowance, not two further isolate coupons.
For a=1 the selected witness set is empty. Additional endpoint-adjacent
isolates may exist; the deliberately interior selection simplifies nonreuse.
The residue restriction belongs to the imported allocation; the local
isolate/exchange lemmas were stated separately for general n>=8.

## 5. Simultaneous nonreuse, including adjacent sides

Select distinct guarded banks, each assigned one target side. Their Z_B
sets are pairwise disjoint.

On one side every displayed back FF edge is active at the same cut A-4
after orientation. Different active rows cannot differ by one (diagonal
cycle) or two (six-cycle). Difference three joins the carriers into the
same bank. Consequently level blocks of distinct selected banks cannot
interleave, and their rows are separated by at least four. Their interior
off-level witness sets are disjoint.

Opposite-side witnesses have distinct depth-two coordinate lines, since
n>=8. Adjacent-side lines intersect only at a depth-two corner. Such an
intersection cannot actually be shared. For example a shared (2,2) would
come from interior mark y=3 on a left bank and x=3 on a top bank: interior
marks are at least three, so mark1 is impossible. Their back FF edges
force (3,3),(4,3),(3,4) to be F. The last two vertices are diagonal,
contradicting feasibility. Rotation handles the other corners. Thus even
an additive corner-overlap allowance is unnecessary.

For N_g guarded banks, letting Z_g be their union, (3) gives

    sum_guarded D_B <= |Z_g|+2N_g.                     (4)

## 6. Combination with the existing exposed-bank account

Use exactly the DIRECT K resource pool from metric-closure (26), before
any additional root allocation:

    R_av=b+c+r_1+Q_roots+R_sb.

Let E be a collection of distinct exposed banks as defined in that note,
with E disjoint from the selected guarded collection G. Each selected
bank is assigned exactly one target side.
Its reviewed simultaneous theorem gives

    sum_exposed D_B <= R_e+6N_e,

where R_e counts unique boundary-hole, protected-carrier and depth-one
isolate coupons. Guarded Z_g lies in the deep square {2,...,A-2}² and
is disjoint from every depth-one exposed isolate. Its resource type is
also different from boundary holes and carrier units. Therefore

    R_e+|Z_g| <= R_av,
    sum_(E union G) D_B <= R_av+6N_e+2N_g.              (5)

This is a single original-resource allocation. If later arguments have
spent any of these units, they must be deducted rather than reused.
It is not combined with an independent copy of the clean-isolate budget.

For the global reduction, restrict E and G to positive-height WIDE banks.
Under K<n the existing wide-bank count gives N_e+N_g<=13. Thus (5) has
total error at most78. If every positive-height wide bank belonged to E union G, the existing
sufficient rectangle comparison (27) would follow with an absolute error.
That coverage statement is NOT proved.

## 7. Exactly what is new and what remains

Previously the exposed-window payment required actual common interior
roots and back FF edges at depth two. The new guarded subclass has back
FF edges at depth three and can have completely disconnected root pieces.
It is paid directly from forced private isolates. This removes the root
condition for that subclass rather than assuming a neutral normalization
for arbitrary unexposed banks.

Uncovered: variable-depth fronts, missing boundary-spine guards, mixed
stopped/extended levels, partial fronts not covering all bank levels,
and general height-weighted terminal transport. These remain genuine
global obligations. The guarded hypotheses are not consequences of low K.

The neutral exchange is not a pump: it preserves f and consumes two
isolates per level. No renewable increment or controlled cap closure is
obtained. The global upper and lower bounds are unchanged.

## 8. Finite checks and evidence scope

`analysis/research_program/guarded_fronts.py` examined all393,216 optional
subsets in four fixed side14/15 extension families. Exactly208 were feasible;
all passed the isolate and neutral-exchange identities. The middle and
side15 cap patches each admit only the baseline; cap patches on rooted
and rootless side14 boards admit125 and81 feasible extensions respectively.
These are complete specified families, not all feasible extensions.

An independently written Rust driver, `src/bin/audit_guarded_fronts.rs`,
reconstructed the skeletons and optional sets, re-enumerated all masks,
matched every feasible-mask list, and checked all five ledger changes.
The side14 full-three-row control gives (46,7,36,71)->(46,9,39,66);
its outer endpoint is outside the guarded lemma and is not generalized.

The rootless fixture has three teeth in three distinct actual H components.
The side15 fixture verifies a two-level simultaneous operation, not the
residue-two resource theorem. Uniform statements rely on the proofs above;
the finite audits do not establish their unrestricted quantifiers.

Artifacts: `data/guarded_fronts_batch001.json` and
`data/guarded_fronts_batch001.rust_audit.json`.
