# Forced crops: exact nesting and rewrite costs

Batch003,2026-09-15. Independent mathematical review accepted the symbolic
argument and finite-test scope, requesting explicit feasibility in C_k;
that clarification is incorporated below. This is not Lean verification.
This concerns the specified moving-phase frozen-core classes, not all
grid forests or all possible constant-gap constructions.

## 1. The source sets and the larger frozen-core rule

Use zero-based(row,column) coordinates, n=3k+2, k>=2, and
d_k(r,c)=min(r,c,n-1-r,n-1-c). Let I_k be the FULL nonboundary source set

    A_i=[2,3i] x {3i+1},       1<=i<=k-1,
    B_i=[3i+5,3k-1] x {3i+3}, 0<=i<=k-2,
    x_j=(3j+2,3j+2),         0<=j<=k-1.

These are the rods/singletons in the constant-gap lower research note.
Let C_k be the class of FEASIBLE boards (H(F) a forest) whose labels at depth>=3 are EXACTLY
I_k intersect{d_k>=3}. Every other deep vertex is fixed U; the entire
outer three-layer annulus is free.

Embed the old board by tau_k(r,c)=(r+3,c+3) into side n+6. Then

    d_(k+2)(tau_k(v))=d_k(v)+3.

Every old vertex is therefore frozen by the larger class C_(k+2), not
only the old deep core. Its forced destination pattern is

    Q_k=tau_k^(-1)(I_(k+2)).                            (1)

The preimage is restricted to the old board's vertex set. Labels outside
Q_k are forced U. No larger board is needed to compute this pattern.

## 2. Explicit formula and counts

Reindexing the nonempty cropped rods gives

    Q_k = union_(j=0..k) [0,3j] x {3j+1}
        union union_(j=-1..k-2) [3j+5,3k+1] x {3j+3}
        union {(3j+2,3j+2):0<=j<=k-1}.                 (2)

In the first family, j=0 is the singleton(0,1). The rightmost rod has
j=k. The second family's j=-1 term is the left boundary rod. Distinct
column residues make the three displayed families disjoint.

The first family has sum_(j=0..k)(3j+1) centers, the second has
3 sum_(j=1..k)j, and the diagonal family has k. Thus

    |Q_k|=3k²+5k+1=T(k)-(2k-1).                        (3)

Equivalently, Q_k is I_k plus disjoint top extensions at rows0,1,
bottom extensions at rows3k,3k+1, a left rod[2,3k+1]x{0}, a right
rod[0,3k]x{3k+1}, and singleton(0,1). The additions have10k-2 centers
and lie in the outermost two layers. Since |I_k|=3k²-5k+3, this checks(3).

Clipping I_k to depth>=3 removes one center from each of its k-1 A rods,
one from each of its k-1 B rods, and the two end diagonal centers. Hence

    |I_k intersect{d_k>=3}|=3k²-7k+3,
    |Q_k intersect{d_k<=2}|=12k-2.                     (4)

Q_k and I_k agree on every old deep F AND U label.

## 3. Uniform literal-nesting obstruction

**Theorem.** If S_(k+2) belongs to C_(k+2) and its central copy of S_k
is unchanged in all labels, then S_k=Q_k.

Proof: every copied vertex has new depth>=3 and therefore exactly the
label prescribed by I_(k+2). Equation(1) specifies those labels. QED.

Consequently a literally nested chain in these classes has

    f(S_k)=T(k)-(2k-1)

at every stage having a successor. No fixed C gives f(S_k)>=T(k)-C
at arbitrarily large k. If both consecutive stages have successors,

    f(S_(k+2))-f(S_k)=12k+22,

four fewer centers than the target increment12k+26.

The Q_k actually form a feasible nested family: the source theorem
proves H(I_(k+2)) is a forest for arbitrary k+2>=4, and restriction to
the central board gives H(Q_k). Moreover Q_(k+2) differs from I_(k+2)
only at new depth<=1, so its three-layer crop is precisely Q_k. Thus the
count obstruction describes actual nested forests, not only a formal
incompatible pattern. It is not an improved lower bound.

## 4. Bounded-cardinality rewrite is also impossible

For a seed S_k in C_k, the required label changes before embedding are

    D_k=S_k\Q_k,   A_k=Q_k\S_k.

All are in the OLD rewrite band depth<=2, which becomes NEW depth3..5.
The old deep core becomes new depth>=6 and already agrees. The new
outermost three-layer frame is the only free part of the larger class.

If |S_k|=T(k)-C, then

    |D_k|-|A_k|=2k-1-C.                               (5)

For |S_k|>=T(k)-C this is a lower bound on the net deletions. Thus any
uniform bound B on the number of changed old labels fails once
2k-1-C>B. This rules out bounded-CARDINALITY edits, not a fixed-width
band containing linearly many edits, nor a different larger deep core.

For a gap-C successor, the new frame would have to supply exactly

    [T(k+2)-C]-|Q_k|=14k+25-C                         (6)

centers. Equations(5),(6) identify the needed growing rewrite and new-
frame budget. Separate high-scoring witnesses do not establish renewal.
The signed difference between the new-frame count and target increment
12k+26 is exactly2k-1-C, the mandatory net old-label loss. It supplies
no additional score gain once the rewrite is included.

## 5. Exact finite tests, preserving old deep labels

Only Q_2 on n8 and Q_4 on n14 were materialized. The primary generator
uses(2); an independent Rust auditor reconstructs I_k plus the disjoint
extensions, checks every allowed singleton promotion, and records an
actual cycle for each rejected one.

A rejected singleton promotion excludes that vertex from EVERY superset:
additional F labels only add forced edges and cannot destroy its cycle.
This reduces the complete superset problem to subsets of the eligible
pool, with no heuristic cutoff in these two instances.

| n | Q score | Allowed old-annulus holes | Eligible promotions | Exact maximum superset score |
| --- | ---: | ---: | --- | ---: |
| 8 | 23 | 38 | (0,0),(7,7) | 25 |
| 14 | 69 | 86 | (0,0),(13,13) | 71 |

All four subsets of each two-vertex eligible pool are feasible. The
independent audit contains120 explicit rejection cycles (36+84). These
finite upper exclusions do not depend on the earlier SAT UNSAT answer.

At n8 all703 pairs of the38 allowed old-band holes were also enumerated.
Exactly one pair yields25 centers: the two corners. The three other
Q_2 holes in the old deep core are fixed U and were NOT candidates.

## 6. A genuine gap-one step, but not a renewable template

Let S_8=Q_2 union{(0,0),(7,7)}. It has25=T(2)-1 centers. Delete the two
corners, embed the resulting23-center Q_2 at(+3,+3), and add the52
outer-frame centers of the recorded75-center n14 witness. Its central
8-square is exactly that embedded Q_2.

Every intermediate graph is a forest: deletion preserves feasibility;
the embedded Q_2 and each later prefix are subsets of the final verified
forest. Both implementations replayed all56 stages. The actual step is

    25 -> 23 -> embedded23 -> 75,

with net gain50=T(4)-T(2), and the old deep F/U core unchanged.
The frame alone adds52 rather than50 centers, but it is attached only
after the two old corners are removed. Ignoring that rewrite would
misidentify a one-step count surplus as a renewable gain.

The same one-sided rewrite template cannot continue from a75-center
n14 seed in C_4. Such a seed cannot contain Q_4, since the exact maximum
allowed superset of Q_4 is71. Therefore the next rewrite needs additions
of missing Q_4 centers as well as deletions, not merely deletion of extras.
This conclusion does not instantiate or optimize an n20 board.

For the specific recorded inputs, the mandatory rewrite to Q is:

* recorded n8 score26 seed: delete10, add7, totaling17 flips;
* recorded n14 score75 seed: delete18, add12, totaling30 flips.

The latter is the cost for that particular seed, not the minimum over
all75-center seeds. Both changes stay in the old band. The score mismatch
alone (three or six) significantly understates those label differences.

## 7. Outcome and scope

The literal-nesting and uniformly bounded-edit approaches are refuted
for these frozen-core classes by a uniform counting/geometry proof.
A first minimum-rewrite gap-one step exists, but the delete-only template
already fails at the next tested seed size. A constant-gap construction
with an O(k)-sized coordinated rewrite inside a fixed-width band remains
open, as does a construction with different frozen cores.

No global lower bound or pump is claimed. These tests are different from
optimizing all forests on n8 or n14; the earlier restricted M_3(4)=75
retains its solver-UNSAT/no-independent-proof-trace status. Only its
positive75 witness is used for the composition here.

Sources: `analysis/research_program/nested_renewal.py`,
`src/bin/audit_nested_renewal.rs`. Artifacts:
`data/nested_renewal_batch003_cycle3.json` and its `.rust_audit.json` peer.
The source artifact's display rows use F/U; center IDs and the coordinate
scope are explicit. Native Rust verification reconstructs the board from
those IDs, independently of display alphabet.
