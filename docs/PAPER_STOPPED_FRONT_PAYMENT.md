# Stopped depth-three banks: zero-error unrooted payment

Batch001, 2026-09-14. Independent mathematical review covered the entire
note and its imported allocation/definitions, with no mathematical findings.
The finite artifacts have a separate independent Rust audit. This strengthens
the direct payment in `PAPER_GUARDED_FRONT_PAYMENT.md`: the preserved
boundary spine is unnecessary. It does not generalize that note's surgery
without its guards, and it does not establish global bank coverage.

Follow-up: `PAPER_MIXED_FRONT_PAYMENT.md` supplies a separate rooted mixed-
endpoint payment using protected supplier-bank units. This note remains
the zero-error unrooted stopped case of the combined account.

## 1. Model and hypotheses

Let H(F) be the forced forest on a finite n-square, with all vertices
retained and every primal edge incident to F forced. Set A=n-1, n>=8.
Normalize a selected target side to x=A by one fixed rotation for that
side. Suppose

    y_j=y_0+3j, j=0,...,a,  a>=1, 0<=y_0<y_a<=A,
    (A-4,y_j),(A-3,y_j) are F,
    p_j=(A-2,y_j) is U.                                (S)

All other labels and exterior connections are arbitrary subject to forest
feasibility. In particular the boundary word at x=A is unrestricted.

For bank payment, these must be EVERY transverse level of the actual
bank B, with the displayed back FF edges belonging to B. Arbitrary
additional same-level fragments are allowed. A partial run supplies only
its local invoice and cannot silently pay the entire bank's height.

## 2. An exact original-resource invoice

Let Y_B be the off-level rows strictly between y_0 and y_a. There are
exactly 2a such rows. For y in Y_B set

    u_y=(A-2,y),   s_y=(A-1,y).

**Lemma 1.** The vertex u_y and its left, upper and lower neighbours are
U. Its only possible F neighbour is s_y.

Proof. If y=y_j+1, u_y is diagonal to (A-3,y_j), and its left neighbour
is diagonal to (A-4,y_j). Its neighbour toward row y_j is the stipulated
hole p_j. Its other longitudinal neighbour (A-2,y_j+2) is diagonal to
(A-3,y_(j+1)). Thus all four stated labels are U. For y=y_j+2 use the
reflected argument from the next rail. Diagonally adjacent F vertices
would force a unit-square cycle, so every exclusion is valid. QED.

Assign one coupon for each y in Y_B:

* if s_y is U, assign the actual isolated vertex u_y;
* if s_y is F, assign the boundary-hole unit at h_y=(A,y+1).

The first coupon is a GLOBAL isolate by Lemma1. The second exists because
s_y and h_y are diagonal, forcing h_y to be U. The coordinate y+1 is
on the board, since y<=y_a-1<=A-1.

Boundary deficiency units are SIDE-LABELLED: an open-side boundary hole
has one missing-normal unit, and a corner has two, one for each incident
side. Here we request its right-side unit. This is exactly part of the
original b count, not an extra corner resource.

Let Z_B be the chosen isolates and H_B the chosen side-labelled hole
units. Isolate vertices are distinct, y->y+1 is injective, and the two
resource types are separate ledger units. Consequently

    |Z_B|+|H_B|=2a.                                    (1)

This counts selected original resources, not every resource in the region.
No contraction, root condition, maximum hypothesis or replacement occurs.

## 3. Zero-error full-bank payment

Now assume n=3k+2, k>=3, and use the existing direct-K bank allocation.
For an actual bank, s_B=v_B-a_B-1 and q_B=max(1,p_B), with p_B its number
of nonsingleton pure-boundary carriers. The existing protected-root
inequality q_B-1<=s_B and W_B<=A give

    D_B=max(0,3a_B W_B/A-a_B-s_B+(q_B-1)) <= 2a_B.

Here D_B is the full positive rectangle demand from metric-closure (32),
so it bounds the actual packet demand as well. From (1),

    D_B <= |Z_B|+|H_B|.                                (2)

There is NO additive error per stopped bank. The local invoice works for
general n>=8; importing the protected global allocation requires the
stated residue-two hypothesis. Height-zero banks have no positive demand
under that allocation and need no such invoice.

## 4. Same-side nonreuse

Select distinct stopped banks, each assigned one target side. At that
side's common cut A-4, every level of a selected bank has its back FF edge.
Distinct active rows cannot differ by one (diagonal cycle) or two (six-
cycle); difference three joins them into the same bank. Hence full level
blocks of distinct selected stopped banks cannot interleave. Their
off-level sets, and their shifted boundary-hole sets, are disjoint.

For mixed payment, let E be a disjoint selection of exposed banks from
the existing theorem. Consider only the consecutive REGULAR marked run
of an exposed bank that supplies an actual window J. Its back FF edge
is at (A-3,e),(A-2,e). An exposed mark cannot lie in a stopped block:

* equality with a stopped mark contradicts p_j=U;
* difference one gives diagonal F vertices;
* every off-level inside a stopped block is within one of a stopped mark.

The marked blocks cannot cross without a forbidden mark: the stopped
block has length at least three, and consecutive exposed marks are three
apart. Their nearest marked endpoints differ by at least two. Stopped
hole witnesses have tangent coordinates in [y_0+2,y_a], while the exposed
window is [e_0-1,e_last+1]. These intervals are therefore disjoint in either
ordering. Same-side isolate witnesses have different normal depths.
Explicitly, an exposed run following the stopped block has e_0>=y_a+2,
so e_0-1>y_a. A preceding one has e_last<=y_0-2, so e_last+1<y_0+2.

Additional fragments do not invalidate this argument: it uses the
specified back FF edge on EVERY relevant level, not uniqueness of the
carrier at that level. Exposed banks with no charged window use their
existing constant allowance and request none of these boundary units.

## 5. Cross-side isolate nonreuse, with no corner error

Stopped isolate witnesses lie on a depth-two line, with tangent coordinate
between1 andA-1. Opposite-side lines are distinct for n>=8. Adjacent lines
meet only at depth-two corners; those intersections are geometrically
impossible for two stopped banks.

For example, suppose (2,2) is an off-level candidate for both a left-
stopped bank and a top-stopped bank. Since coordinate2 is strictly between
two consecutive marked levels, the left bank has a mark Y in {3,4},
forcing (3,Y),(4,Y) to be F. The top bank similarly has a mark X in {3,4},
forcing (X,3),(X,4) to be F. These FF edges meet at (X,Y), forming a turn
in the vertex square {3,4}². Their other endpoints are diagonal F vertices,
a contradiction. Rotation handles the other corners. Thus even candidate
off-level sets cannot overlap there, whether or not s_y is F.

The EXACT old exposed-window isolate set is also important. Its tangent
coordinate is strictly between regular marked endpoints satisfying
2<=e_0<=e_last<=A-2, hence lies in [3,A-3]. An adjacent stopped depth-two
line could intersect it only at tangent coordinate2 orA-2, excluded by
that interval. Same-side and opposite-side depths are distinct. Therefore
new stopped isolates and all old exposed isolates are disjoint.

## 6. Boundary units and the combined original account

On the same side, Section4 prevents reuse of a hole unit. On different
sides, boundary vertices can coincide only at corners, where the side-
labelled units are distinct and their total available deficiency is two.
Old exposed windows exclude corners. Thus no boundary-hole collision
allowance is required either.

Take disjoint collections E,S of positive-height WIDE actual banks,
assigning each bank exactly one side and one payment method. Let R_e be
the old deduplicated exposed-bank resource sum and R_s the union of the
stopped invoices. The disjointness proofs and distinct resource types give

    R_e+R_s <= R_av = b+c+r_1+Q_roots+R_sb,
    sum_(E union S) D_B <= R_e+R_s+6N_e
                        <= R_av+6N_e.                 (3)

Use the resource account at the stage of metric-closure (26), after the
protected small-bank allocation and before any unreconciled later root
payment. This is not added to a separate clean-isolate budget. Neither
new edge rank nor components created by a cut are charged as resources.

Under K<n the existing reduction bounds the total selected WIDE banks by
13. Thus the error is at most78 and arises only from the exposed banks.
If every positive-height wide bank admitted one of these two payments,
the existing sufficient rectangle comparison would follow. That coverage
is still unproved.

## 7. Scope and remaining research

This removes BOTH common-root connectivity and the full boundary-spine
assumption for entire banks stopped at depth three. It uses the correct
height coefficient: there are 2a_B coupons for a demand bounded by 2a_B,
not a bounded front count substituted for weighted area.

Remaining geometries include mixed stopped/extended levels, varying front
depth, and banks with partial runs lacking the prescribed back edge on
some levels. No theorem says that a low-K maximum avoids those cases.
The global constant-gap bound and the construction/pump problems remain
open. The guarded neutral exchange is retained as a structural corollary
under its original assumptions, not generalized by this direct payment.

## 8. Complete finite falsification checks

Two fixtures fix full rails x=0..A-3 and stopped holes, while enumerating
arbitrary labels in the outer two columns:

| n | Rail levels | Free exterior rows | Masks | Feasible |
| --- | --- | --- | ---: | ---: |
| 11 | 2,5,8 | 1..9 | 262,144 | 7,263 |
| 14 | 4,7,10,13 | 4..13 | 1,048,576 | 18,826 |

All26,089 feasible cases satisfy the invoice. They include all-isolate,
mixed, and all-hole invoices; 4,461 n14 cases request the corner's right-
side hole unit. An independently written Rust driver reconstructed both
fixtures and re-enumerated all1,310,720 masks, matching exact feasible lists,
invoice histograms, corner cases and example actual-component counts.

The uniform and cross-side results rest on Sections2–6, not these two
finite fixtures. This is a paper proof, not Lean verification.

Files: `analysis/research_program/stopped_fronts.py`,
`src/bin/audit_stopped_fronts.rs`, `data/stopped_fronts_batch001.json`,
`data/stopped_fronts_batch001.rust_audit.json`.
