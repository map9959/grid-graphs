# Bilateral full-rail payment without common roots

Batch003,2026-09-15. Independent mathematical review accepted the proof
and constants, requesting the suppression-order and scope clarifications
now included below. This is reviewed paper mathematics, not Lean.
This is a two-sided payment for a new geometric subclass. It does not
prove that arbitrary wide banks have the required common central interval.

## 1. Actual geometry, not a bounding-box assumption

Work on a finite n-square with A=n-1 and forced forest H(F), retaining
all vertices. The local reduction needs n>=8. On every marked level

    y_j=y0+3j, j=0,...,a,

one actual F carrier contains the entire interval[3,A-3] on that row.
For bank payment these are ALL transverse levels of the actual bank B
containing those carriers; extra same-level fragments are permitted.
Both end vertices P_L=(2,y_j), P_R=(A-2,y_j) may be F or U. The columns
S_L=1, boundary_L=0, S_R=A-1, boundary_R=A have arbitrary feasible labels.

There is NO hypothesis that different marked carriers share an interior
or ambient root. The full interval is an additional hypothesis: W_B is
the span of a union of carrier intervals, not a common interval contained
in every carrier. For n=3k+2>=11 this geometry implies W_B>=A-6>A/3,
so positive-height banks of this type are wide.

## 2. A legitimate six-column forest reduction

At each marked row there is an actual path

    P_L--(3,y_j)--...--(A-3,y_j)--P_R.

Both terminal edges are forced even if P_L or P_R is U. Different paths
have disjoint interiors. First restrict to the marked span, delete omitted
exterior connections and the central pendant leaves described below,
then suppress each marked central path to ONE P_L--P_R edge. Its internal
vertices have degree two at that stage. This is not contraction of a
whole bank or identification of all marked carriers with a root.

Between consecutive marked rows, diagonal exclusion forces both P columns
and every off-row vertex of the central interval to be U. The central
forced edges are pendant attachments to their nearest marked carrier;
there is no off-level path across the middle or between marked carriers.
Off-level edges from the middle to P are U--U and absent. Thus the reduced
graph has exactly the actual horizontal/vertical forced edges in each
three-column side strip, and the marked P_L--P_R links.

Take the regular marked run in[2,A-2], with t marks. Omit cap connections
and other exterior paths; every actual forest then gives an accepted
forest in this necessary-condition relaxation. A six-vertex frontier
partition keeps all connections between the two sides. There is no
persistent root, and closed components may disappear. No resource is
charged merely because a reduced component disappears.

## 3. Complete finite certificate

The row state is

    (phase, previous_mask, current_mask,
     partition(PL,SL,BL,PR,SR,BR), four_dimer_history_bits).

Phase0 is marked. Both P bits are forced U off-level. Add every vertical
and side-horizontal grid edge with an F endpoint, plus the marked link;
reject every cycle, retaining edge multiplicity. Canonicalize the next
six frontier vertices. The four history bits record the last same-phase
off-level dimer status on each side.

For each side finalize the current row with one-row lookahead, charging:

* a boundary-hole unit if its boundary vertex is U;
* one pure boundary F-run occurrence at its start, excluding an inward
  FF continuation;
* an off-level P-isolate when both longitudinal P neighbours and S are U;
* an off-level S-isolate when its boundary and longitudinal S neighbours
  are U (P is already U);
* an actual S-singleton if its four F-neighbour tests are all negative;
* one start of a maximal three-spaced off-level S--boundary dimer chain.

Subtract ONE demand unit per off-row across the whole bilateral model,
not one on each side. A regular run has2(t-1) demand units.

Initially no past graph edges are inserted. Virtual preceding boundary
bits are U, to count entering pure carriers once; virtual preceding S
bits are F, to suppress unsupported initial singletons. The last marked
row contributes only its boundary-hole and pure-run-start costs on each
side. These conventions do not assume labels in the omitted caps.

The complete reachable graph has2,424 states and22,508 edges. Its integer
potential phi in[-3,0] satisfies

    weight(e)>=phi(target)-phi(source)                  (1)

for EVERY edge. The maximum initial potential is0; the minimum terminal
potential including the final-row cost is-2. Therefore

    2(t-1) <= bilateral_raw_resources+2.                (2)

The complete ordered state/edge/potential arrays are archived in
`data/bilateral_fronts_batch003.json`. An independently written Rust
verifier regenerated them using adjacency components rather than the
generator's union-find and checked every weight and endpoint inequality.

The raw resources have exactly the physical interpretations listed above.
All off-level neighbour labels are known in the full grid, so isolate
claims are global. Pure boundary carriers remain pure outside the window:
an inward FF turn on a vertical F run would force a diagonal cycle.
Endpoint-suppressed singletons are never charged speculatively.

## 4. Protected suppliers and whole-bank allowance

The off-level S--boundary FF pair is an actual two-vertex horizontal
carrier, since diagonal exclusion forces its vertical neighbours U and
P is U. Its only FF cut is0 on the left or A-1 on the right. A bank
neighbour must occur three rows away and share that cut, and inside the
window can only be the corresponding dimer.

For each of the four side/off-phase classes, discard a chain touching
its first available row and a chain touching its last. There are at
most EIGHT such chains. Every remaining chain is an ENTIRE width-one
actual bank: both neighbouring rows at its ends are inside the window
and lack the required dimer, so no first bank edge can escape. Same-level
fragments cannot share its occupied FF cut with another carrier.

These interior supplier banks have no pure-boundary carriers, hence q=1.
Charge each once from its distinguished protected Q_roots unit, leaving
its small-bank refund untouched. Raw dimer-chain starts are bounded by
these actual units plus8. All other terms use original b,c,r_1 and pure-
carrier protected units. In particular no nonisolated component-closure
coupon is required for this certificate.

Let R_B^occ be the actual bilateral resource sum, retaining pure boundary
carrier occurrences but replacing raw chain starts by whole supplier units.
Then(2) gives

    2(t-1) <= R_B^occ+10.                              (3)

For n=3k+2,k>=3, use the existing protected allocation q_B-1<=s_B and
W_B<=A:

    D_B=max(0,3a_B W_B/A-(v_B-q_B)) <=2a_B.

At most d<=2 bank levels are nonregular, so a_B=t-1+d. Hence

    D_B <= R_B^occ+14.                                (4)

If t<=1, then a_B<=2 and D_B<=4; the same allowance applies without a
charged window. The whole-bank hypothesis is essential to this step.

## 5. Joint nonreuse with previous payments

Choose disjoint collections of positive-height wide banks:
E(old exposed), S(unrooted stopped), M(rooted mixed), and B(bilateral).
Each bank receives exactly ONE payment method. A bilateral bank contributes
one demand and TWO opposite side-window incidences, not two demands.

On each side, bilateral back FF edges share the depth-three cut with
stopped/mixed edges. Different banks cannot have marks at distance1 or2;
distance3 joins the displayed carriers into the same bank. Full marked
blocks cannot interleave. Against an exposed edge at the adjacent cut,
an equal mark either contradicts a P hole or belongs to the same carrier
and bank, and distance1 is diagonal. Thus nearest marked endpoints are
at least2 apart. Expanded exposed windows and unexpanded bilateral/mixed
windows are disjoint; stopped hole requests stay within their own block.
This establishes same-side hole ownership, independently of tangent
orientation conventions for the stopped invoice.
Only same-side windows are asserted disjoint; across perpendicular sides
the argument concerns distinct charged resources, not disjoint geometry.

Bilateral P/S-isolates have tangent coordinates in[3,A-3]. They cannot
meet another side's depth-one or depth-two witness line at its excluded
endpoint coordinates. The previous stopped/stopped nonreuse proof handles
the remaining pairs. S-singletons lie at depth1 and tangent[2,A-2], so
different windows cannot share them, including across perpendicular sides.
They are interior, not old pure-boundary singleton coupons.

Each charged supplier is a whole interior width-one bank. It cannot also
be a selected wide bank, a pure-boundary protected unit, a supplier in
another disjoint same-side window, an opposite-side width-one chain, or
a perpendicular supplier bank. Thus the new Q_roots charges are distinct.

Pure boundary carrier occurrences are deduplicated jointly over all
requesting side windows. Every repeat crosses a gap between consecutive
same-side windows and at most one carrier crosses a given gap. The
conservative loss is N_e+N_m+2N_b. Local allowances are5 for exposed,
10 for rooted mixed,14 for bilateral, and0 for stopped banks. Consequently
one original direct-K account gives

    sum_(E union S union M union B) D_B
       <= R_av+6N_e+11N_m+16N_b,                      (5)
    R_av=b+c+r_1+Q_roots+R_sb.

Take this account before any unreconciled later allocation. The existing
K<n reduction bounds the number of selected distinct WIDE banks by13,
so the error in(5) is at most208. It does not prove that all wide banks
are covered by the four geometric classes.

## 6. Scope, verification, remaining gap

A concrete new-coverage example is on n11: preserve x=2..8 on rows2,5,8,
the left boundary x=0 on rows2..5, and the right boundary x=10 on rows5..8;
all other vertices are U. The three rail-support trees and two boundary-
support trees meet at exactly(1,2),(1,5),(9,5),(9,8). Their intersection
graph is a tree, so the full forced graph is a forest. The main bank
meets the bilateral hypothesis. Both ends are extended on every level,
so it is not stopped. Behind the right front its rail roots split as
{2,5}|{8}, and behind the left front as{2}|{5,8}; the same splits hold
whether the P column is retained or removed. Thus neither front satisfies
the old exposed or rooted-mixed common-root condition. This illustrates
strictly new coverage, not a hypothetical low-K maximum.

This genuinely removes common-root connectivity when EVERY level of the
actual bank has a carrier spanning the stated central interval. Additional
same-level fragments need not span it. This is not an implication from width
alone. Variable-depth, fragmented or shorter interiors may fail that
interval condition, and root localization there remains open. No global
constant-gap upper or lower theorem is obtained.

For precision, if R_used is the deduplicated expenditure on selected
banks and U the unselected positive-height wide banks, the remaining
direct-K account is

    3X_2/A <= K+C_selected
        +sum_(B in U)[3X_B/A-(v_B-q_B)]-(R_av-R_used),
    C_selected=6N_e+11N_m+16N_b.

The remaining banks must be paid from R_av-R_used, not another copy of
R_av. The constant208 bounds only the selected-payment error.

The independent audit checked all155,136 candidate transitions and22,508
accepted edges, all292,604 integer charge terms, and the endpoint bound.
It also checked every one of1,048,576 physical assignments on an n11
two-rail fixture (rows3,6, central F columns3..7). The36,608 feasible
assignments agree between full primal traversal, direct suppressed-strip
topology and frontier acceptance. These finite checks verify the model;
the arbitrary-size deduction additionally uses Sections1–5 and the
complete transition potential.

Sources: `analysis/research_program/bilateral_fronts.py`,
`src/bin/audit_bilateral_fronts.rs`. Audit artifact:
`data/bilateral_fronts_batch003.rust_audit.json`.
