# Rooted mixed fronts: supplier-bank payment

Batch002, 2026-09-14. Independent final mathematical review covered the
complete proof, counterfamily, finite-state model and allocation imports;
no mathematical defect was found. This is reviewed paper mathematics,
not a Lean formalization.
This note retains the original direct-K allocation. It does not establish
root localization or global coverage of arbitrary wide banks.

Batch003 continuation: `PAPER_BILATERAL_FRONT_PAYMENT.md` removes the
common-root requirement for banks with an actual spanning central carrier
on every level, using both physical fronts. It does not infer that
common-interval geometry from bank width alone.

## 1. Geometry and the failed first invoice

On a finite n=3k+2 square, k>=3, set A=n-1. An actual positive-height bank
B has all its transverse levels y_j=y0+3j, j=0,...,a, and contains the
back FF edges (A-4,y_j)--(A-3,y_j). Extra same-level fragments are allowed.
Set p_j=(A-2,y_j) and epsilon_j=1 when p_j is F. Both epsilon values are
allowed. Assume all q_j=(A-3,y_j) lie in one ACTUAL component of the
induced forest H[x<=A-3]. No boundary-word hypothesis is imposed.

The old stopped invoice survives on exactly

    2a-m,  m=epsilon_0+epsilon_a+2 sum_(0<j<a)epsilon_j

off-levels. A first attempt tried to pay the rest using only boundary
holes, depth-one/depth-two isolates, and pure boundary carriers. That
attempt is false, even under the actual common-root hypothesis.

### An actual repeatable counterfamily

For L>=1 set n=9L+5, A=9L+4, y0=2. Preserve the full left spine x=0
and rails x=2,...,A-3 on rows y_j=2+3j, j=0,...,3L. In columns
(P,S,boundary)=(A-2,A-1,A), use L copies of the nine-row mask word

    1,4,4,5,4,4,0,6,0

followed by terminal marked mask1. Bits0,1,2 denote F at P,S,boundary.
All other vertices are U. Marked rows are phases0,3,6 modulo9, so their
P word is F,F,U. All marks are regular, in[2,A-2].

The left spine and separated rails form a tree with pendant neighbours.
In each nine-row block, the boundary F run at offsets1..5 attaches to
that tree through offset3. The S--boundary FF dimer at offset7 attaches
to this boundary component through the U at offset6. It has no second
inward attachment. Boundary rows at offsets8,9 are both U, separating
successive boundary components. Thus the graph is a forest at every L,
and all q_j are connected behind the strip. Equivalently, the explicit
rooted-strip state returns to itself after this block without a cycle.

On the marked span, the old invoice has 3L+1 boundary holes, L pure
boundary carriers, L depth-two isolates, and zero depth-one isolates.
Enlarging to the old regular window adds two boundary holes, giving5L+3.
There are no singleton F carriers anywhere in this family.

The main bank has a=3L, v=3L+1, q=1. Its actual straight-cell count is

    X_B=L(3A-14).

Indeed adjacent rail widths are A-4,A-4,A-5 cyclically, and each gap
contributes the smaller FF width. Therefore its ACTUAL demand, not just
its rectangular surrogate, exceeds that restricted window invoice by

    (3X_B/A-a)-(5L+3)=L-3-42L/A,

which is unbounded. Adding only S-singleton coupons cannot fix it.

The missing supplier is the horizontal FF dimer at offset7. Successive
dimers are nine rows apart; each is its own one-carrier, height-zero bank,
with p=0 and one retained Q_roots unit. Those L original units pay the
exhibited deficit. This is not a counterexample to the full resource pool:

    f=27L²+27L+6, r=5L+2, b=21L+13, c=19L+12,
    K=45L+27>n.

Only L=1 (n14) was materialized; its literal ledger is(60,7,34,31), its
actual X_B is25, and its singleton count is zero. Arbitrary L is justified
by the displayed geometric/periodic forest argument, not a larger search.

## 2. A corrected finite certificate

Take the consecutive regular marked levels, 2<=y_j<=A-2, and let their
number be t. For t>=2 use the three-column strip on the marked span.
Contract the actual connected back component to one persistent root rho.
Off-level vertices in P and the adjacent back column are U by diagonal
exclusion. The only forced edges crossing the left strip cut are the
marked q_j--p_j edges, even when p_j is U.

The state records phase modulo3, previous/current three-bit row masks,
the exact partition of current P,S,boundary,rho, and two bits recording
whether the previous row of each off-phase was an S--boundary dimer.
Closed nonroot components are allowed to disappear. Each next row inserts
every forced vertical and horizontal edge and, at a mark, the root edge.
Any cycle is rejected, retaining multiplicities. Other exterior paths are
omitted, so this is a necessary-condition relaxation.

Finalize the current row with one-row lookahead. The transition weight is

    h + p + z2 + z1 + s1 + dstart - demand,              (1)

where:

* h=1 if the current boundary vertex is U;
* p=1 for a boundary F-run start with inward S labelled U;
* at an off-level, z2=1 if S is U and both longitudinal P neighbours are U;
* at an off-level, z1=1 if S,boundary and both longitudinal S neighbours
  are U (off-level P is already U);
* s1=1 if S is F and its P,boundary and two longitudinal S neighbours
  are U: an actual singleton carrier;
* dstart=1 for an off-level S--boundary FF dimer when the preceding row
  of that SAME off-phase was not a dimer;
* demand=1 at an off-level and zero at a mark.

Thus dstart counts three-spaced dimer CHAINS, not all their vertices or
all dimers. Such dimers have vertical neighbours U by diagonal exclusion
and P=U, so they are actual two-vertex horizontal carriers.

Initially the first row is marked, with all8 masks allowed. There are no
past graph edges. The virtual preceding boundary bit is U, to count a
pure carrier already entering the window once. The virtual preceding S
bit is F, solely to suppress an unsupported first-row singleton charge.
Both dimer-history bits start zero. After the first step the masks are
actual row data. The last marked row contributes only its hole/run-start
cost; unsupported endpoint singleton or isolate claims are not made.

The complete reachable graph has104 states and300 edges. Its archived
integer potential phi, in[-3,0], satisfies

    weight(e) >= phi(target)-phi(source)                (2)

on EVERY edge. The largest initial potential minus the smallest terminal
potential including the final marked-row cost is2. Consequently, on every
length of regular run,

    2(t-1) <= h+p+z2+z1+s1+dstarts+2.                  (3)

The graph, ordered states, weights and potential are in
`data/mixed_fronts_suppliers_batch002.json`. The precise transition and
weight rules are implemented in `analysis/research_program/mixed_fronts.py`.
An independent Rust checker regenerates the entire graph by adjacency
traversal rather than union-find and verifies every inequality and the
endpoint bound. No reset occurs at changes of epsilon.

The previous model, without s1/dstart, has59 states and171 edges. Its
negative nine-edge cycle has weight-1 and exactly the word in Section1.
That failed certificate and its independent audit are also retained.

## 3. Turning local dimer chains into original protected units

There are two off-phase classes. In each, at most one dimer chain touches
the first available off-level and at most one touches the last. Discard
those at most FOUR boundary chains from the resource charge. They may
extend outside the window or belong to an otherwise larger bank.

Every remaining chain is an ENTIRE actual width-one bank. Its dimers have
only the FF cut A-1. Any adjacent bank carrier must lie three rows above
or below and share that cut; within the window the P hole forces such a
carrier to be exactly the corresponding S--boundary dimer. At both ends
of an interior chain that neighbouring row is inside the window and is
not a dimer. No bank edge can escape. Same-level additional fragments
cannot share this FF cut with another carrier.

All these dimers lie on interior rows, so none is a pure-boundary carrier.
Their bank has p=0, q=1 and W=1; its one distinguished protected carrier
unit is retained in Q_roots after the small-bank allocation. Charge that
unit once for the chain, leaving its small-bank refund untouched.

Let Q_supp count these interior supplier banks. Then

    dstarts <= Q_supp+4.

The other terms in(3) count genuine original resource units: boundary
holes, global isolates, actual S-singletons, and occurrences of actual
pure boundary carriers. In particular s1 uses r_1, not cut components.
Hence

    2(t-1) <= R_window+6.                              (4)

For the whole bank, at most d<=2 of its a+1 levels lie outside[2,A-2],
so a=t-1+d. Since D_B<=2a in the protected residue-two allocation,

    D_B=max(0,3a_B W_B/A-(v_B-q_B)),

    D_B <= R_window+10.                                (5)

Here R_window consists of the actually charged hole/isolate/singleton
terms, endpoint-suppressed pure-carrier occurrences, and the protected
units of interior whole supplier banks. Discarded boundary chains are
covered by the additive allowance, not charged as unverified resources.

If t<=1, then a<=2 and D_B<=4, so the same allowance applies without
requesting a window. Equation(5) is a rooted mixed-bank payment, not an
unrooted normalization theorem.

## 4. Simultaneous resource ownership

Select disjoint collections of positive-height wide actual banks:
E (old exposed), S (unrooted stopped), and M (rooted mixed here). Assign
each bank exactly one target side and one payment method.

Mixed and stopped marked runs have the same back FF cut. Their blocks
cannot interleave: row differences1,2 are cyclic, and difference3 joins
the carriers into the same bank. For an exposed/mixed pair at adjacent
FF cuts, equality of marks either contradicts a P hole or joins the
displayed FF edges into the same carrier/bank; difference1 is diagonal.
The consecutive marked blocks therefore cannot interleave and their
nearest endpoints differ by at least2. An old expanded exposed window
and a mixed marked-span window are disjoint. Stopped hole requests are
within their own marked span. Thus same-side hole units are distinct.

Mixed z1 and z2 witnesses have tangent coordinate strictly between
regular marks, hence in[3,A-3]. Opposite normal lines are distinct;
cross-side intersections with depth-one/depth-two lines would require
coordinates1,2,A-2 orA-1, outside the relevant tangent range. Together
with batch001's stopped/stopped argument, all isolate witnesses are
non-reusing. Mixed S-singletons lie at depth1 on tangent rows[2,A-2];
distinct mixed windows cannot share them, including across sides. They
are interior, so they are not old pure-boundary singleton coupons.

Each charged supplier bank is a whole interior width-one dimer chain.
It is not wide, has no pure-boundary carriers, cannot extend to another
same-side window, and cannot be a supplier chain on an opposite side
or perpendicular orientation. Therefore its Q_roots unit is neither a
selected main-bank demand nor a previously charged pure-carrier coupon.

Pure boundary carriers can meet several exposed/mixed windows. Deduplicate
their occurrences jointly: every repeat crosses a gap between consecutive
disjoint same-side windows, and at most one carrier crosses each gap.
The loss is at most N_e+N_m. Old exposed local error is5 per bank; mixed
local error is10 per bank; stopped payment has zero error. Thus one
original direct-K allocation gives

    sum_(E union S union M) D_B
        <= R_av+6N_e+11N_m,                           (6)
    R_av=b+c+r_1+Q_roots+R_sb.

Take this account before any unreconciled later root payment. Under K<n,
the existing WIDE-bank reduction gives N_e+N_s+N_m<=13, making the error
at most143. No conclusion that every wide bank belongs to these classes
has been established. The global constant-gap bound remains open.

## 5. Verification scope

The complete graph and integer certificates were independently regenerated
in Rust. For BOTH versions, every one of131,072 assignments on a physical
n11 rooted seven-row strip was checked against full primal traversal,
direct contracted-strip traversal and frontier acceptance. Those tests
check the implementation; the arbitrary-length theorem uses the transition
model, the finite potential and the original-resource arguments above.

The old negative-cycle tile has a separate literal n14 replay and symbolic
all-size derivation. Neither it nor the finite tests instantiate K<n.
No board above15 was optimized or materialized in this batch.
