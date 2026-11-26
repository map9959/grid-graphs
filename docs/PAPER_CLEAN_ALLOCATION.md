# Global Clean Allocation

Date: 2026-09-08. Paper deduction only; no optimization or Lean.

## Outcome

Current checkpoint: independent read-only reviews covered this complete
note through Fragment Budget And Minimal Banks (original line 1778), with
no mathematical findings. Historical review-status statements below describe
earlier snapshots. No result here is Lean-verified.

The global ordered-join optimization is exact, but cannot generate credit
after all unused length is retained. Subsequent spatial arguments eliminate
representative corrections and discount all overlap of named wide-bank
rectangles without error. Every small bank can be paid using its height
units, with pure-boundary units and the genuine fragment remainder protected.

The unfinished problem is the singly covered wide-bank area and its actual
weighted terminal demand. Even a minimal bank with one carrier per level
has height-weighted front motion. The diamond construction refutes cutting
into vertex-disjoint carrier paths at one unit per fragment; it does not
refute the global upper bound or a low-budget theorem. See also
[the metric continuation](PAPER_CLEAN_METRIC_CLOSURE.md).

The unconditional bound `P(3k+2)<=3k^2+7k+C` is NOT proved here.
This note gives a global, non-reusing allocation reduction, rather than
another list of short-strand subclasses. For the fixed paid isolate
allocation, all remaining ordered projection joins can be optimized
exactly by an interval-width theorem. Their Hall obstruction is an actual
overlap set of physical chain projections, not an abstract numerical ray.

The reduction does not bound that obstruction by the retained clean bank.
Moreover, once exact unused length is admitted, optimizing these joins
cancels identically from the residual. This identifies the exact failure
of this global augmenting-path approach; it is not a counterexample to
the desired bound or a proof that other allocations cannot succeed.

Inputs read: all of `PAPER_ISOLATE_ROUTING_UPPER.md`, including its final
Clean Endpoint Resources certificate; all of `PAPER_GLOBAL_CAP_PAYMENT.md`,
including the corrected outer-J_3 hypothesis and E_C overlap warning;
and the dual note's area conversion, strand budget, matching/rank, and
exact spare-length arguments. The new deductions below are not described
as independently audited.

## Freeze Only Paid Resources

Assume F is nonempty, `n=3k+2>=11`, and use the source's physical counts.
Put `A=n-1`, `T=3k^2+7k`, and fix one execution of the simultaneous
isolate donor allocation. Keep its dirty matching and new donor joins,
of sizes `nu_D` and `nu_N`. Do NOT select any clean join yet.

Retain the source's private endpoint payments E_C exactly once, and set

```text
D_port = D_C-E_C,
B = B_C+nu_N+sigma_D,
B_C = 3(c-z-1)+t_0+3delta/2+C_C,
sigma_D = 3nu_D-3m_D/2,
N = g_+-nu_D-nu_N.
```

All terms in B are nonnegative. Equation (38) of the isolate note with
`j_C=0` gives

```text
S >= 3N+1+B-D_port.                                (1)
```

The retained dirty/donor joins partition the positive corridors into N
nonempty base chains. Each has one horizontal or vertical axis and
strictly ordered, disjoint straight-cell projections. These statements
are properties of the actual paid allocation, including its nonreuse.

There is no fresh V_rem, T_rem, component, or contact credit in (1).
In particular the flat-packet inner charge is already represented in
its E_C slots; it is not added again. Positive clean ports at J_4 are
not presumed free. The outer-J_3 classification withdrawn in the cap
note is not used.

## Global Projection Packing

For each base chain q take the hull of its straight-cell projections,

```text
I_q = [a_q,b_q],  0<=a_q<=b_q<=A-1,
ell_q = number of straight cells in q.
```

These are integer cell labels on that chain's own axis. Although the
chain may contain corridors on different parallel rows, its projections
are disjoint, so `ell_q<=b_q-a_q+1`. Every straight cell occurs in exactly
one base chain, and hence `sum_q ell_q=X_2`.

Permit an additional projection join from q to r exactly when their
axes agree and `b_q<a_r`. This is a counting join, not an assertion of a
path in C or a modification of F. Its meaning is simply that the entire
ordered list of straight intervals of q can precede the entire list
of r in one A-cell allowance. No bend strand, backing FF edge, or
presumed opposite partner is required.

This extends the allowed clean joins in the source's final statement,
but its capacity justification is direct: concatenating such lists
keeps all their projected cell labels distinct. It spends no donor
token. A base chain may have at most one predecessor and one successor;
these use its two different outer ends, never an end already used by
an internal dirty/donor join. Exterior ends need no special assumption:
an end reaching label 0 cannot have a predecessor, and one reaching
label A-1 cannot have a successor.

For axis `d` in `{horizontal,vertical}` define

```text
w_d(t) = #{q of axis d : a_q<=t<=b_q},
W_d = max_{0<=t<A} w_d(t),
W = W_horizontal+W_vertical.
```

An axis with no base chains has W_d=0.

**Global width theorem.** The minimum number of allowances in any packing
by the permitted additional joins is exactly W. The maximum number of
additional joins is exactly `N-W`. In particular, for every actual
configuration, with arbitrary clean strands and isolates,

```text
X_2 <= A W.                                       (2)
```

Proof. Work on one axis. Intervals containing a common integer label t
must belong to different allowances, so at least W_d are necessary.
For sufficiency, process intervals in nondecreasing order of their left
endpoints. Append the next interval to any list whose last right endpoint
is strictly smaller than its left endpoint; if none exists, start a new
list. When the algorithm creates its j-th list at label a, the last
intervals of all j-1 old lists contain a: their left endpoints are at
most a, and none has right endpoint below a. The new interval also
contains a. Thus `j<=W_d`. Every list is ordered and has total straight
length at most A. Summing over the two axes proves (2).

There are no cycles, since each join strictly increases the hull's
coordinates. A list of h base chains uses h-1 additional joins, so the
number of joins is N minus the number of lists. This proves the claimed
maximum and endpoint nonreuse simultaneously. No greedy loss is hidden
in the algorithm: the common-label lower bound proves optimality. QED.

Optimality here is relative to keeping the paid base chains intact and
concatenating their whole ordered projections. It does not rule out
interleaving their internal gaps, splitting paid chains with returned
credits, or using a different metric argument.

## Exact Hall Form

The same global allocation has a precise augmenting-path formulation.
Make left and right copies of the N base chains, with an edge `q_L r_R`
for every permitted projection join. A matching is exactly a set of
joins using each outgoing and incoming end at most once. Strict order
excludes a directed cycle, so every matching gives disjoint lists.

For a subset U of the left copies, write Gamma(U) for its right-copy
neighbours. The maximum matching formula is

```text
maximum joins = N-max_U (|U|-|Gamma(U)|),
max_U (|U|-|Gamma(U)|) = W.                        (3)
```

For completeness, every matching leaves at least
`|U|-|Gamma(U)|` left vertices unmatched. Conversely, take a maximum
matching and start alternating paths at all unmatched left vertices.
There is no reachable unmatched right vertex. If U is the reached left
set, all neighbours Gamma(U) are reached right vertices; their matched
partners are precisely the reached matched left vertices. Thus
`|U|-|Gamma(U)|` equals the total number of unmatched left vertices.
This proves the first line. The width theorem proves the second.

Therefore choosing more candidates or rerouting a matching in this
ENTIRE ordered-projection join graph cannot improve on N-W. This graph
already contains all eligible and backed-packet joins compatible with
keeping these base chains intact; it does not need an exposure theorem
for either gadget. One cannot infer (3) from forest acyclicity alone:
the interval coordinates are essential to the value W.

## What The Allocation Pays

Substitute `N=W+(N-W)` into (1). This gives the following unconditional,
parameterized clean certificate:

```text
S >= 3W+1+B-D_port+3(N-W),
D_width = max(0,D_port-B-3(N-W)),
3(f-T) < 19+D_width.                              (4)
```

Indeed (2) is the physical allowance, (1) pays it with the indicated
debt, and `K>=S+1` gives the source's area-conversion hypotheses. No
exceptional area is charged a second time.

Equation (4) is a simultaneous global allocation, not a demand-by-demand
assignment of a whole three-unit join to every incident strand. The
signed bank is summed once in (1), and each of the N-W joins reduces
the number of allowances once. Tokens need not be geographically
adjacent to the strand whose signed debit they offset: their use here
is the global additive budget, not a new local routing assertion.

For a proposed absolute debt D_0>=0, this particular width-only allocation
closes precisely when

```text
W <= N-(D_port-B-D_0)/3.                           (5)
```

If `D_port<=B+D_0`, no joins are needed. Otherwise the required number
is `ceil((D_port-B-D_0)/3)`, and (3) is the exact Hall test for obtaining
it. Thus the unanswered step is a bound on ACTUAL projection overlaps
relative to ACTUAL retained credit, not the availability of a better
augmenting-path algorithm.

No uniform version of (5) is proved here. No assignment of scalar counts
or an abstract interval family is offered as a feasible grid violating
it. In particular failure to prove (5) is not an actual counterexample
to (5), much less to the target bound.

## Width-Weighted Failure

One might hope to pay the remaining overlap obstruction by the unused
width of the optimal lists. Its complete non-reusing form is explicit.
Define the base-chain internal gap count

```text
H = sum_q (b_q-a_q+1-ell_q) >= 0.
```

Double counting actual hull labels proves

```text
Delta_width = A W-X_2
  = H+sum_d sum_{t=0}^{A-1} (W_d-w_d(t)).           (6)
```

The first term counts missing labels inside each base hull. The second
counts unused hull capacity in the W_d allowances. They are separate
slots of the same total capacity, not private physical area credits
that can also be allocated to overlapping windows.

Using (6) in the area conversion is valid, but the signed debt becomes

```text
D_port-B-3(N-W)-3Delta_width/A
  = D_port-B-3N+3X_2/A.                            (7)
```

More generally ANY permitted packing with j additional joins has
`Delta_j=A(N-j)-X_2`, and

```text
3j+3Delta_j/A = 3N-3X_2/A.                         (8)
```

Thus augmenting by one join adds three units of join credit and removes
exactly three units of normalized unused-length credit. A maximum
matching cannot create a new payment after the complete unused length
has been retained. This identity holds on the actual grid, without a
numerical relaxation or a hypothetical configuration.

To locate also the loss from conservative banking, define the actual
nonnegative discarded surplus

```text
epsilon = S-(3N+1+B-D_port) >= 0.
```

Then (7) is exactly

```text
1+3X_2/A-S+epsilon.                               (9)
```

Recovering epsilon would require identifying further unspent resources
or rebuilding the donor payments, not merely selecting different clean
joins. Even with epsilon recovered completely, the remaining expression
is the original signed physical metric deficit `1+3X_2/A-S`.

## Exact Unfinished Step

This attempt supplies a full global matching algorithm, its proof of
optimality, actual endpoint nonreuse, and an exact Hall obstruction.
It does NOT supply the geometric inequality that would bound that
obstruction or its width-weighted residual by an absolute constant.

Specifically, the two possible closing statements for this allocation are
(5), or the weaker sufficient statement

```text
D_port <= B+3N-3X_2/A+D_0                          (10)
```

for one absolute D_0 on every actual feasible square. Neither is proved.
The all-one-pair eligible case is not removed: its positive regular
through endpoints have no E_C payment, and with z=0 it receives no new
isolate-join surplus. No argument above forces its simultaneous hull
overlaps, terminal positions, and retained bank to satisfy (5) or (10).

This is the exact failure returned by this pass, rather than an assertion
that backed partners exist or a promise of a future Hall proof. A proof
of the desired unconditional theorem is still absent. Only this file was
created; no grid search, optimization, finite feasibility check, Lean
command, or unrelated edit was performed.

## Spatial Crosscut Continuation

This appendix preserves the preceding pass. The unconditional constant-gap
theorem is still not proved. There is now a genuine two-dimensional
inequality: h actual horizontal corridors through one vertical cut and v
actual vertical corridors through one horizontal cut force at least 3hv
distinct missing axial slots in those corridors. A second-moment consequence
uses both orientations globally. Neither argument assumes that hull overlap
is actual corridor occupancy.

For the paid arbitrary-isolate chains, the correct transfer includes an
explicit occupied-slot correction E. The resulting payment below is valid
for every configuration, but its remaining signed debt is not proved
bounded. In particular `K>=3W-O(1)` is neither proved nor refuted here.

## Physical Stripe Packets

Use cell coordinates in `{0,...,A-1}^2`. An actual horizontal positive
corridor e has straight cells

```text
{(x,y_e): a_e<=x<=b_e},   ell_e=b_e-a_e+1.
```

Its two perpendicular leaves at every straight cell give the rectangle

```text
R_e = [a_e,b_e] x [y_e-1,y_e+1].
```

The analogous vertical rectangle is
`[x_e-1,x_e+1] x [a_e,b_e]`. All these rectangles, over BOTH orientations,
are pairwise disjoint sets of physical cells.

Proof. A straight cell has its two actual deleted leaves in the
perpendicular directions, as in the dual note's local lemma. Each deleted
leaf has exactly one parent in the full dual. It cannot be assigned to
two straight cells or also be a straight cell. Straight cells themselves
belong to unique corridors. This proves disjointness, including between
orientations. The perpendicular leaves are board cells, not exterior
ports: consequently `1<=y_e<=A-2` horizontally and `1<=x_e<=A-2`
vertically. All the displayed width-three bands are untruncated. The
argument is unchanged by globally isolated holes. QED.

Fix a vertical cut at column label x_0 and a horizontal cut at row label
y_0. Let H_0 be the actual horizontal corridors with `a_e<=x_0<=b_e`,
and V_0 the actual vertical corridors with `a_e<=y_0<=b_e`. Write
`h=|H_0|`, `v=|V_0|`.

The three-row bands of the H_0 corridors are pairwise disjoint: otherwise
their rectangles intersect at x_0. Similarly the three-column bands of
the V_0 corridors are pairwise disjoint. In particular

```text
3h<=A,  3v<=A.                                    (11)
```

These bounds concern actual corridor occupancy, not the hull counts W_d.

## Non-Reusing Plus-Crosscut Payment

**Crosscut theorem.** For every x_0,y_0 in the cell array,

```text
3hv <= sum_{e in H_0 union V_0} (A-ell_e).          (12)
```

Proof. For a pair `(e,f)` in `H_0 x V_0`, write e's row as y and f's
column as x. The two rectangles would intersect if both

```text
[a_e,b_e] meets [x-1,x+1],
[a_f,b_f] meets [y-1,y+1].
```

Since their Cartesian intersection is forbidden, at least one of these
two intersections is empty. Make the following deterministic assignment:

1. If the first intersection is empty, assign the pair the three missing
   axial slots `x-1,x,x+1` of horizontal corridor e.
2. Otherwise assign it the three missing axial slots `y-1,y,y+1` of
   vertical corridor f; the second intersection must then be empty.

For fixed e, different vertical partners have disjoint three-column
bands. For fixed f, different horizontal partners have disjoint
three-row bands. Slots of different corridors have different corridor
identities; horizontal and vertical slots are also distinct. Thus all
3hv assigned slots are different and are absent from their named
corridors. Every slot lies in the board's axial range. Summing their
available missing slots proves (12). QED.

Each assigned band is entirely before or entirely after its named
corridor. This is a literal endpoint-inset payment, with three different
labels per pair. It is NOT one new component unit per pair or per
endpoint: a single endpoint may own many bands, but only with the
correspondingly large missing length. The physical 3-by-3 rectangles
`[x_f-1,x_f+1] x [y_e-1,y_e+1]` of different pairs are disjoint as well.
No enclosing larger rectangles have been summed.

## A Global Second Moment

Let X_H and X_V count all horizontal and vertical straight cells, so
`X_H+X_V=X_2`. With ell_e the length of each actual positive corridor,
(12) has the unconditional consequence

```text
3 X_H X_V <= A sum_e ell_e(A-ell_e).                (13)
```

Proof. Sum (12) over all A^2 pairs of cuts. Each horizontal corridor
appears at exactly ell_e vertical cuts, and each vertical corridor at
exactly ell_e horizontal cuts. Therefore the left-hand sum is
`3(sum_{x_0} h(x_0))(sum_{y_0} v(y_0))=3X_H X_V`.
On the right a corridor's contribution occurs ell_e times for its own
cut coordinate and A times for the other cut coordinate. This gives
exactly the right-hand side of (13). QED.

Equivalently,

```text
sum_e ell_e^2 + 3X_H X_V/A <= A X_2.               (14)
```

If g_H,g_V are the numbers of positive corridors in the two orientations,
Cauchy-Schwarz also gives

```text
X_H^2/g_H + X_V^2/g_V + 3X_H X_V/A <= A X_2,        (15)
```

where a term with zero corridor count is defined to be zero (its
corresponding X is zero). These are restrictions on actual simultaneous
lengths, not a formal-count feasibility argument.

The summation does not authorize repeated donations to the clean bank.
Dividing the cut sum by A^2 is a weighted average of valid inequalities.
A missing slot of corridor e has total weight at most ell_e/A in that
average. It is not a fresh unit every time another cut sees it. Thus
(13) is a second metric constraint, not an additional independent copy
of the spare-length term in (7).

## Hull Gaps And Paid Isolates

Before transferring (12), distinguish two precise ways a chain can
invalidate a naive corridor-inset donation.

First, retain the base chains of the prefix and define h_d(t) to be
actual straight-corridor occupancy at the cut perpendicular to d. The
base chain's straight projections are disjoint, so at most one of its
corridors occupies any label. Consequently

```text
w_d(t) = h_d(t)+gamma_d(t),
gamma_d(t) = number of base chains whose hull contains t
             but whose straight projections do not,
sum_d sum_t gamma_d(t) = H.                        (16)
```

The last H is exactly the internal hull-gap count in (6), not a new
isolate bank. At most one gap of a given base chain contains a specified
label. Thus a hull-only overlap can be labelled by an actual missing
slot, but it cannot be treated as a physical width-three stripe.

Second, even if the chain really crosses the cut, its selected corridor
is generally shorter than its whole chain. A slot absent from that
corridor can be occupied by another corridor in the same chain on a
different parallel row or column. Subtracting `A-ell_e` from a chain's
allowance without this correction would reuse already counted length.

Both issues occur at the level of the actual paid chains. Their solution
does not involve pretending isolates are absent, returning a z credit,
or assuming that a positive J_4 clean port was reserved.

## Corrected Chain Crosscut Theorem

Take any optimal W-list packing constructed in the prefix, keeping all
paid dirty/donor joins intact. Choose x_0 and y_0 attaining the BASE hull
peaks W_H and W_V. Each horizontal packed list contains exactly one of
the W_H base hulls meeting x_0: those hulls must be in different lists,
and there are only W_H lists. The same holds vertically at y_0.

Hence the actual corridors in H_0 and V_0 lie in distinct packed lists.
Their counts are exactly

```text
h = W_H-gamma_H(x_0),
v = W_V-gamma_V(y_0).                              (17)
```

Carry out the three-slot assignment from (12), but label every assigned
slot by its packed list rather than just its representative corridor.
This preserves injectivity: the representatives are in different lists,
and the three-bands at a fixed representative were already disjoint.

Define E to be the number of those assigned slots occupied by another
straight corridor in their named packed list. This is a measurable
integer in `[0,3hv]`, not a hypothetical resource. Each occupied slot
corresponds to one actual straight cell, since a list has no repeated
projected label. Distinct such slots correspond to distinct straight
cells. In particular

```text
E <= sum_{selected packed lists q} (ell_q-ell_rep(q)).
```

The other `3hv-E` assigned slots are genuinely missing from their lists.
They can therefore be donated simultaneously, giving

```text
Delta_width = AW-X_2 >= 3hv-E.                     (18)
```

Unselected lists and all other missing slots are simply left uncharged.
This proves (18) with arbitrary isolates and arbitrary clean strands.
There is no assumption about paths through the space between joined
corridors, or about the transverse displacement of a virtual join.

With B and D_port from the retained certificate, the resulting global
payment is

```text
D_cross = max(0,D_port-B-3(N-W)-3(3hv-E)/A),
3(f-T) < 19+D_cross.                              (19)
```

Indeed use the allowance `W-(3hv-E)/A`, which is nonnegative and at
least `X_2/A` by (18), in (1) and the area conversion. This uses the
W-list join saving and ONLY the specified missing slots of those same
lists. The occupied E slots are not donated. The old isolate resources,
endpoint slots, and dirty matching surplus remain allocated exactly as
in the prefix.

For multiple choices of peak cuts or optimal packings, one may take the
best single resulting bound. Their separate 3hv-E payments must not be
summed: the same list's missing slots can be encountered in more than
one choice.

## Diagonal And Turn Allowances

A diagonal sweep does mix the two orientations, but its length price
must also be retained. For `phi(x,y)=x+y`, successive horizontal or
vertical straight cells advance by one if traversed east or north.
Their unit intervals in phi lie in a range of length `2A-1`, not A.
For `x-y` the same statement holds after reversing the vertical direction.
A valid monotone diagonal packing therefore supplies up to `2A-1`
straight cells per list. It is not an A-length allowance merely because
the list has been given one name.

Rescaling phi does not remove this cost. With phi=(x+y)/2 the range is
at most A, but every straight cell contributes only one-half unit of
projected length. More generally the affine sweep
`phi=alpha*x+beta*y`, with alpha,beta nonnegative, weights horizontal
length by alpha and vertical length by beta and has range at most
`A(alpha+beta)`. Choosing `alpha+beta=1` normalizes the range, not both
orientation weights to one. Paid base joins must also be checked for
monotonicity in the new sweep before they can be retained.

A turn join has an equally explicit price. Suppose two distinct current
lists have actual straight lengths ell_1,ell_2, each at most A. Even if
their geometry permits a turn, a combined allowance of the form
`A(1+rho)` with a nonnegative surcharge rho must satisfy

```text
rho >= max(0,(ell_1+ell_2-A)/A).                    (20)
```

At this minimum price, replacing their two old allowances saves only
`1-rho` allowances, or `3(1-rho)` budget units, rather than three.
This is just length conservation, not an obstruction to all turn joins.
A proof that the sum is at most A would justify a full saving. A proved
unspent bend payment could instead pay the surcharge 3rho. Neither
follows from the existence of the turn. In particular a clean contact
edge already used to form D_port or C_C is not another available bend
payment unless its earlier allocation is returned.

Thus a diagonal or turning argument can still be substantive, but must
prove a new length or resource bound; it cannot silently replace the
axis-split W by a smaller list count at the same price.

## Remaining Spatial Failure

The new deduction captures the requested quadratic interaction on the
physical grid: (12) forces 3hv private endpoint slots, and (13) constrains
all corridor lengths jointly. The arbitrary-isolate transfer (18)
identifies exactly which of these slots survive the already paid joins.
There is no unsupported claim that every pair forces a new component,
a new carrier, an exceptional cell, or a backed clean partner.

For an absolute debt D_0, the still-unproved sufficient comparison is

```text
D_port-B-3(N-W) <= 3(3hv-E)/A+D_0.                 (21)
```

No uniform bound on the occupied-slot correction E by an unspent bank
has been obtained. Allocating all its cells to an intervening join does
not by itself prove a bounded charge per join: those cells can lie along
the subsequent corridor, rather than in the short join gap. They have
only the length value explicitly recorded above. Likewise, the
nonnegative hull-gap count in (16) cannot be counted a second time as a
full credit per chain.

Even an E-free mixed-orientation argument does not alone settle the
one-orientation obstruction: the quadratic term vanishes when one
orientation is absent. The all-one-pair eligible seam problem is still
not paid by a proved spatial bank inequality in this appendix. Neither
(21) nor `K>=3W-O(1)` is inferred from the second-moment inequality.

The result is therefore an unconditional two-dimensional nonreuse
inequality and its exact corrected clean certificate, not the requested
unconditional constant-gap upper theorem. The remaining failure is the
comparison (21), with its occupied-slot correction and the independent
one-orientation case, not an unperformed matching computation.

Verification: in-memory direct checks used only the explicit boundary-comb
and five-deletion nested-frame families on sides 11 and 14. Their forced
graphs were verified to be forests. At every pair of cuts, the 3hv slots
were checked for absence and nonreuse, and (13) was checked as an integer
inequality. There were 538 cut pairs over the four configurations. These
checks do not establish the general theorems or bound E; their proofs are
the arguments above. No optimization, configuration search, board above
14, or Lean command was run. Only this appendix was added to this note.

## Finite Wide-Bank Continuation

Date: 2026-09-08. The user reports review of the preceding crosscut
continuation. The new arguments below do not inherit that review. Read
the complete height-weighted continuation of
`PAPER_CLEAN_METRIC_CLOSURE.md`, including its small-bank allocation,
at-most-thirteen-wide-bank reduction, and internal-contact warning.

The new result removes the representative occupied-slot correction E
from the bank-level crosscut argument. It also pays ALL overlapping-box
overcount simultaneously, with zero boundary error, and protects every
pure-boundary carrier in the small-bank allocation. The remaining
single-covered area/root payment is not proved. In particular the
unconditional constant-gap theorem is still absent.

This appendix uses the metric note's DIRECT allocation from K. Nothing
here is added to the old isolate certificate's B or D_port. Switching
to the direct argument avoids splitting its paid chains or spending
their carrier resources twice.

## Whole Physical Stripes

Keep the metric note's banks of nonsingleton carriers. For a horizontal
bank B, let its extreme carrier rows be y_B and y_B+3a_B, and its axial
active-cut interval be

```text
I_B = {l_B,...,u_B-1},   W_B=u_B-l_B.
```

The potential stripe j, for `0<=j<a_B`, has the three physical cell rows

```text
J_Bj = {y_B+3j,y_B+3j+1,y_B+3j+2}.
```

Define S_Bj to be ALL cut labels at which B has an active carrier on
both bounding rows y_B+3j and y_B+3j+3. Thus S_Bj is a subset of I_B,
possibly a union of many separated intervals. Every actual corridor
fragment on this same stripe is included. By the cutwise rail bijection,
its complete straight-and-leaf packet set is exactly `S_Bj x J_Bj`.
Use the transposed definition for vertical banks.

Write sigma_Bj=|S_Bj| and define the missing stripe capacity

```text
G_B = sum_j (W_B-sigma_Bj) = a_B W_B-X_B >=0.       (22)
```

These are missing labels on named PHYSICAL stripes, not missing labels
on a representative corridor or an abstract joined list. A label is
missing only when no fragment on that stripe occupies it. There is
therefore no analogue of E to subtract later.

The source's fragmentation integral is retained exactly. Let n_B(t)
count active carriers of B and p_B(t) its cut-component count. Then

```text
F_B = sum_{t in I_B} (p_B(t)-1),
U_B = sum_{t in I_B} (a_B+1-n_B(t)),
G_B = U_B+F_B.                                    (23)
```

Indeed at most one carrier is active per transverse level, so U_B>=0.
The cut forest has `x_B(t)=n_B(t)-p_B(t)`. Subtract this from a_B and
sum. This proves (23) including arbitrary same-level fragments. U_B
and F_B are two parts of G_B, not additional credits on top of it.

## E-Free Bank Crosscuts

Let B be horizontal and C vertical. Keep B's stripes with `J_Bj subset
I_C`, and C's stripes with `J_Ci subset I_B`. These are full three-cell
bands within the other bank's actual axial range. Put

```text
Y_BC = sum_{j: J_Bj subset I_C} sigma_Bj,
Y_CB = sum_{i: J_Ci subset I_B} sigma_Ci.
```

At cuts t in I_B and u in I_C, select the retained B stripes containing
t in their S sets and the retained C stripes containing u. If their
counts are h and v, then

```text
3hv <= sum_selected_B (W_B-sigma_Bj)
       +sum_selected_C (W_C-sigma_Ci).             (24)
```

Proof. For any selected pair, the actual packet sets are
`S_Bj x J_Bj` and `J_Ci x S_Ci`. Their intersection would be nonempty
if both `S_Bj meets J_Ci` and `S_Ci meets J_Bj`. Physical packet
disjointness forbids this. Assign all three labels of J_Ci to stripe
Bj if that entire band is absent from S_Bj; otherwise assign J_Bj to
stripe Ci. At least one assignment exists. Different partners have
disjoint three-bands, and different named stripes have different slots.
Thus there are 3hv distinct missing whole-stripe labels. Disconnected
S sets cause no problem: the argument uses set intersections, not
interval containment of one representative fragment. QED.

Summing (24) over the W_B W_C cut pairs gives the sharper bank-level
second-moment inequality

```text
3Y_BC Y_CB
 <= W_C sum_{j retained} sigma_Bj(W_B-sigma_Bj)
    +W_B sum_{i retained} sigma_Ci(W_C-sigma_Ci).    (25)
```

Every retained stripe is selected at exactly sigma of its own cuts.
This proves the formula by the same weighted averaging as (13), with
the bank widths in place of A. In particular

```text
G_B+G_C >= 3Y_BC Y_CB/(W_B W_C).                   (26)
```

No occupied-slot correction is suppressed in (24)--(26). Counting each
maximal fragment separately would instead introduce artificial losses:
for disjoint fragments of lengths ell_i on one stripe,
`sum_i ell_i(W_B-ell_i)` is generally larger than
`sigma(W_B-sigma)`. The latter, with sigma=sum_i ell_i, is the quantity
actually proved here.

The boundary trimming in this version has an absolute total price in
the low-K reduction. At most two stripes of B partially intersect I_C
without being contained in it, one at each end. Together they contain
at most 2W_B straight cells; the transposed exclusion costs at most
2W_C. With p horizontal and q vertical wide banks, `p+q<=13` and
`pq<=42`. Omitting every such partial stripe once costs at most

```text
sum_omitted 3X/A <= 12pq <= 504.                   (27)
```

This is an upper bound on the UNION of omitted cells, not separate
donations for each encounter with the same stripe. Stripes wholly
outside the other axial interval are not boundary errors and are not
declared paid by that pair. They have no interaction with its box.
The next theorem handles partial intersections directly and needs no
trimming or 504 allowance at all.

## Exact Joint Box Discount

Define the potential cell rectangle

```text
R_B = I_B x {y_B,...,y_B+3a_B-1}
```

for a horizontal bank, and transpose this for a vertical bank. A bank
of height zero has an empty rectangle. This is a proved containment
of its STRAIGHT-AND-LEAF PACKETS: those packets are the disjoint union
of the sets `S_Bj x J_Bj` just constructed. No containment of the
bank's forced components, connecting paths, or contact roots is asserted.

Consequently exactly 3G_B cells of R_B are absent from B's packet set.
Let WIDE denote the at-most-thirteen wide banks and put

```text
R_union = union_{B in WIDE} R_B,
Omega = sum_{B in WIDE} |R_B|-|R_union| >=0.
```

**Joint discount theorem.** With arbitrary isolates and fragments,

```text
3 sum_{B in WIDE} G_B >= Omega.                    (28)
```

Proof. At any cell z let m(z) be the number of wide rectangles containing
it. Since all actual bank packets are disjoint, at most one of those
banks occupies z. Thus at least m(z)-1 of the named slots `(B,z)` are
missing when m(z)>0. Choose exactly m(z)-1 missing slots there. Choices
at different cells use different slots, and no slot is chosen twice.
The total chosen is `sum_z max(m(z)-1,0)=Omega`. Each bank has precisely
3G_B missing slots available, proving (28). QED.

This is a simultaneous allocation, not a sum of pairwise rectangle
overlaps. A cell in m rectangles contributes m-1, not `m(m-1)/2`.
The distinction prevents reuse even with only thirteen banks. Different
`(B,z)` slots at the same physical z are legitimate here only because
they discount the different copies of capacity that were previously
included in `sum_B |R_B|`. They are not new physical resource tokens in K.

For just two banks, (28) reads
`3(G_B+G_C)>=|R_B intersection R_C|`; it includes all partial three-bands
with zero rounding error. The general theorem handles both perpendicular
and parallel bank boxes. Rectangles may overlap arbitrarily and banks
may occupy arbitrarily sparse subsets of them.

## What Finite Interactions Actually Remove

Let r_ns, t_bank, R_small, and R_free have the metric note's meanings.
Retain signed wide demands rather than truncating them separately:

```text
T_wide = sum_{B in WIDE} [a_B(3W_B/A-1)-s_B].
```

The small-bank payment and the exact formula (22) imply

```text
3X_2/A <= r_ns-t_bank-R_small
          +T_wide-(3/A)sum_{B in WIDE} G_B.         (29)
```

This improves the rectangle-only sufficient demand by its ACTUAL
missing stripe capacity, with F_B already included once through (23).
Apply (28). The overlap correction cancels the duplicate box areas
exactly:

```text
T_wide-Omega/A
 = |R_union|/A-sum_{B in WIDE}(v_B-1).              (30)
```

Thus all overlapping-box interaction can indeed be removed jointly,
without E and without a per-bank-pair boundary error. But what remains
is the singly covered union, not zero:

```text
|R_union|/A
 <= sum_{B in WIDE}(v_B-1)+R_free+C                (31)
```

would suffice for the constant bound. Equation (31) is NOT proved.
Using merely `|R_union|<=A^2` does not prove it. In the low-budget regime
its right side can only be bounded using the still-unallocated root,
boundary, and carrier resources; inserting the desired K bound at that
point would be circular.

One may also retain
`3sum_WIDE G_B-Omega=|R_union|-3sum_WIDE X_B`, the area of this union
not occupied by WIDE packet sets. Those cells may contain small-bank
packets or exceptional cells; they are not asserted to be empty grid
space. This nonnegative residual may improve (31), but does not relate
the remaining wide-packet area to R_free.
The second-moment restriction (25) is additional geometry, not an extra
copy of G_B that may be subtracted again after (29).

## All Boundary Carrier Units Can Be Protected

There is a refinement of the small-bank allocation useful for the
remaining root problem. Let p_B be the number of nonsingleton PURE
BOUNDARY carriers belonging to bank B, and set `q_B=max(1,p_B)`.
These p_B are carrier counts, not the cut-component function p_B(t).

**Protected-root theorem.** On `n=3k+2`, every bank has a simultaneous
cutwise cell assignment with the following properties:

* Every straight cell is assigned to one of its two active rail carriers.
* Every pure-boundary carrier receives no cell.
* If p_B=0, a specified distinguished carrier receives no cell.
* Each other carrier receives at most one cell per cut, and no more
  cells in total than its own number of FF edges.

Proof. All rows of a horizontal bank have one residue modulo three.
The two boundary rows 0 and A=3k+1 have different residues. Hence B
can have pure-boundary carriers on at most ONE boundary row. At each
cut at most one such carrier is active, even if the bank has many
separate fragments on that boundary. If active, root its cut-forest
component there. When p_B=0, root the component of the distinguished
carrier there whenever it is active. Root all other components at their
lowest transverse carrier. Orient each path component away from its
root and assign its straight-cell edges to their child carriers.

A nonroot has one parent edge; a root has none. An inactive carrier
cannot receive a cell. Thus every pure-boundary carrier is protected
over ALL cuts, including disjoint activity intervals of different pure
fragments. Rotation proves the vertical case. The two orientations
have different nonsingleton carriers, so their assignments are disjoint.
QED.

It follows that

```text
X_B <= (v_B-q_B)W_B.                               (32)
```

Also `q_B-1<=s_B`: if p_B>0, its p_B boundary fragments lie on one
transverse level, and each of the other a_B levels has at least one
carrier. This is compatible with `a_B<=v_B-q_B`.

For small banks, (32) spends at most one unit at each of the v_B-q_B
nonprotected carriers. Their remaining conservative refund is

```text
R_small_boundary
 = sum_{B small} (1-3W_B/A)(v_B-q_B) >=0.
```

Thus the following original resources can be retained jointly:

```text
Q_roots = sum_B q_B,
R_free_boundary = b+c+r_1+Q_roots+R_small_boundary. (33)
```

Each nonsingleton pure-boundary carrier has its OWN unused r unit in
Q_roots, not one unit per bank shared by all such carriers. Singleton
pure carriers already belong to the separate r_1 resource. For wide
banks this is a reservation of units, not a claim that their remaining
carrier units pay all their area. Their corresponding signed demand
must use `v_B-q_B` instead of `v_B-1`.

This strengthens the small-bank allocation without assuming that small
banks are rectangles. It may support a future root allocation, but the
protected carrier count cannot also be added to the old R_free: that
would mix two different divisions of the same r term.

## Exact Remaining Root Payment

Combining the protected-root allocation with the joint box discount
gives the improved sufficient comparison

```text
|R_union|/A
 <= sum_{B in WIDE}(v_B-q_B)+R_free_boundary+C.     (34)
```

The area of R_union outside the wide packet sets can again be subtracted
if retained.
Neither (34) nor its actual-area version is established universally.
Consequently no absolute C is obtained in this pass.

The one-orientation failure is particularly precise. When the relevant
wide rectangles are disjoint, Omega=0 even if there are only one or two
banks. A wide bank can contain order-n transverse rail levels. Protecting
its boundary carriers supplies actual available units, but does not
prove a payment for all those levels. A perpendicular boundary spine
may itself be a wide bank of HEIGHT ZERO: it has an empty R_B and no
crosscut area product, yet can connect many other bank rails through
distinct real contacts. It must not be dropped from a root argument
merely because it has no corridor area.

The metric note's `m_B<=s_B` correctly leaves at least a_B+1 contact
components inside a bank after other carriers are removed. Those are
still not a_B+1 ambient c tokens. The new protected pure-carrier units
do not change that fact. No row-coverage or opposing-root Hall inequality
has been proved here that bounds the unpaid part of (34) by those
protected units, boundary holes, and the actual ambient components.

Thus the finite mixed-bank interaction is now accounted for exactly
at the level of capacity overcount. It does not, by itself, pay the
remaining singly occupied region. This is an exact failure of the
proposed closure, not a feasible counterexample to (34) or to the
constant-gap target. No unproved rectangle containment or contraction
of a rail bank into a contact-tree vertex is used.

Verification: direct in-memory checks used six explicit feasible sets
on sides 11 and 14: the boundary comb, the five-deletion nested frames,
and the complete three-spaced horizontal rows with the single vertex
(3,0) deleted. The last family has two pure-boundary fragments in one
bank and tests the multiple-protected-root case. Forced-forest
feasibility, whole-stripe fragmentation identity, disjoint packet sets,
joint box discount, bank-pair moment inequality, and protected child
assignments all passed. These finite checks are not the uniform proofs
and instantiate no low-K counterexample. No search, optimization, larger
board, or Lean ran. Only this appendix was added to this note.

## Moving Physical Strip Continuation

Date: 2026-09-08. Read the metric note's new Rooted Boundary Coverage
continuation, including its actual interior-connectivity hypothesis,
protected resource allocation, and total 6N error. That payment is
retained, not silently extended to interior moving endpoints.

There is a new exact moving-strip theorem below. It allows arbitrary
phase changes consistent with the physical forest and arbitrary additional
preserved vertices in the strip. It turns the number of strip steps into
signed terminal phase displacement, private deep isolates, singleton
bridges, and an actual root-partition term, with no per-row error.

The terminal displacement is not paid universally. Neither an
unconditional one-orientation upper theorem nor the global constant-gap
bound is proved. An explicit feasible family also shows why the
triangular box discount alone cannot pay this terminal term.

The dual rigidity statement must be used precisely: with two straight
cells at every participating corridor, sigma in
`v_(i+2)=v_i+(sigma,3)` is FIXED along a good one-pair component. It is
not an independently chosen sign at every step. The variable-phase
theorem below does not assume every variable-phase transition is itself
a clean one-pair link; it counts the other events physically.

## Actual Variable-Phase Rails

Use (x,y) coordinates. Let t>=1, and choose integer L,R,y_0 with

```text
0<=L<R<=A,   0<=y_0,   y_0+3t+1<=A,
w=R-L,
L+1<=a_j<=R-3,  0<=j<=t.
```

Require the following actual preserved horizontal rail segments:

```text
L_j = {(x,y_0+3j): L<=x<=a_j},
R_j = {(x,y_0+3j+1): a_j+2<=x<=R},  0<=j<=t.       (35)
```

Every displayed rail has an FF edge. The left rails all belong to one
rail bank, because consecutive levels share the FF cut L; the right
rails all belong to another, through the FF cut R-1. Their residues
differ, so these are different banks. They may extend beyond this window
or have additional fragments elsewhere. No contact connectivity of either
bank is assumed yet.

Other labels, inside and outside the window, are initially arbitrary
subject to feasibility. Diagonal exclusion already forces the displayed
left endpoints to stop at a_j and the displayed right endpoints to
start at a_j+2 on their seam-facing sides. A different fragment cannot
occupy the intervening forced-U positions.

Put `d_j=a_(j+1)-a_j`, for `0<=j<t`. Feasibility implies

```text
d_j<=2.                                           (36)
```

If d_j>=3, R_j and L_(j+1), on rows differing by two, both contain
columns a_j+2 and a_j+3. Their horizontal FF edges and the two forced
vertical paths between them form a six-cycle. This is a local cycle,
independent of all exterior roots.

If d_j=2, their sole common seam column is a_j+2. The vertex
`(a_j+2,y_0+3j+2)` is U and gives a real two-edge contact between R_j
and L_(j+1). Let u count these upward-two contact events.

## All Gap Suppliers Are Accounted For

For d_j<=0 define the gap vertex set

```text
Gamma_j = {(x,y_0+3j+2): a_(j+1)+1<=x<=a_j+1}.
```

For d_j=1 or 2 put Gamma_j empty. The exact gap count is

```text
g = sum_j |Gamma_j|
  = sum_j max(1-d_j,0)
  = t-(a_t-a_0)+u.                                 (37)
```

Here are the complete local restrictions needed for a global-isolate
count, rather than a window-isolate count.

* Both vertical neighbours of every vertex of Gamma_j are U. For the
  upper one use a diagonal F neighbour on L_j; for the lower one use
  a diagonal F neighbour on R_(j+1).
* Both endpoints of Gamma_j are U, by diagonals to L_(j+1) and R_j.
* The two vertices immediately outside Gamma_j on its own row are U.
  They have diagonally adjacent F vertices on those same two rails;
  the FF margins in (35) ensure the needed vertices exist.

Consequently the only possible preserved gap suppliers are

```text
(x,y_0+3j+2),   a_(j+1)+2<=x<=a_j,                (38)
```

which requires d_j<=-2. Any such F vertex supplies an actual four-edge
path from L_j to R_(j+1), through its upper and lower U neighbours.
There can be at most one such vertex per Gamma_j: two would give two
internally disjoint paths between the SAME two straight carriers and
hence a forced cycle. Its horizontal neighbours are therefore U too,
so it is an actual singleton carrier.

Let p count these singleton suppliers, and let z_Gamma count the
globally isolated vertices in the union of the Gamma_j. A singleton
supplier can prevent at most three of its row's gap vertices from
being isolates: itself and its two horizontal neighbours. The vertical
neighbours and the two external horizontal guards were proved U, so
no unlisted outside supplier is possible. Thus

```text
z_Gamma >= g-3p,
t <= (a_t-a_0)+z_Gamma+3p-u.                       (39)
```

All these gap sets are disjoint. Moreover they lie in the deep vertex
square `{2,...,A-2}^2`: their column bounds follow from (35), and their
row bounds from the last rail row y_0+3t+1<=A. Thus z_Gamma is disjoint
from the rooted-boundary theorem's next-ring isolate witnesses. The p
singleton suppliers are interior, not pure-boundary singletons. Their
r_1 units were not used in that theorem's R_pay either. These are actual
remaining resources, not returned dirty-donor credits.

The same diagonal arguments classify every row of the vertex window
`[L,R] x [y_0,y_0+3t+1]`: its only F vertices are the displayed L_j,
R_j, and the optional singleton suppliers in (38). In particular the
theorem did not obtain (39) by declaring the moving gap to be all U.

## The Actual Root Forest

Retain the u two-edge contact paths and the p four-edge singleton paths
just identified. Their internal vertices are disjoint and do not lie
on any rail. Different gaps have disjoint internal row ranges; within
one gap there is at most one event. The holes internal to these paths
have exactly their two displayed F neighbours. The singleton's two
additional horizontal neighbours are pendant leaves.

Let T_ext be the subgraph of H obtained by deleting the INTERNAL vertices
of these p+u paths. All rail carriers remain intact. Let m count the
components of T_ext meeting the selected rails, and let c_roots count
the components of the original H meeting them.

Contract those actual T_ext components and restore the selected paths,
suppressing their degree-two internal vertices and ignoring the pendant
leaves. This gives a forest on m root vertices with p+u edges. It has
exactly c_roots components, so

```text
p+u=m-c_roots <= m-1.                              (40)
```

The equality uses the proved path degrees: there is no additional
connection through a deleted internal vertex beyond these paths. This
contracts connected subgraphs of H, not whole rail banks joined by
virtual distance-three edges.

Combining (39) and (40) gives the uniform rooted-strip telescope

```text
t <= (a_t-a_0)+z_Gamma+p+2(m-1).                   (41)
```

For example, if all selected left rails are connected in T_ext and all
selected right rails are connected there, then m<=2, whether or not
the two sides are already connected to each other. The error in (41)
is at most two, not two per phase change. If both sides are in one
T_ext component, p=u=0 and (39) has no root error at all.

There is a simultaneous version. Take any nonempty collection of such strips
with disjoint gap sets and disjoint event-path interiors, and form ONE
T_ext by deleting all event interiors together. If its root-component
count is m, the same single forest count bounds the TOTAL p+u by m-1.
Summing (37)--(39) therefore proves

```text
sum_strips t
 <= sum_strips (a_last-a_first)+z_Gamma_total+p_total
      +2(m-1).                                    (42)
```

All coupons are assigned once to their actual gap vertex or singleton.
If the selected rails belong to at most 13 banks and each bank's selected
rails are genuinely connected in this COMMON T_ext, then m<=13 and the
entire root error is at most 24. This last connectivity statement is
a hypothesis about real paths; the bank count alone does not imply it.

When it fails, (40), not a fictitious m-component reserve, is what the
forest proves. In particular m can exceed the ambient c because the
selected paths were removed. Its excess has already been used in the
p+u bridges. It cannot also be offered as fresh c payment in (41).

## Exact Physical Strip Area

There are t left corridor stripe portions and t right portions with
complete packets in the cell window
`[L,R-1] x [y_0,y_0+3t]`. Their respective straight-cell lengths are

```text
ell_Lj=min(a_j,a_(j+1))-L,
ell_Rj=R-max(a_j,a_(j+1))-2.
```

Both are positive by (35). These formulas use intersections of the
actual rail FF intervals, not their hulls. The row classification above
shows that there are no other full packets in this window: all FF edges
there are on the displayed horizontal rails, and the additional gap
centers are singletons. Thus their exact packet count is

```text
X_strip = t(w-2)-sum_j |d_j|.                       (43)
```

This counts full packets in the specified window, not arbitrary paths
or straight cells whose leaves lie outside it. Missing external cap
regions have not been declared empty or paid.

The two families have t stripe levels apiece. Their baseline cost of
one carrier unit per stripe is compatible with the protected bank
allocation: `v_B-q_B>=a_B`, so a bank has at least one available baseline
unit per transverse stripe level. Multiple strips may use this fact
jointly only if they use disjoint named stripe levels in each bank, or
if their shared baseline is explicitly reallocated once. Merely having
at most 13 banks does not give fresh carrier units per strip occurrence.

Relative to the 2t baseline units, (43) gives exactly

```text
3X_strip/A-2t
 = t-(3/A)[t(A-w+2)+sum_j |d_j|].                  (44)
```

Consequently (41) bounds this excess by

```text
(a_t-a_0)+z_Gamma+p+2(m-1)
  -(3/A)[t(A-w+2)+sum_j |d_j|].                    (45)
```

This is a physical sloped-strip inequality uniform in arbitrary phase
drift, without a per-row error. It is not yet a constant-gap payment:
the signed END displacement a_t-a_0 is still present. Consecutive
panels of the same interface can telescope this displacement, but an
open interface can still have macroscopic displacement between its two
terminal regions.

## Triangular Loss Is Already Spent

Take a rigid ascending phase `a_j=a_0+j`, with t>=2. The two strip
rectangle capacities have widths `a_t-L` and `R-a_0-2`, both of height
3t, with a one-row transverse offset. Their missing stripe capacities
are exactly

```text
G_L=G_R=t(t+1)/2.
```

The rectangle overlap is

```text
Omega_strip=(3t-1)(t-2).
```

Indeed their common axial width is t-2 and their common transverse
height is 3t-1. The portion of missing packet capacity NOT already
discounting this overlap is therefore only

```text
3(G_L+G_R)-Omega_strip = 10t-2.                    (46)
```

This is less than `(10/3)A` since the window fits in the board. Thus
after the exact box-overlap discount, the extra shape slack has bounded
normalized value. There are not two further independent triangular
credits of order t squared to donate. If these two rectangles are only
subwindows of larger banks, (46) concerns just these subwindows and
does not assert that the entire banks are contained in them.

For this same rigid strip, (44) becomes

```text
3X_strip/A-2t = t-(3t/A)(A-w+3).                   (47)
```

When w=A-O(1), this is t-O(1), not O(1). The remaining linear cost is
precisely the terminal displacement a_t-a_0=t in (45). Triangle
discount and phase displacement must not both be counted as unused
payments of that same cost.

## A Literal Test Of The Triangle Shortcut

The obstruction in (47) occurs in an actual arbitrary-size feasible
family, not merely an assignment of strip dimensions. Let t>=2,

```text
n=3t+5, A=3t+4, L=2, R=A-2, y_0=1,
a_j=t+1+j, 0<=j<=t.
```

Preserve exactly the rails (35) and the two full boundary spines x=0
and x=A. No other vertices are preserved.

The supports of the horizontal rails are pairwise disjoint. Within
each family the row separation is three. Between families the only
close cases are L_j against R_j, and R_j against L_(j+1); their nearest
preserved vertices have Manhattan distance three. Every other pair has
row separation at least four. Each left rail support meets the left
spine support at exactly its endpoint leaf `(1,y_0+3j)`; each right
rail similarly meets the right spine at `(A-1,y_0+3j+1)`. There are no
cross-side attachments. Gluing these trees proves feasibility for every
t, with two nontrivial components and whatever actual isolates remain.

There are exactly two horizontal banks and two height-zero vertical
spine banks. The horizontal bank widths are both 2t-1; for t>=3 all
four banks are wide. Both rail families have genuine common roots
outside the seam, so m=2. Nevertheless the seam has
`p=u=z_Gamma=0`, and its strip excess in (47) is

```text
t-21t/(3t+4) -> infinity.                          (48)
```

This disproves the proposed LOCAL inference that two rooted banks and
their triangular overlap alone pay all strip packets from their 2t
baseline units plus an absolute error. It does not disprove payment
using the remaining global cap, boundary, and component resources.

In fact this family has ample global reserve. Directly,

```text
f=3t^2+9t+10,
K=n^2+4n-3f=15t+15,
f=T(t+1)-4t.
```

In particular K<n is FALSE. No counterexample to a low-K theorem, to
the global target, or to an unconditional one-orientation bound is
claimed. The family tests exactly the missing local inference, with
actual packets and actual connected roots.

## Residual After The Rooted-Bank Payment

There is an explicit combined certificate when the remaining packet set
really has the indicated strip decomposition. Work under K<n, since
K>=n already gives the target metric inequality. Suppose the packet set
of the unexposed positive-height wide banks is the disjoint union of the
selected strip packet sets, with no repeated named stripe baseline,
gap coupon, or event-path interior. Assume this collection is nonempty;
an empty remaining set needs only the existing rooted-bank payment.
These are substantive hypotheses, not consequences of the number of banks.

Let R_unused be their baseline carrier units left after allocating the
two t-unit families of each strip. It is nonnegative under this
nonreuse hypothesis. Set

```text
J_loss = sum_strips [t(A-w+2)+sum_j |d_j|],
R_rest = R_av-R_pay-z_Gamma_total-p_total >=0.
```

The last inequality follows from the private deep-isolate and interior
singleton allocation proved above. The root-boundary payment, the
exact area formula (44), and the SINGLE common root-forest count now
give

```text
3X_2/A <= K+6N+2(m-1)
          +sum_strips (a_last-a_first)
          -3J_loss/A-R_unused-R_rest.              (49)
```

To check the bookkeeping, first substitute the disjoint strip areas
in the metric note's (35). Their signed demands are the sum of (44)
minus R_unused. Apply the summed version of (45), which uses (42) and
only one 2(m-1) term. Finally remove z_Gamma_total+p_total from the
remaining available resources, leaving R_rest. No c coupon is used
to pay a deleted root component.

If each selected bank has connected roots in the common T_ext, the
nonterminal error in (49) is at most `6*13+2*12=102`. Thus even after
the desired bounded-bank and root-localization reductions, the exact
unproved terminal comparison is

```text
sum_strips (a_last-a_first)
 <= 3J_loss/A+R_unused+R_rest+O(1).                 (50)
```

No uniform proof of (50), or of the required strip decomposition and
root localization, is supplied here. This gives a finite constant for
the errors actually proved bounded, not a declaration that the terminal
phase sum itself has bounded cost.

## Remaining Global Obligation

The metric note already pays its exposed banks from R_pay with total
error 6N. The new deep gap isolates and interior singleton units in
(42) are disjoint from R_pay, and so could be used on the remaining
moving interfaces under a genuinely non-reusing strip decomposition.
The inter-root contacts then obey one actual forest-rank count, not
one assumed contact-component credit per bank.

Two uniform statements are still absent:

1. A decomposition of every remaining one-orientation wide-bank packet
   set into such interfaces and already paid regions, with no repeated
   stripe baseline or gap coupon. Two-cell one-pair rigidity does not
   itself provide this when one-cell corridors, fragments, or other
   strand types interrupt an interface.
2. A payment for the resulting signed terminal phase displacements and
   any unlocalized root-partition term. A bank not connected in the
   common T_ext does not automatically give extra ambient c units;
   (40) records precisely the bridge consumption. For open rigid
   interfaces the terminal displacement can be order n even with two
   connected banks, as the literal family demonstrates.

Equation (46) explains why the previously proved rectangle discount
does not supply that terminal payment again. Bounding the number of
banks bounds neither these displacements nor the missing connectivity
localization. No theorem paying them from R_av-R_pay has been proved
here. Thus the new uniform strip telescope is substantive but does not
close even the unrestricted one-orientation case.

Verification: ten explicitly specified strip completions were checked
in memory on sides 11 and 14. Eight were forests and passed the gap,
singleton, contact-rank, and exact packet-area identities; the two
completions with two bridges between the already rooted sides were
rejected by actual forced cycles. The rigid examples also passed the
triangle and global-count formulas. No optimization, search, board
above 14, or Lean command ran. Only this appendix was added to this note.

## Fragment Budget And Minimal Banks

Date: 2026-09-09. Read the current metric note through Root Hulls And
Interior Escape Transport, including its full-height terminal theorem,
and all of `PAPER_TERMINAL_TRANSPORT.md`. The claims below concern actual
carrier intervals and packet areas, not arbitrarily specified transport
loads. Only this appendix is new.

There are three rigorous deductions:

* The fragment units can be separated from the bulk allocation, with
  the protected-boundary adjustment made explicitly.
* A bank admits a monotone carrier-path cover with at most s_B+1 paths.
  Its s_B=0 case really has one carrier per level and two endpoint fronts.
* The coefficient-one reduction obtained by discarding corridors between
  those paths is false. A one-bank feasible family requires almost three
  normalized area units per fragment for that operation.

The unrestricted s_B=0 finite-bank case is not solved. Two endpoint
fronts alone do not bound their actual height-weighted metric terms.
An exact identity below distinguishes the bounded normalized front
length from that unpaid quantity. No unconditional global constant is
obtained.

## Return The Fragment Units Once

Retain `v_B=a_B+1+s_B` and the protected root count
`q_B=max(1,p_B)` from the preceding appendix. Define

```text
f_B = v_B-q_B-a_B = s_B-(q_B-1) >=0.               (51)
```

Thus the original v_B carrier units split exactly into

```text
a_B bulk units, q_B protected root units, f_B fragment units.
```

There are s_B EXTRA carrier units relative to a_B+1, but q_B-1 of them
may already be protected pure-boundary carriers. One can use all s_B
only by also charging any use of those protected units to the same
pool. Keeping both all q_B root coupons and all s_B fragment coupons
would double-count q_B-1 units.

Every small bank can indeed be paid from only a_B bulk units. Its
physical stripe j has sigma_Bj straight cells, and

```text
3 sigma_Bj/A <= 3W_B/A <=1.
```

Choose a_B different nonprotected actual carriers in the bank, which
exist by `v_B-q_B>=a_B`, and inject the a_B stripe labels into their
original units. Charge each stripe's actual normalized packet area
to its assigned unit. Every cell belongs to one stripe, every unit is
assigned to one stripe, and its charge is at most one. This is a bank
budget assignment, not a claim of a physical contact path from the
stripe to the carrier owning its coupon. In particular it does not
retain an additional bound by that chosen carrier's own FF length.

The exact small-bank refund in this allocation is

```text
R_small_a = sum_{B small} (a_B-3X_B/A) >=0.
```

All q_B protected units and all f_B fragment units remain unused.
Let

```text
F_frag_coupon = sum_B f_B,
R_av_a = b+c+r_1+sum_B q_B+F_frag_coupon+R_small_a.
```

For wide banks use the signed demand

```text
D_B_a = 3X_B/A-a_B.
```

The exact new division of the original K account is

```text
3X_2/A-K = sum_{B wide} D_B_a-R_av_a.               (52)
```

There is no separate -s_B or -f_B rebate left in D_B_a. Equation (52)
is bookkeeping, not a bound on its right side.

The rooted-boundary theorem still pays its exposed banks at the same
6N total error in this division. Its proof paid 2a_B, whereas
`max(0,D_B_a)<=2a_B` follows directly from W_B<=A and X_B<=a_B W_B.
It uses the same distinct boundary, isolate, and protected-root coupons,
not the f_B fragment units. Consequently the fragment pool really can
be retained after that payment. It must replace, not supplement, the
fragment contribution inside the old wide-bank baseline v_B-q_B.

## A Real Carrier-Path Decomposition

Let k_j be the number of carrier fragments on level j of a bank,
`0<=j<=a_B`. Thus all k_j>=1 and

```text
sum_j (k_j-1)=s_B.
```

Join two carriers on consecutive levels when their actual FF intervals
overlap. This is the bank graph itself. Between two fixed consecutive
levels, the overlap graph is a forest, and hence has at most
`k_j+k_(j+1)-1` edges. One proof selects a vertex with earliest right
endpoint in a hypothetical cycle. Both of its cycle neighbours would
have to extend to that endpoint from its left, contradicting disjointness
of the two intervals on their common level. Half-open FF intervals
remove any endpoint-touch ambiguity.

Connectedness of the bank implies that every level boundary has at
least one overlap edge. If e_B is the bank's total number of edges,
summing the two-level bound gives

```text
e_B <= a_B+2s_B-(k_0-1)-(k_(a_B)-1).               (53)
```

In particular its graph cycle rank is at most s_B. This is a statement
about the rail-overlap graph, NOT additional cycle credit in H.

Choose one overlap edge at every level boundary and orient it toward
the next level. Each carrier has at most one incoming and one outgoing
chosen edge. There is no directed cycle, and the chosen a_B edges
partition all v_B carriers into exactly

```text
v_B-a_B=s_B+1
```

vertex-disjoint monotone paths. Along a path the actual carrier
intervals overlap at consecutive levels. Its rail-activity region
has one interval per level and two monotone endpoint fronts. This is
an actual geometric decomposition of the carriers, not a choice of
abstract source-sink loads.

It is NOT yet a decomposition of all bank packets. An unchosen overlap
edge represents a real corridor between two carriers that may lie in
different paths. Those packets cannot be omitted or charged again to
their original bulk units without an allocation.

## The Cost Of Cutting Between Paths

One can quantify that loss rather than hiding it in O(s_B). At each
level boundary choose an overlap edge of maximum length. The overlap
intervals at that boundary are disjoint, so their total length is at
most W_B. If there are h>=2 such intervals, the discarded length is
at most

```text
W_B(1-1/h) <= (W_B/2)(h-1)
            <= (W_B/2)[(k_j-1)+(k_(j+1)-1)].
```

For h=1 the discarded length is zero. These independently chosen
edges still give the same valid s_B+1-path cover. If X_cut is the
total straight-cell area discarded, summing proves

```text
X_cut <= W_B[s_B-((k_0-1)+(k_(a_B)-1))/2]
       <= W_B s_B,
3X_cut/A <= (3W_B/A)s_B <=3s_B.                    (54)
```

The factor three cannot in general be reduced to one for this
carrier-path cutting operation. This remains true with only ONE
positive-height bank, as the following physical family shows.

## A Feasible Fragment-Cost Obstruction

For m>=1 set

```text
n=6m+2, A=6m+1, x_*=3m.
```

Preserve the full horizontal rows y=3j for `0<=j<=2m`, except delete
the single vertex `(x_*,3j)` on every odd j. Preserve nothing else.

Before these deletions, the supports of the three-spaced full rows
are disjoint trees covering the board. Deletion preserves the forest.
On a deleted row, all horizontal edges remain forced, so its two
preserved fragments are still joined through the deleted vertex.
Only its two vertical spokes are removed, creating two actual isolates.
This proves feasibility and the exact counts

```text
r=3m+1, c=4m+1, b=14m+4,
f=12m^2+9m+2, K=21m+6.                            (55)
```

There is exactly one rail bank, of width A and height 6m. Its level
multiplicities alternate `1,2,1,2,...,1`, so

```text
a_B=2m, s_B=m, q_B=1, f_B=m.
```

At each of its 2m level boundaries, the two overlap lengths are
3m-1 and 3m. A monotone vertex-disjoint carrier-path cover can retain
at most one edge there: one side of the boundary has only one carrier.
Thus EVERY such cover, not just the particular longest-edge algorithm,
discards at least

```text
X_cut >= 2m(3m-1),
3X_cut/A >= 3m-9m/(6m+1).                          (56)
```

Choosing the longer edge at every boundary attains this bound.
The deficit beyond the available m fragment units is
`2m-9m/(6m+1)`, which is unbounded. It cannot be put into an absolute
error per bank or per pair of banks.

This disproves a specific reduction: split banks into monotone carrier
paths, discard their cross-path corridors, and pay all discarded packet
area with one original unit per fragment. It does NOT disprove a
different interface decomposition that retains those corridors and
proves signed cancellation. Nor is this a low-K counterexample:
`K=21m+6>n`. The boundary and component reserves in (55) are real and
have not been erased. No abstract flow assignment is used in this test.

## The Minimal-Bank Front Theorem

When s_B=0 there is exactly one carrier interval
`I_j=[l_j,u_j)` per level, j=0,...,a_B. Connectedness now forces
EVERY consecutive pair to overlap: deleting its only possible edge
would separate the levels below and above it. Therefore

```text
X_B=sum_(j=0)^(a_B-1) [min(u_j,u_(j+1))-max(l_j,l_(j+1))].
```

The carrier activity diagram really has just two monotone fronts,
given by l_j and u_j, with horizontal steps between adjacent levels.
No monotonicity in x, no bound on those steps, and no common axial
FF cut are implied. Also the PACKET intervals of two consecutive
stripes need not overlap each other: each overlaps its bounding
carrier, not necessarily the next packet interval. Thus these two
activity fronts are not automatically two clean-strand interfaces.

Write w_j=u_j-l_j, and let TV(l),TV(u) denote total variation along
the two endpoint sequences. Using min/max identities gives exactly

```text
X_B = w_0/2 + sum_(j=1)^(a_B-1) w_j + w_(a_B)/2
      -(TV(l)+TV(u))/2,                            (57)
```

for a_B>=1. Since the source's cutwise identity is
`W_B+F_B=sum_j w_j-X_B`, this also proves

```text
2(W_B+F_B)=w_0+w_(a_B)+TV(l)+TV(u).                (58)
```

For a_B=0 use X_B=F_B=0 and W_B=w_0; (58) still holds. This is an
exact spatial relation between the fronts and the actual fragmentation
integral, not an assumed relation between arbitrary loads and coupons.

There is even a global normalized front-length bound. For ANY bank,
including fragmented ones, draw its rail-activity diagram with one unit
of transverse height per carrier level and its actual FF cut intervals
on that level. At an axial cut, its active levels form p_B(t) components.
Their top and bottom boundary edges give exactly 2p_B(t) axial boundary
segments. Therefore the total axial boundary length of these diagrams is

```text
L_front = 2 sum_B (W_B+F_B) = 2P_cut.              (59)
```

Under K<n, the metric note gives `K<=n-2` and `r>=(n+4)/3`, hence

```text
P_cut <= 2n-1/3+3K-r <= (14n-23)/3,
L_front/A <= 28/3-6/A <28/3.                       (60)
```

So a bound on normalized UNWEIGHTED axial front length is available
already, even without s_B=0. The open issue is whether the actual metric
terminal demands have that unit-load interpretation. They do not get
it merely from there being two fronts.

## The Actual Height Weights

The necessary weights can be read directly from the minimal bank, without
postulating any transport loads. Put

```text
delta_lj=l_(j+1)-l_j, delta_uj=u_(j+1)-u_j,
V_l_plus=sum_j max(delta_lj,0),
V_u_minus=sum_j max(-delta_uj,0).
```

Discrete summation by parts in the ACTUAL packet formula gives

```text
X_B = a_B w_(a_B)
      -sum_(j=0)^(a_B-1) (j+1)(delta_uj-delta_lj)
      -V_l_plus-V_u_minus.                         (61)
```

Indeed each stripe length is
`w_j-max(delta_lj,0)-max(-delta_uj,0)`, and
`sum_(j<a_B) w_j=a_B w_(a_B)-sum_(j<a_B)(j+1)(w_(j+1)-w_j)`.
This proves (61) and fixes both the boundary signs and their weights.

The normalized area formula multiplies the front motion at level j by
`3(j+1)/A`, not by a uniform `1/A`. With `l_j=L` and `u_j=u_0+j`, the
unweighted motion is a_B, but its sum with the forced height weights is
`a_B(a_B+1)/2`. It can have order A squared before division by A.
The increasing rails in the preceding literal moving-seam family realize
exactly this geometry in a feasible set; these are not assigned port loads.

Likewise that family has s_B=0 in EVERY bank, four banks in total, and
one actual rigid seam with terminal displacement t in (47). Its area
correction after triangle overlap is only O(1) in normalized units.
Thus fragment count alone does not make that packet-derived terminal
term bounded. The family has ample unspent global resources, so this
observation does not refute a successful boundary/root payment for the
term, or the proposed bound on what remains AFTER such a payment.

Equation (60) cannot simply be substituted for the height-weighted term
in (61), or for the unscaled coordinate displacement in (50). Such a
substitution would drop the actual multiplicity with which a front
segment enters the packet-area account. Nor may the variation losses
already used in (57) be added once again as transport refunds.

## Exact Failure Of The Proposed Reduction

The fragment reallocation itself is valid: bulk can start with a_B units,
the f_B remaining fragments can be reserved once, and the exposed-bank
theorem keeps its existing error. The carrier geometry also gives the
proposed O(1+s_B) number of monotone CARRIER paths. Neither step gives
the required coefficient-one packet/interface allocation:

1. The natural carrier-path cover omits cross-path corridors. Its sharp
   worst-case cost approaches three, not one, per fragment, even in one
   actual bank. The explicit forest (55)--(56) rules out hiding that gap
   in O(number of wide banks squared).
2. In the s_B=0 case, two activity fronts are proved, as are their exact
   signs in (61). But the actual area terms have height multiplicities.
   No allocation cancelling those weighted terms through the other
   banks, or paying them from the available boundary and root coupons,
   has been established. Unweighted normalized front length is a
   different quantity, despite its bounded value in (60).

A decomposition retaining all cross-path packets and controlling the
geometric weighted signs could still succeed. This pass does not prove
it, does not prove the unrestricted s_B=0 finite-bank theorem, and does
not prove `P(3k+2)<=T+C`. It also supplies no counterexample to those
global claims. The exact failure is the demonstrated cutting coefficient
and the remaining height-weighted terminal payment, not a missing
algorithm for choosing the carrier paths.

Verification: direct in-memory checks used the diamond banks on sides
8 and 14 and the rigid two-root seam forests on sides 11 and 14. They
verified forest feasibility, the original counts, the edge/path-cover
bounds, discarded corridor lengths, the protected fragment split, and
both minimal-bank front identities. The arbitrary-size obstruction is
the explicit construction and counting proof above. No optimization,
search, board above 14, or Lean ran. Only this appendix was added.
