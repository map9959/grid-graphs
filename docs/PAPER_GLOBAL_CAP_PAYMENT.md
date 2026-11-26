# Global Cap Payment

Date: 2026-09-08. Paper continuation; no search, optimization, or Lean.

## Outcome And Inputs

Current review status: independent read-only audits covered the complete
note through the corrected flat-packet appendix (original line 1657).
They found a gap in the original arbitrary-isolate flat-packet transfer;
that claim is withdrawn. The corrected version explicitly requires all
four outer packet anchors to be J_3 and passed re-review. The isolate-free
packet theorem was unaffected. Historical review-status paragraphs below
refer to earlier snapshots.

New reviewed constant-gap cases include backed double folds and the
specified flat singleton zero-corridor packets, with the separate isolate
hypotheses stated at their proofs. A broader isolate-free coefficient
result gives T+floor(k/3)+4 when one- and two-pair through strands are
eligible; this is not an unconditional improvement. Neither the global
constant bound nor the full eligible-one-pair case is closed.

The unconditional `P(3k+2)<=3k^2+7k+C` is NOT proved here. The unrestricted
isolate-free case remains open, including the case where every through
strand is an eligible one-pair strand. No counterexample to the desired
bound is obtained.

The complete endpoint/cap continuation of
[PAPER_DUAL_UPPER_RESEARCH.md](PAPER_DUAL_UPPER_RESEARCH.md), including its
final audit status, and the U1/U3/L2 checkpoint were read. The arguments
below use its physical definitions. In particular, `p` here is the number
of interior R corridors, NOT the checkpoint's pure-carrier count. Write
`p_B` for a number of pure boundary carriers instead.

The reviewed global inputs remain

```text
A=n-1, K=r+b+c, S=K-4+3C_o/4,
A^2=3X_2+Q_exc, Q_exc<=10K.
```

A genuine length allowance with `X_2<=A L` and `3L<=K-2+D` gives
`3(f-T)<19+D` on `n=3k+2`. In particular `D=0` gives `f<=T+6`.
Exceptional area is already paid. The initial deductions assume `z=0`;
later appendices state separate transfers using the isolate-routing proof.

The substantive additions are a joint pure-interval contact count, its
precise forest interpretation, an explicit accounting of unused end and
join-gap lengths, a parallel-carrier consequence for eligible one-pair
strands, and a proved obstruction to a natural boundary exchange. None
supplies the missing global payment by itself.

## Two Contacts Per Straight Cap

Consider a blocked immediate cap with `h=2`, corridor pointing east, and
junction `(1,y)`. Suppose its leaf is west, the pure-boundary-spine case.
Its boundary footprint is

```text
(0,y-1), (0,y), (0,y+1), (0,y+2), all preserved.
```

The first straight corridor cell is `(2,y)`. Its two deleted leaves
force the horizontal FF edges

```text
(2,y-1)--(3,y-1), (2,y+2)--(3,y+2).
```

Consequently the two holes

```text
(1,y-1), (1,y+2)
```

are actual contact holes. Each joins the pure boundary carrier to a
horizontal inward carrier. These are forced primal paths, not UU mirrors.
The holes are U by the diagonal obstruction. Their two opposite preserved
neighbours are the displayed boundary and inward vertices.

This proof uses only the first straight cell, so the positive corridor
need not have two straight cells. The two inward carriers are distinct:
otherwise the two contact paths and the boundary carrier would give a
cycle in the actual contact forest.

## Joint Interval Count

Fix one side and one actual pure carrier interval I on that side. Select
any of its straight `h=2` blocked caps. Write their junction row labels as

```text
y_1<...<y_N.
```

Their assigned six-cell sets are disjoint and have identical two-column
projections. Therefore `y_(i+1)-y_i>=3`. Each cap contributes contact levels
`y_i-1` and `y_i+2`. Two contributions coincide precisely when consecutive
cap labels differ by three. No contact is used by three caps.

Partition the labels into maximal runs of successive differences three,
and let s_I be the number of nonempty runs. For an empty selection put
`N=s_I=0`. The number of DISTINCT forced contacts is exactly

```text
q_I=N+s_I.                                          (1)
```

Proof: a run of t caps contributes the t+1 levels
`y_first-1,y_first+2,...,y_first+3t-1`. Different runs have disjoint level
sets. Thus (1) counts physical contacts jointly, retaining their sharing.

If I has ell preserved vertices, also

```text
3N+1<=ell, if N>0.                                  (2)
```

Indeed the first-to-last footprint contains at least `3(N-1)+4` vertices.
The footprint is contained in I. This bounds the multiplicity that one
interval can support; it does NOT give one fresh interval credit per cap.

For a fixed side, contacts from distinct pure intervals cannot coincide,
since their boundary F endpoints would coincide. Hence both counts sum
over intervals. For simultaneous four-side use, first retain only caps
whose two contact levels, in their side coordinates, lie in `[2,n-3]`.
Call these regular caps. Their contact holes are distinct between sides:
on the left they have coordinates `(1,j)`, `2<=j<=n-3`, and the rotated
sets on the other sides are disjoint. Their inward F neighbours are not
boundary vertices.

At most four cap positions per side fail this regularity test. The possible
junction labels are `1,...,n-3`; failure requires `y<3` or `y>n-5`.
Thus omitting all nonregular caps costs at most 16 caps, uniformly in n.
This deliberately loose corner allowance avoids any cross-side token reuse.

Writing N_B for all selected regular caps and s_B for their total run
count gives the joint, four-side physical lower bound

```text
q_selected=N_B+s_B.                                 (3)
```

This removes the hole-only obstruction: a pure footprint supplies contact
paths even when it supplies no boundary hole. It does not yet pay those
paths from K.

## What The Forest Actually Forces

Use the actual contact forest on all r carriers. Its component count is c
because `z=0`. Let B be the set of all pure boundary carriers, of size p_B.
Delete these carrier vertices and their incident contact edges. Let d be
the number of components of the remaining forest, including isolated
carrier vertices. This d is NOT the ambient forced component count c.

Contract each of those d components. Retain the p_B boundary vertices and
only the selected contact edges from (3). The result is a forest: all
operations were deletion or contraction in a forest. In particular two
selected contacts cannot connect the same pure interval to the same
remaining component. If gamma is the number of components of this
contracted graph, retaining its isolated vertices, then exactly

```text
N_B+s_B=p_B+d-gamma.                                (4)
```

Thus for nonempty selections `d>=N_B+s_B-p_B+1`. For a SINGLE pure
interval the N+s_I selected contacts meet N+s_I different components
after all pure carriers are removed. Multiple intervals must instead be
handled by (4): a remaining component can meet several different pure
intervals without creating a cycle.

This is a genuine nonlocal restriction on the inward forest. It excludes
any proposed realization that reconnects two of one interval's selected
inward roots using only nonpure carriers. It is stronger than counting
cap footprints alone.

However, its apparent component payment cancels against the splitting
caused by deleting B. To see this precisely, let q_BN be the number of
contacts with exactly one endpoint in B, and q_BB those with both endpoints
in B.
The full contact forest has r-c edges; its remainder has
`r-c-q_BN-q_BB` edges and `r-p_B` vertices. Therefore

```text
d=c-p_B+q_BN+q_BB.                                  (5)
```

Large d can be created by the very boundary contacts being counted.
Substituting (5) in (4) does not give a new linear reserve in c. In
particular, paying every selected cap by a different inward component
would spend components that are not independent ambient components.
There is no proved global relation between these deletion components and
the unspent terms of B_end.

## Unused Length Located Explicitly

This section allows arbitrary eligible strand lengths, still with z=0.
Fix a maximum eligible matching and the resulting monotone positive-corridor
chains. Let V_open consist of all J_3 ends of positive corridors not used
by a selected join. Include exterior-corridor junction ends if unselected.
An actual exterior port has axial inset zero and need not be listed.

For v in V_open use the outward axial inset h(v) from the dual note.
For a selected join e, orient its two corridors in the chain's increasing
axis and let delta_e be the positive axial displacement from its incoming
junction to its outgoing junction. Eligibility proves delta_e>=1.

The complete chain partition gives the physical formula

```text
Delta_len = sum_(v in V_open) h(v)
            + sum_(selected e) (delta_e+1).         (6)
```

Proof: the last straight cell before the join is one cell before the
incoming junction; the first straight cell after it is one after the
outgoing junction. Their intervening missing labels number delta_e+1.
All these gaps are distinct within the ordered chain. The two outer
missing intervals are precisely its unjoined-end insets. Sum this literal
partition over chains. Distinct chains have separate length allowances;
no assertion about disjoint physical projections between chains is needed.

For a one-pair join delta_e is one or two, so its gap is two or three.
For a join along a k-pair strand's main axis, the gap is k+2. For an odd
strand joined along its transverse axis it is two.

In particular the old blocked-end estimate can be strengthened to

```text
Delta_len >= sum_(blocked positive interior v) h(v)+2nu,             (7)
```

with additional nonnegative insets for all other unjoined junction ends.
The sums in (7) use disjoint slots of (6). They do not reintroduce the
insets at selected seam junctions.

This is useful for evaluating an actual geometry, but its scale matters:
the extra payment in the global certificate is `6nu/A`, not `2nu` or
`3nu`. An O(A)-long seam can have an O(A) cap demand while these constant
gaps supply only O(1) normalized payment.

Nor does optimizing the matching produce another reserve. A selected
join replaces endpoint insets of total `A+delta_e+1` by a gap of
`delta_e+1`. It lowers Delta_len by A. The simultaneous three-unit
matching change in B_end cancels it after multiplication by 3/A.

## Seam Placement And Carrier Insets

For a rigid one-pair seam whose corridors each contain at least two
straight cells, the reviewed displacement is

```text
v_(i+2)=v_i+(sigma,3), sigma in {-1,1},
```

after rotation. Thus a seam confined to d consecutive axial columns has
at most `2d-1` links: its even-indexed junctions alone occupy
`floor(m/2)+1` different columns for m links. This is an actual placement
restriction, not a rank argument. A long seam must leave any fixed-width
boundary strip. This assertion is not extended to seams with one-cell
corridors, for which the two-cell rigidity hypothesis has not been proved.

Crucially, leaving that strip concerns the SEAM end of a corridor. A
blocked cap can still be near the opposite boundary. Most seam-end
insets disappear into selected joins as in (6). The placement statement
alone therefore does not force the required unused length.

There is also a parallel-carrier consequence valid with only positive
corridors. Every eligible one-pair strand joins carriers of the common
corridor axis, and both participating carriers are nonsingletons.

For proof use the short-pair normal form: bend cells `(0,0),(1,0)`, F
corners `(0,0),(2,1)`, anchors `(0,1),(1,-1)`. In the west/east case
the first straight cells force FF extensions from `(0,0)` to `(-1,0)`
and from `(2,1)` to `(3,1)`. In the north/south case they force FF
extensions from `(2,1)` to `(2,2)` and from `(0,0)` to `(0,-1)`.
These exhaust the eligible possibilities. Forbidden carrier turns then
fix the claimed axes.

Consequently, when all P through strands are eligible one-pair strands,
the reviewed parallel-knight inset lemma gives

```text
2(nr-f)>=nP.                                        (8)
```

There is no singleton-axis ambiguity in these P uses. But the factor two
in (8) still cannot be removed: different knight edges may use the two
bend slots of one carrier end. This inequality measures real carrier
length deficits, not a new copy of bend/contact credit. No allocation of
its endpoint slots simultaneously with (3) and (6) is established here.

## A Boundary Exchange That Fails

There is an exact obstruction to the tempting count-neutral operation
"delete one pure-spine center and promote its inward contact hole."

Suppose `(0,j-1),(0,j),(0,j+1)` are preserved in a straight pure boundary
carrier, with j an open-side level, and `(1,j)` is a contact to an inward
preserved vertex. Put

```text
F'=(F minus {(0,j)}) union {(1,j)}.
```

The next-ring vertices `(1,j-1),(1,j),(1,j+1)` are originally U by the
diagonal obstruction. After deleting `(0,j)`, the entire path

```text
(1,j-1)--(0,j-1)--(0,j)--(0,j+1)--(1,j+1)
```

remains forced: each of its four edges has a preserved endpoint other
than the deleted vertex. Promoting `(1,j)` adds edges to both ends of
this path. These six edges form a cycle. Thus F' is infeasible, regardless
of all distant connections or of whether F is maximum.

The argument applies wherever the contact level is internal to its pure
interval. It does not rule out deleting an interval endpoint, deleting
several centers, or a distributed count-balanced exchange. It does rule
out using this particular one-for-one shift to normalize repeated cap
contacts in a maximum configuration.

More generally, the exact single-promotion test in a feasible F is simple.
For u in U, promotion adds just the edges from u to its U neighbours.
Contract the existing H components. Promotion is feasible if and only if
the component of u and the components of those U neighbours are pairwise
distinct. Otherwise there is a loop or two parallel star edges after
contraction; if they are distinct the new edges join trees as a star.
Maximality can forbid such a promotion, but does not specify where its
obstructing existing path runs. No locality or beneficial exchange follows
without a further proof. No maximum-specific normalization is assumed here.

## Remaining Failure

The reviewed payments for non-immediate caps and the h=3, h=4, and
perpendicular-leaf h=2 cases remain intact. New equation (3) describes
the joint physical contacts of the straight h=2 boundary exception, and
(4) constrains their inward connectivity. It does not convert the deletion
component count d into unused bank credit. Intermediate-depth immediate
caps with `5<=h<A/3` also still lack a universal payment.

The next missing geometric implication must link that inward connectivity
to actual seam placement and lengths: either repeated pure-interval
contacts force unspent rank/strand resources, or their routed corridors
lose enough total length after all selected joins. No such implication is
proved, even with every through strand one-pair eligible. Assuming that
distinct deletion components cost distinct c units is precisely the
failure in the most direct attempted closure.

Equations (6)--(8) locate extra physical resources but do not assert that
they cover the residual. The sufficient exact budget is not promoted to
a theorem about all feasible sets. The unconditional paper bound remains
`P(3k+2)<=T+floor(k/2)+1` for k>=3, as recorded in the checkpoint.

Only this new note was written. Existing notes and concurrent changes were
preserved. No finite configuration was searched or checked, no optimizer
was run, and no Lean command was run. The deductions above are paper
proofs, not independently reviewed or formalized results.

## Continuation After Independent Audit

The user reports independent audit of the preceding prefix. This appendix
is new and has not received that audit. The prefix is preserved verbatim.

There IS a quantitative improvement from combining the two length
inequalities, rather than using the parallel-carrier tax only to bound P.
For n=3k+2, k>=3, the following paper theorem is proved below:

> If z=0 and every through strand is an eligible one-pair strand, then
> `f<=T+floor((k+10)/3)`.

This improves the asymptotic excess coefficient from k/2 to k/3 in this
class. It is not a constant-gap theorem and not an unrestricted upper
bound. The theorem also holds when each through strand either is an
eligible one-pair strand or has at least four knight pairs, with the
longer strands otherwise unrestricted.

There is a stronger weighted conclusion, retaining actual b and c. In
either class, `b+4c>=2n/3+8` implies `f<=T+3`. Thus the new elimination
also closes some component-heavy configurations outside the earlier
large-(b+c) regime. All these claims have geometric inputs proved above
or in the reviewed dual note; none assumes exhaustion of blocked caps.

## Exact Elimination Of Contact Loss

Continue with z=0, but for now allow arbitrary through-strand lengths.
Write d_MM in full to distinguish it from the deletion-component count
in (4),(5). Let theta be the number of parallel-carrier knight edges for
one fixed assignment of singleton axes. Let nu be a maximum matching in
the eligible-strand graph, allowing all eligible lengths.

The reviewed physical length inequalities are

```text
X_2/A <= g-nu,
f/n   <= r-theta/2.                                 (9)
```

The first can be weakened from `g_+-nu` by retaining the zero corridors.
The second is the carrier-inset lemma. Both apply to the SAME actual
configuration. We will add these two valid inequalities with their
displayed coefficients; no extra copy of their inset slots is asserted.

The isolate-free contact and strand equations imply

```text
g = r-1-J_4-(t_M+d_MM+q_bd)/2,

2P = 2r+2c-b+2+t_M/2+t_0-3C_o/2-d_MM.              (10)
```

For the second equality, substitute the first into

```text
S=3g+1+3J_4+3(c-1)+2t_M+t_0+3delta_bd/2+d_MM/2-2P,
delta_bd=2+q_bd-C_o/2,
S=r+b+c-4+3C_o/4.
```

In particular d_MM must not be discarded before elimination. Solving
(10) for it and substituting back into g gives exactly

```text
g = P+b/2-c-2-J_4-3t_M/4-t_0/2+3C_o/4-q_bd/2.     (11)
```

This is where the full contact/rank account is used: the raw r allowance
is replaced by a P allowance together with actual boundary and component
terms. Pendant contact loss cancels, rather than appearing as an unpaid
error in the final estimate.

Define the measurable geometric surplus

```text
Gamma = J_4+nu+theta/2-P.                           (12)
```

Adding (9) after using (11) now proves

```text
X_2/A+f/n <= K-b/2-2c-2+3C_o/4
             -3t_M/4-t_0/2-q_bd/2-Gamma.           (13)
```

Unlike a bound of the form `e<=constant*P`, (13) has eliminated BOTH P
and the blocked-end count whenever Gamma>=0. Its two left-hand terms
each have leading size n/3. This is the source of the new coefficient.

## A Weighted Metric Theorem

Use the exact area and global ledgers in (13):

```text
3X_2=A^2-Q_exc, 3f=n^2+4n-K.
```

Multiplying (13) by three and collecting terms gives

```text
(3+1/n)K+Q_exc/A
  >= 2n+9+3b/2+6c-9C_o/4
     +9t_M/4+3t_0/2+3q_bd/2+3Gamma.                (14)
```

Consequently, using only the already reviewed `Q_exc<=10K`,

```text
a_n K >= 2n+9+3b/2+6c-9C_o/4
          +9t_M/4+3t_0/2+3q_bd/2+3Gamma,
a_n=3+1/n+10/(n-1).                                (15)
```

Equation (15) is an inequality proved from two distinct metric bounds,
not another form of the exact excess ledger. There is no endpoint-
exhaustion premise. The unspent boundary and component terms remain
with their correct signs.

For every feasible board here, b>=2: the boundary cycle of H must be
missing an edge, and that edge has two distinct U endpoints, each of
boundary deficiency at least one. Also c>=1 and C_o<=4. Therefore
Gamma>=0 implies

```text
a_n K >= 2n+9.
2n+9-a_n*(2n/3) = 5(n-5)/(3(n-1)) > 0.             (16)
```

For n>=11 this proves `K>2n/3`. Substitution into
`3(f-T)=n+10-K` gives

```text
f-T < n/9+10/3 = k/3+32/9,
f <= T+floor((k+10)/3).                             (17)
```

The last floor follows by the three residue cases of k modulo three.
This is an actual k/3-coefficient upper theorem whenever Gamma>=0.

Retaining b,c in (15) gives a useful constant-gap subcase. If Gamma>=0
and `b+4c>=2n/3+8`, then, since C_o<=4,

```text
a_n K >= 2n+(3/2)(b+4c) >= 3n+12,
a_n*n = 3n+11+10/(n-1) <= 3n+12.
```

Hence K>=n and f<=T+3. This criterion need not require
`b+c>=2n/3-1`; the coefficient four on c is a genuine benefit of the
joint elimination. It still does not cover all low-(b+c) configurations.

For arbitrary z=0 sets put `E_pair=max(0,-Gamma)`. The same proof gives

```text
K > 2n/3-E_pair,
f-T < k/3+32/9+E_pair/3.                            (18)
```

Indeed (15) has right-hand side at least `2n+9-3E_pair`, whereas
`a_n*(2n/3-E_pair)` is smaller by the positive margin in (16) plus
`(a_n-3)E_pair`. This is a parameterized consequence, not a claim that
E_pair is bounded for arbitrary strands.

## Classes With Nonnegative Surplus

In the all-one-pair eligible class, (8) gives theta>=P, and the eligible
graph's path/even-cycle matching gives nu>=P/2. Thus Gamma>=J_4>=0
(in fact J_4=0 in this class). This proves the first theorem in (17).
The contact or inset resources of the remaining blocked caps need not
be assumed paid to apply it.

There is a useful extension. Let N_1 count eligible one-pair through
strands and suppose every other through strand has at least four pairs.
The reviewed thin-zigzag lemma supplies at least k_s-2 parallel knight
edges internal to each such longer strand. These edges are disjoint
from the one-pair strands' knight edges, so singleton axes can be chosen
as in that lemma to give

```text
theta >= N_1+sum_other (k_s-2),
nu >= N_1/2.
```

There is no axis conflict: the one-pair participating carriers are
nonsingletons with forced axes, while the internal-use construction only
chooses axes of singletons consistently. It follows that

```text
Gamma >= J_4+(1/2)sum_other(k_s-4) >=0.              (19)
```

Thus (17) and the b+4c criterion apply to this mixed class with no bound
on either strand count. Purely long-strand classes may already satisfy
the stronger T+6 theorem in the dual note; (19) concerns mixtures with
arbitrarily many one-pair strands.

More generally, distinguish eligible one-pair strands from all others.
The same argument bounds E_pair above by the positive part of

```text
N_(ineligible one-pair)+N_2+N_3/2
  -(1/2)sum_(k_s>=5)(k_s-4)-J_4.                   (20)
```

Four-pair strands cost zero in this bound. Additional eligible joins or
parallel knight edges can improve it. No bound on the positive part in
(20) has been proved universally; in particular this does not dispose
of mixed or same-facing two-pair strands, or isolates.

## Cap Contacts Leave Unused Carrier Slots

The cap contacts also strengthen the carrier tax jointly, not just through
the deletion-component count. Select N_B regular straight boundary-spine
caps as in (3). Then for the same theta as in (9),

```text
2(nr-f) >= n*theta+4N_B.                            (20a)
```

Proof: orient a cap east with junction `(1,y)`. Its two immediate pendant
bends are `(1,y-1)` and `(1,y+1)`, with F corners `(2,y-1)` and `(2,y+2)`.
The first straight cell forces horizontal FF extensions to column three,
so these are left carrier endpoints with outward inset exactly two.
Each displayed bend is a terminal bend, not a member of a knight pair.
It therefore leaves one of that endpoint's two inset slots unused by
all parallel knight edges. The cap supplies two unused slots of weight
two, for a total of four.

Different caps have disjoint assigned bend cells. If adjacent caps share
a contact and its inward carrier endpoint, they use its two DIFFERENT
bend slots. This is precisely the sharing counted in (1), not a second
use of one slot. Slots on different sides are also distinct for the
regular selection. All participating carriers are nonsingletons, so
their assigned axes are forced. Add these unused weights to the knight
edge weights in the original proof of (34) in the dual note. The total
available two-slot weight is `2(nr-f)`, proving (20a).

Thus (13)--(15) can be strengthened by replacing Gamma everywhere with

```text
Gamma_B=Gamma+2N_B/n.                               (20b)
```

For example the right side of (15) gains `6N_B/n`. This is a quantitative
nonreuse statement linking caps, contacts, and the carrier tax. It does
not treat the deletion components as fresh c credits.

The scale again explains its limitation. By (2), summing over side
intervals gives `3N_B<=4(n-1)` even before subtracting interval-end
allowances. Therefore `2N_B/n<8/3`. The entire new normalized carrier
credit is bounded, not linear in the number of caps. The small inset
at a boundary-rooted carrier end cannot pay a full unit per cap.

## Scalar Feasibility At Linear Excess

The joint elimination is not merely too weak by an additive constant.
There is a rational/integer family satisfying the numerical inputs above
with excess exactly k/3. This is a COUNTERCHECK TO SCALAR ELIMINATION,
not a feasible grid construction or a counterexample to constant gap.

Take k a positive multiple of three, n=3k+2, and assign

```text
r=2k+3, b=8, c=1, C_o=4,
P=2k-2, g=2k+2, p=2k-2, q=4, h=0,
J_3=4k, J_4=0, t_R=4, w=4,
t_M=t_0=q_bd=d_MM=delta_bd=g_zero=0,
M=8k, e_1=4k+4, theta=P,
nu=k-1, sigma_match=k-2,
u_root=3, u_int=2k-2.
```

The eligible graph can abstractly be one path of P even edges, with all
other junctions eligible-isolated. Give its first vertex an exterior
corridor and every other path vertex an interior corridor to a new
terminal cap. Add three exterior corridors with terminal-cap junctions.
This R-plus-through graph is a tree. It verifies the full rank,
matching, and endpoint identities; it does not assert a grid embedding.

The remaining numerical quantities are

```text
K=2k+12, S=2k+11, f=T+k/3,
Q_exc=20k+4,
X_2=3k^2-14k/3-1,
L=g-nu=k+3,
Delta_len=44k/3+4,
B_end=k-1, Gamma=0.                                (21)
```

Both ledgers hold exactly. In particular

```text
3X_2+Q_exc=(n-1)^2,
3f+K=n^2+4n,
n(r-P/2)-f=20k/3+8 >=0,
Delta_len >= 2u_int+2nu.
```

Thus the parallel-carrier tax, mandatory blocked-cap insets, selected
join gaps, and the full matching/rank budget all admit this linear
excess. The available constant-sized gap and inset allowances leave
O(k) spare cells, which is only O(1) payment after division by A.

The joint pure-interval count does not exclude the ray either. Assign
N_B=2k-4 regular boundary-spine caps to two opposite pure intervals,
k-2 caps per interval in one run each. Then

```text
s_B=2, q_selected=N_B+s_B=2k-2 <= r-c=2k+2.
```

The length requirement is also consistent at the scalar level: two
side intervals of length 3k-4 each can accommodate k-2 regular footprints
by (2). Together with two intervals of length n their total length is
`12k-4=4n-b-C_o`, the preserved boundary count of the ray. The other two
blocked caps are left outside the selected boundary class. No boundary
word is asserted to realize the port types in (21); scalar interval
capacity does not encode the local distinction between zero-length and
positive exterior corridors.

Numerically set p_B=4, q_BN=r-c, q_BB=0. The deletion-component count
in (5) is then `d_B=r-4=2k-1`, and (4) holds with gamma=5. The selected
contacts can abstractly attach distinct inward vertices to each of the
two side intervals; the four remaining contact edges can connect these
five selected-contact components into one tree. This satisfies the
joint contact-forest inequality, not any unproved spatial routing rule.

Even the joint unused-slot strengthening (20a) survives, since

```text
n(r-P/2)-f-2N_B=8k/3+16 >0.                         (22)
```

For k>=6 the scalar straight-cell count is also large enough to give
every corridor at least two straight cells. The seam's necessary
transverse span and axial drift fit within the square dimensions.
These are necessary numerical checks only: no simultaneous placement
of the corridors, carriers, caps, and contacts has been exhibited.

This family shows that the stated scalar counts and lower bounds cannot
prove a constant excess, or improve the leading k/3 coefficient. Any
such improvement needs an additional geometric inequality beyond this
retained scalar system, not a different linear combination of just these
inputs. This is not a feasibility certificate for every local rule in
the dual note; in particular exterior port placement has been relaxed.

## The Sharpening Still Needed

The unsuccessful closure is now quantitative. In the ray (21), there
are Theta(k) boundary-rooted inward carriers and Theta(k) parallel knight
pairs. Almost all contact-forest edges can be spent attaching those
carriers to the pure boundary. The scalar data allow large carrier
insets to be assigned predominantly to selected seam ends, rather than
unused ends of the joined corridor chains. Realizability of that
simultaneous assignment is exactly what has not been established.

To improve (17), one must prove that these two purported saturations
cannot coexist in the physical grid with small b,c. A suitable new
statement would force additional unused corridor length or additional
carrier deficit beyond the parallel-pair tax when many cap-rooted
components meet one moving seam. Distinct deletion components alone do
not force this. Nor can their many contacts simply be charged again to c.

The new result is therefore a real coefficient improvement with P and
u_int eliminated in the stated classes, plus a precise obstruction to
closing by scalar LP elimination alone. The arbitrary metric target
`3X_2<=A(K+C)` and the unconditional constant-gap theorem remain open.
No maximum-specific exchange or normalization was used.

Verification: an attempted optional SymPy arithmetic check was unavailable
because SymPy is not installed. A standard-library exact-rational check
then passed 28 scalar identity/inequality checks on synthetic budget
parameters. A second pass checked the threshold, floor arithmetic,
weighted criterion, and cap-slot slack with 1,094 further exact-rational
checks. These instantiated no grids, ran no optimization, and supply
no geometric evidence. All uniform claims have their paper proofs above.
Only this appendix was added; no previous note text, other files, or Lean
artifacts were changed.

## Planar Placement And Arbitrary Longer Strands

This is a further append-only continuation. The preceding text is
unchanged. The new inputs read were the complete "Simultaneous Donor
Allocation" continuation in PAPER_ISOLATE_ROUTING_UPPER.md and the
distance-four and separation-seven continuations in
PAPER_GLOBAL_METRIC_UPPER.md. The donor allocation is an independently
audited claim only if that separate audit succeeds; at the time of this
continuation the user reports its audit underway. None of the proofs
below depends on its success.

No unconditional constant-gap proof is obtained. There is a new, broader
coefficient theorem:

> On n=3k+2, k>=3, suppose z=0 and every ONE- OR TWO-PAIR through strand
> is eligible. All other through strands may have arbitrary lengths and
> arbitrary endpoint orientations. Then
> `f<=T+floor(k/3)+4`.

In particular, noneligible three-pair strands no longer require
orientation restrictions for this coefficient theorem. They are paid by
their actual contact-type edges in the combined count. Noneligible
two-pair strands still leave a half-unit each at this scale. None of
this pays the full coefficient needed for a constant bound. The new
theorem also does not automatically cover one-pair strands incident to
knots, exterior bend ports, or zero corridors, and is stated only for z=0.

The attempt at the main constant target is recorded first: a precise
planar ordering lemma, how it applies to cap roots, and why the evident
seam order does not violate it. No alternating sequence on two different
seam banks is treated as if it lay on one disk boundary.

## The Planar Ordering Test

Here is the planar fact that a cap-placement proof may safely use.
Let Omega be a closed topological disk in the square. Suppose disjoint
connected subgraphs A and B of the physical forced forest lie in Omega
and meet its boundary at distinct points a_1,b_1,a_2,b_2 in that cyclic
order. Then this configuration is impossible.

Proof: take simple paths inside A and B joining their respective two
points. They are vertex-disjoint. A simple arc joining a_1 to a_2 in a
disk separates b_1 from b_2, so the second path must meet it. If the
first path touches the boundary elsewhere, take a sufficiently small
perturbation into the disk, still disjoint from the compact second path.
This gives the same contradiction. This is the usual disk separation
argument for actual paths, not an assertion about their bounding boxes.

An equivalent useful form has two disjoint boundary arcs I,J. Suppose
pairwise disjoint trees connect different roots on I to different
terminals on J, and all the connecting paths stay in Omega. With I and J
oriented as opposite sides of a strip, the root-to-terminal correspondence
is order-preserving. An inversion would give the forbidden four-point
order above. These hypotheses include the required localization of the
paths. Global connectedness outside Omega is not a substitute for them.

For the cap roots in (3), delete all pure boundary carriers first.
Different selected contacts on a fixed pure interval lead to different
remaining components, as proved in (4). Thus if paths from those roots
to a proposed interface are actually confined to one intervening disk,
their interface terminals must have the same order. If instead two
such roots reconnect through a single remaining component, the existing
pure interval already closes a forced cycle. Both conclusions are valid
without assuming a maximum configuration.

What is not proved is that the desired terminal paths all stay in a
single first-facing disk. A component can pass around the end of a
partial facing carrier. Declaring that carrier to be a full separator
would add a path that is not in H.

## Rigid Seams Pass The Basic Order Test

Consider one horizontal rigid one-pair seam, assuming the source's
two-straight-cell hypothesis for its participating corridors. With
transverse advance north, its junctions satisfy

```text
v_(i+2)=v_i+(sigma,3), sigma in {-1,1}.
```

The west-pointing corridors are one parity of this sequence and the
east-pointing corridors the other. Each parity separately advances by
three rows in increasing order. If their far ends are immediate caps
backed by the left and right pure intervals respectively, the cap
junctions have exactly the same row labels as their corridors. Their
contact levels on either side are y-1 and y+2.

Consequently consecutive caps on ONE side share the contact level

```text
(y+3)-1=y+2.
```

This is precisely the run sharing in (1). The distinct contact levels
on that side are strictly ordered; they do not make an inverted root
correspondence. The same holds independently on the other side.

Thus the most direct proposed planar contradiction does not occur:
alternating west/east junctions along the seam are not alternating roots
on the same strip boundary. They refer to opposite banks. A narrow ribbon
about a simple seam has one bank traversed forward and the other backward;
joining the two lists as if they were a single forward boundary arc loses
this distinction. The two monotone families pass the disk ordering test.

This does not establish a feasible seam-and-cap filling. It identifies
why noncrossing order alone has not supplied its missing width payment.
One must also control the end regions that join the two banks to the
physical boundary. Proving an inverted order there, or proving a
width-sized loss when avoiding it, remains an additional obligation.

The new global metric inputs do not by themselves supply that obligation.
A literal distance-four overlap has private isolate witnesses; an actual
copy of the specified separation-seven replacement has immutable
singleton witnesses. Neither result proves that a general seam end
exposes one of those windows. The latter note also disproves summing
all enclosing wider pairs. No arbitrary pair window is charged here.

## What Two And Three Pairs Physically Contain

There is nevertheless useful exact contact information for short strands,
including the noneligible orientations. Use the reviewed northward thin
zigzag normal form with first transverse step east.

A two-pair strand has the three distinct preserved vertices

```text
B=(0,2), A=(2,1), C=(2,3).
```

The hole (2,2) is a real contact between the carriers of A and C.
It is U: it is an endpoint of the primal UU edge dual to the strand's
middle contact-type bend-bend edge. A and C are in different carriers,
since one straight filled carrier containing both would contain (2,2).
B is in neither of those carriers because it differs in both coordinates
from each. This proves a three-carrier local statement, not an abstract
connector with three preserved neighbours at one hole.

A three-pair strand adds D=(0,4). Its two contact-type bend-bend edges
come from the actual holes

```text
(2,2), joining A to C;
(0,3), joining B to D.
```

These are distinct contacts and their four participating carriers are
distinct. The only aligned displayed pairs are A,C and B,D, and the
intervening holes exclude a shared carrier. These deductions do not
depend on the endpoint corridors being parallel, positive, or eligible.

Across different strands the same contact hole may supply its two valid
perpendicular sides. Therefore one must not charge each strand's contact
edge as a different ambient-component loss. The exact d_MM accounting
already counts those sides with their proper multiplicity. There is
no new independent c credit from these local contacts.

The next proof uses precisely that counted resource, only once. It
does not need to classify the permitted mixed or same-facing endpoint
directions further.

## Elimination Without The Parallel Tax

Still assume z=0. Retain the exact carrier/contact equations (10).
Let m_E count ALL eligible through strands, let nu be a maximum matching
on them, and put

```text
eta_match=2nu-m_E>=0,
I_1=number of ineligible one-pair through strands,
I_2=number of ineligible two-pair through strands,
I_ge2=number of ineligible through strands with at least two pairs.
```

The eligible graph is bipartite of maximum degree two, including its
isolated vertices and parallel edges. Thus the displayed matching slack
is nonnegative for arbitrary eligible lengths. The physical chain bound is

```text
X_2/A <= g-g_zero-nu.                               (23)
```

Solve the second equation of (10) for P/2, then subtract from the first
equation. Directly,

```text
g-P/2 = r/2-c/2+b/4-3/2-J_4
        -5t_M/8-d_MM/4-t_0/4+3C_o/8-q_bd/2.        (24)
```

Since `P-m_E=I_1+I_ge2`, multiplying (23) by two and using (24) yields

```text
2X_2/A <= K-b/2-2c + I_1+I_2/2 - B_len,

B_len=3-3C_o/4+2J_4+5t_M/4+t_0/2+q_bd
      +2g_zero+eta_match+d_MM/2-I_ge2+I_2/2.        (25)
```

The remaining contact term has a physical nonnegative decomposition:

```text
d_MM/2-I_ge2+I_2/2
 = sum_through [(k_s-1)/2
                -1_{strand ineligible and k_s>=3}
                -(1/2)*1_{strand ineligible and k_s=2}]
   +(1/2)sum_pendant k_a.                          (26)
```

An eligible one-pair strand contributes zero here, as does an ineligible
one-pair strand: its debit was left explicitly in I_1. A noneligible
two-pair strand contributes zero after its half-unit debit has been
left in I_2/2. A noneligible three-pair strand contributes zero without
any remaining debit. Every other summand is also nonnegative. This pays
all noneligible lengths at least three jointly, without a bound on their
number or an assumption about their directions. Each contact-side
contribution in d_MM was used just once in (26).

Since C_o<=4, every remaining term of B_len is nonnegative. This covers
length classes not all covered by the earlier sufficient estimates for
Gamma>=0. It also shows that the k/3 coefficient in the all-one-pair
eligible case can be obtained
without the parallel tax: physical matching and the exact contact loss
already suffice for that weaker coefficient. The parallel tax and its
cap-slot improvement remain valid additional constraints, not necessary
premises of the theorem below.

## The Broader Coefficient Theorem

If I_1=I_2=0, (25) gives the actual metric inequality

```text
2X_2/A <= K-b/2-2c.                                (27)
```

It has coefficient TWO rather than the coefficient THREE needed for
the constant-gap target. This distinction is essential. Substituting
`3X_2=A^2-Q_exc` and `Q_exc<=10K` gives

```text
(3+20/A)K >= 2A+3b/2+6c >= 2n+7,                  (28)
```

where the last step uses b>=2 and c>=1 as in (16). Exactly,

```text
2n+7-(3+20/A)*(2n/3-19/9)=260/(9A)>0.
```

Thus `K>2n/3-19/9`. For n=3k+2, the global ledger implies

```text
f-T < k/3+115/27,
f <= T+floor(k/3)+4.                               (29)
```

The last floor is checked separately for the three residues of k.
This proves the theorem stated at the start of this continuation, with
arbitrary pendant paths, arbitrary numbers of junctions, and arbitrary
lengths and orientations of all through strands with at least three pairs.
For the narrower classes covered by (17), retain that slightly better
constant instead of replacing it by (29).

Retaining b,c in (28) also gives a constant-gap subcase: if

```text
b+4c >= 2n/3+16,
```

then the right side of (28) is at least `3n+22`, while
`(3+20/A)n=3n+20+20/A<=3n+22` for n>=11. Hence K>=n and f<=T+3.
This remains a weighted subcase, not the low-budget global closure.

For completely arbitrary z=0 sets, (25) remains valid with I_1+I_2/2 present.
The crude noneligible-one-pair incidence count is

```text
I_1 <= 4J_4+t_M+4p_zero+2q_zero.                   (30)
```

Indeed a one-pair strand with two positive J_3 endpoints is eligible
by the reviewed one-pair direction lemma. Every ineligible one-pair
strand therefore has an end at J_4, at o, or at a J_3 whose R edge has
zero length. There are at most four, t_M, and two bend ports respectively
at those anchors; the zero R edges have 2p_zero+q_zero junction ends.
This upper bound may count a strand twice, which is harmless here.

But (30) does not finish even the unrestricted coefficient theorem.
Against (25), it can leave `2J_4+2p_zero` before the other available
terms are used. Ineligible one-pair strands at nonpositive anchors
still need a sharper joint argument. No inference that these counts
are bounded follows from their being local.

## Constant-Scale Failure And Isolate Scope

The new payment of noneligible three-pair and longer strands is real at
the coefficient-two metric scale of (27). Noneligible two-pair strands
retain the explicit half-unit error. At the desired coefficient
three scale their contact resources have different prices. Equation
(26) must not be imported into the clean D_C certificate as a payment
of that stronger demand. In particular, the all-one-pair eligible
configuration remains the unresolved geometric case even though (29)
now allows all orientations of strands with at least three pairs.

The separate donor-allocation theorem, if its audit succeeds, removes
growing isolate debt relative to its displayed clean bank B_C. It
deliberately does not preserve junction and exterior-bend resources
spent on donors. Equations (24)--(28) here used the z=0 contact/rank
identities, including exactly those geometric counts. Therefore no
automatic arbitrary-isolate extension of (29) is claimed. Its proof
does not spend the same V_rem or T_rem resources a second time.

For a constant bound, the missing statement is still global placement:
after following a canonical first-facing interface, either its end
connections force a repeated physical connection to one pure interval,
or avoiding that connection consumes enough jointly private width.
The straightforward monotone seam passes the basic noncrossing-order
test, and neither a full facing rail nor confined terminal paths have
been proved to exist for every low-K layout. Counting arbitrary larger
pair windows would violate the explicit nonreuse obstruction in the
global metric note.

No unconditional `3X_2<=A(K+C)` or `P(3k+2)<=T+C` is proved in this
continuation. No maximum-specific exchange, unproved normalization,
grid optimization, or Lean argument was used. Only this new appendix
was written; all earlier text and other agents' notes were preserved.

## A Constant Payment For Opposed Double Folds

There is a further genuine constant-gap class, using NEW physical
length joins rather than calling a same-facing strand eligible. This
lemma still assumes z=0. It is stated separately from the weaker
coefficient theorem and does not assert automatic exposure of its gadget.

Call two actual two-pair through strands a backed double fold if, after
a grid isometry and translation, they have the following bend paths:

```text
left:  (0,0)--(0,1)--(1,1)--(1,2)--(0,2)--(0,3),
right: (3,0)--(3,1)--(2,1)--(2,2)--(3,2)--(3,3).
```

The first and last vertices of each displayed path are its anchors.
Their positive corridors point west at the two left anchors and east
at the two right anchors. The preserved corners are

```text
(0,2), (2,1), (2,3), (4,2),
```

and the two backing FF edges are required to be

```text
(2,0)--(2,1), (2,3)--(2,4).                        (31)
```

These are geometric hypotheses on the actual configuration. Each of
the two strands is noneligible: its own corridors point in the SAME
direction. The middle contact is the hole (2,2), with the left and
right strand edges using its two different perpendicular sides.

The two natural opposed joins are instead

```text
(0,0) joined to (3,0),
(0,3) joined to (3,3).                              (32)
```

Their corridor projections are disjoint and ordered. For example, at
the lower join the left straight cells end at axial label -1 and the
right straight cells start at label 4. Joining these intervals makes
a single monotone length chain with a gap of four labels. It saves one
full A-unit allowance exactly as an eligible join does. The join need
not be a path in the once-pruned dual: the capacity proof only requires
ordered straight intervals and endpoint nonreuse. It does not add an
edge to H or claim a feasible modification of F.

### Global Nonreuse Of These Joins

The FF edge in (31) belongs to the two leaf cells immediately beside
it. Their surviving parents are exactly the two anchors in the
corresponding join (32). Thus a proposed join is identified by one
actual FF edge and its two incident leaf cells.

A participating J_3 anchor has just one deleted leaf. Therefore its
backing FF edge and its possible opposite anchor are unique. After
identical proposed joins are identified, ALL joins (32) from all
backed double folds are endpoint-disjoint. There is no greedy matching
loss or unproved Hall condition here.

A single join can belong to at most two backed double folds. Indeed
at either of its anchors there are only two bend ports, and each fold
using that join uses a different actual through strand at that anchor.
A through strand in this gadget has one middle contact edge, so it
has at most one partner across that contact and cannot define two
different folds. Every fold has two distinct proposed joins. If h_F
counts the folds and j_F the distinct joins, incidence counting gives

```text
2h_F<=2j_F, hence j_F>=h_F.                         (33)
```

Selecting all j_F joins consequently orders the positive corridors
into chains with no repeated end. Each chain retains one axis, and its
successive straight intervals have strictly increasing projections.
A closed chain is impossible. Thus

```text
X_2<=A(g_+-j_F).                                    (34)
```

The FF edge labels also prevent summing arbitrary enclosing windows:
these joins use private leaf-end incidences, not every pair of rails
that happens to surround the same region.

### A Noneligible Two-Pair Theorem

Suppose every through strand has either at least five knight pairs or
belongs to a backed double fold. The short strands form disjoint pairs
by their middle contacts, so there are exactly 2h_F of them. Their
total short-strand cost in (43),(44) of the dual note is 3h_F.
Every longer strand has already been paid there. Equation (33) pays
the full short cost by actual length joins:

```text
D_short=3h_F<=3j_F.
```

More explicitly, that reviewed budget gives

```text
S=3g+1+C_bank-3h_F, C_bank>=0,
3(g_+-j_F)<=S-1<=K-2.                             (35)
```

Together with (34) and the reviewed global area conversion, this proves

> For n=3k+2, k>=3, if z=0 and every through strand either has at least
> five pairs or belongs to a backed double fold, then `f<=T+6`.

The number of noneligible two-pair strands is unrestricted. Adjacent
folds may share a backing join; (33) accounts for precisely that sharing.
No previous eligible matching has been retained at those endpoints.
Longer strands need no selected joins for this proof. Thus no matching
or carrier-inset resource is spent twice.

### Nonvacuity And The Missing Exposure

The class has an explicit arbitrary-size family with arbitrarily many
adjacent folds, so the shared-join case in (33) is not merely abstract.
For n=3k+2, k>=3, start with the full vertical spine x=3 and the teeth

```text
{(x,3j): x in {0,1} union [5,n-1], 0<=j<=k}.
```

The spine support covers columns 2,3,4. In the other columns the
three-spaced tooth bands partition the board, with the first band
truncated at the top and the final band ending at the bottom. Each
left tooth attaches exactly once through (2,3j), and each right tooth
exactly once through (4,3j). There are no other support intersections.
Thus the starting forced graph is a spanning tree.

Delete any m of the spine centers (3,3j), 1<=j<=k-1. Each deletion
removes exactly the two horizontal forced edges at that vertex. Its
vertical edges remain forced by the preserved vertices immediately
above and below it. The two corresponding teeth detach, while the
spine remains connected through the deleted vertex. Neither contact
hole becomes isolated, since it is still adjacent to its tooth. Hence
the result is a forest with z=0 and c=1+2m.

Each deletion gives exactly the two displayed two-pair strands, with
backing FF edges above and below the deleted spine vertex. Consecutive
chosen j values share their intervening backing joins. The leftward
corridors have one straight cell each; the rightward ones are positive
as well. All other bend paths are immediate pendant paths. Thus these
are literal backed double folds with unbounded m, not a large-board
claim inferred from a finite optimum. The family has ample reserve;
it is not offered as a near-extremal construction.

The missing general step must not be hidden: a two-pair strand does
NOT automatically have a backed double-fold partner. On the opposite
side of its contact, a transverse FF incidence can make a leaf-bend
edge rather than another contact-type edge. Even when that side is
contact-type, its adjacent bends can continue into pendant paths or
longer strands, and the opposite positive corridors can turn. Nor is
the axial backing FF condition (31) automatic. The deleted-spine comb
is a boundary example where a second interior fold is not available.

Thus (35) closes a real noneligible two-pair class by simultaneous,
private length payment, but does not settle arbitrary two-pair events,
three-pair events at the constant scale, or the pure-interval one-pair
seam end regions. The unconditional constant-gap target remains open.

There is a precise possible transfer to the new donor theorem, distinct
from the invalid automatic transfer of the coefficient proof above.
If that donor-allocation proof is accepted, allow arbitrary isolates
and require every CLEAN through strand to be either long (at least
five pairs) or in a backed double fold. The fold's positive anchors
are J_3 vertices with clean bend ports. By the donor note's local
positive-junction classification they are regular: a positive irregular
J_3 has only its dirty bend port. The fold joins are consequently
endpoint-disjoint from all dirty and donor joins. They use no donor
bank resources and can replace the selected clean joins in that
allocation's length argument. Since their saving is 3j_F>=3h_F, its
retained clean certificate closes with the same T+6 conclusion.
This transfer relies on the pending donor proof; the isolate-free
double-fold theorem (35) does not. Neither statement asserts that every
clean two-pair strand has a fold partner.

Verification for this continuation: direct in-memory checks of the
displayed family at n=11 and n=14, deleting all permitted internal spine
centers, found respectively 4 and 6 two-pair through strands. All their
anchors had positive corridors. The actual forced graphs were forests
with (f,c,z)=(41,5,0) and (66,7,0). These checks instantiate just two
explicit constructions and do not optimize or search. The arbitrary-size
proofs are the coordinate and attachment arguments above. Separately,
940 exact-rational checks verified the corrected contact-loss elimination,
its nonnegative length summands, threshold, and floor arithmetic. No Lean
command was run, and no file outside this appended note was changed.

## Clean Incidence Allocation Continuation

**Audit correction, 2026-09-08:** The originally claimed arbitrary-isolate
flat-packet transfer without an outer-anchor hypothesis is WITHDRAWN.
Positive outer anchors need not be J_3 in the presence of isolates.
The z=0 theorem (39) and the protected inner 3t_F resource remain valid.
The corrected arbitrary-isolate theorem below explicitly requires every
outer flat-packet anchor to be J_3. The countercheck and resource-overlap
warning are recorded below; neither disproves the numerical T+6 bound.

This appendix preserves the preceding prefix, whose review the user
reports is underway. The user now reports successful independent review
of the isolate donor allocation. Its conservative bank B_C still cannot
be supplemented by arbitrary V_rem or T_rem credits. A specifically
proved unused resource is distinguished below from that invalid reuse.

The unrestricted constant-gap proof is still not closed. The new completed
steps are a simultaneous payment for a physical four-one-pair zero-corridor
packet, including its interaction with backed double folds, and a proved
contact-side classification for unbacked two-pair strands. The latter
classification does not assert that all resulting donors are private.

## Four Demands At One Zero Corridor

The coarse incidence bound cannot simply be improved from four to three
one-pair strands per interior zero corridor. Here is an explicit feasible
9 by 7 rectangle, using vertex coordinates x=0,...,8 and y=0,...,6:

```text
y=0: FFFF.FFFF
y=1: .........
y=2: ....F....
y=3: FFF...FFF
y=4: .........
y=5: ...FFF...
y=6: FF.....FF
```

There are eight carriers and 22 preserved vertices. Their single-carrier
supports are pairwise disjoint except that the two y=0 intervals share
the contact hole (4,0). Thus the supports are trees with just that one
contact. They cover
all 63 vertices: the two gaps beside the middle singleton are its leaves,
and the three-vertex interval on y=5 covers the remaining central upper
vertices. Consequently z=0 and c=7.

In cell coordinates there is a zero R edge

```text
(3,3)--(4,3).
```

Both endpoints are J_3 with their deleted leaf north. Their four bend
ports belong to one-pair through strands with other anchors

```text
(1,4), (2,1), (6,4), (5,1),
```

all having positive corridors. Thus all four strands are ineligible
solely because their inner end has a zero corridor. Paying their two-unit
short cost directly from this zero edge's three units would ask for
eight units, not at most three. This is an actual local multiplicity
counterexample, not a synthetic incidence graph or a low-K counterexample.
Its other resources are not claimed small.

## Flat Singleton Zero-Corridor Packets

Here is the geometric payment that the preceding incidence count misses.
Call an actual configuration of four clean one-pair through strands a
flat singleton zero-corridor packet (abbreviated flat packet below) if,
after translation and a square isometry:

```text
the zero R edge is v=(0,0) to w=(1,0);
both v and w are J_3 and have their deleted leaf north;
all four bend ports at v,w are one-pair through strands;
their other anchors have positive corridors pointing horizontally away;
the central preserved corner (1,-1) is a singleton carrier.
```

The forced north FF edges give F at (0,2),(1,2),(2,2). The remaining
F corners on the south/west/east sides are forced in order:

```text
(-1,0), (1,-1), (3,0).
```

For example (-1,1) would be diagonal to (0,2), so the west bend of v
has F corner (-1,0). The diagonal obstruction then excludes (0,-1),
fixing v's south bend at (1,-1). Reflection gives (3,0). Following
the unique knight partners now gives the four positive anchors

```text
a=(-2,1), b=(-1,-2), c=(3,1), d=(2,-2),
with directions west, west, east, east, respectively.              (36)
```

These are the four one-pair strands in the preceding literal example,
translated by (-3,-3). In the following leaf classification and packet
privacy proof, assume z=0 OR explicitly require all four outer anchors
to be J_3. Under this hypothesis all four outer anchors have their
deleted leaf south. At a this follows from the FF extension forced by its first
westward straight cell and the preserved corner (-1,0). At b, the north
and east neighbours are its two bends (the latter uses the singleton
hypothesis) and the west neighbour is straight, so its unique deleted
leaf is south. Reflection gives c,d. In particular
their leaf direction is perpendicular to their corridor axis.

There are two opposed joins

```text
a to c, of axial displacement five;
b to d, of axial displacement three.               (37)
```

They join disjoint ordered straight intervals, not the same-facing
intervals of one strand. Both save a full A-unit length allowance.

The singleton requirement is substantive. Without it, the other three
neighbours of (1,-1) are still U, but it may extend south to (1,-2).
That extension makes the lower anchors' deleted leaves axial rather
than perpendicular. It gives an actual backing FF edge for their
opposed join, but the leaf-direction nonreuse argument below no longer
assigns that lower join privately to this packet. Such nonsingleton
packets are not included by silently identifying their backing join
with a new independent double-fold credit.

## Packet Joins Are Globally Private

This argument requires the outer-J_3 hypothesis just stated. It holds
automatically for z=0, but is not automatic with arbitrary isolates.

Fix a positive corridor-end junction in any flat packet. Its positive
direction and its unique leaf direction determine the normalization
in (36), up to its being an upper or lower anchor. Its proposed opposite
partner is therefore at axial distance either three or five, in the
direction opposite its own positive corridor. Its transverse coordinate
is unchanged. For a fixed one of these distances, the zero edge and
the packet are uniquely determined by the displayed coordinates.

The two different proposed partners cannot both exist. They would be
two junctions on the same cell row, distance two apart, whose positive
corridors point in the same direction from the nearer to the farther.
The nearer one's first straight cell lies between them and has a core
edge to the farther junction. The latter would then have a positive
corridor arriving from one side and another leaving on the opposite
side. This contradicts the reviewed positive-port lemma: a junction has
at most one positive R corridor. That lemma holds even with isolates.

Thus an outer anchor belongs to at most one flat packet. All the joins
(37), over ALL flat packets, are endpoint-disjoint. No half-matching loss
is needed. Each packet has one distinct zero R edge, and each of its
four one-pair strands has that edge at its unique nonpositive end, so
different packets also have disjoint strand sets.

If t_F counts flat packets, they therefore supply exactly 2t_F joins
and use t_F distinct zero corridors. Their short-strand demand is 8t_F.
The payment is simultaneous:

```text
3*t_F from discarding those zero corridors,
3*(2t_F) from the opposed joins,
total 9t_F >= 8t_F.                                (38)
```

This spends each zero-length allowance and each endpoint once. It does
not count the original ineligible one-pair strands as eligible joins.

Flat joins and backed double-fold joins are also endpoint-disjoint.
The former require a perpendicular deleted leaf at a positive junction,
whereas the latter require its axial backing leaf. A J_3 junction has
only one such leaf. Thus both new join systems can be used together.

## A Combined Constant-Gap Class

First assume z=0. Suppose every through strand either has at least five
pairs, belongs to a flat singleton zero-corridor packet, or belongs to a
backed double fold. Let h_F and j_F retain their earlier double-fold meanings.
The short demand is exactly 8t_F+3h_F. Select all the private joins
from both systems and put

```text
L=g_+-2t_F-j_F.
```

All selected joins have ordered projections and no shared end, so
`X_2<=A L`. The reviewed short budget gives

```text
S=3g+1+C_bank-8t_F-3h_F,
3L <= S-1-C_bank-t_F <= K-2,                        (39)
```

using g_zero>=t_F and j_F>=h_F. Consequently `f<=T+6` on n=3k+2,
k>=3. This is an error-free payment of arbitrarily many ineligible
one-pair strands in the stated geometry, together with arbitrarily many
noneligible two-pair folds. It does not require their number to be O(1).

The original arbitrary-isolate transfer without an explicit outer-J_3
hypothesis is withdrawn. Here is the corrected extension, requiring
ALL FOUR OUTER ANCHORS OF EVERY FLAT PACKET TO BE J_3. This is an added
hypothesis, not a consequence of positivity and clean one-pair ports.

The protected INNER resource does not need this added hypothesis.
The packet's two inner J_3 junctions are regular:
their two bend ports are clean and their only R neighbour is the other
inner junction. Each has s=0, is nonpositive, and retains exactly 3/2
in its local V_rem account. Neither can be a donor in the reviewed
allocation:

* A backing donor needs an adjacent positive crossing; its only crossing
  neighbour here is the other nonpositive inner junction.
* A donor in the h role needs a dirty port and isolated corners; these
  junctions have neither.

They are not exterior or strand resources either. The packet inner
junctions are distinct between packets because each has its unique
zero R edge. Hence this SPECIFIED 3t_F of V_rem is provably never
requested, rather than being a second copy of donated credit.
This retained 3t_F replaces the zero-corridor credit in the z=0 proof;
it is not added to another copy of those same three units per zero edge.

Under the added hypothesis, the outer packet anchors are positive J_3
with clean bend ports. The backed-fold anchors are J_3 by their backing
leaf geometry. These anchors are therefore regular by the reviewed
local classification, and the leaf-direction packet privacy proof applies.
The new joins are consequently disjoint from all dirty/donor joins.
One may then
retain this particular unused 3t_F in addition to B_C in the donor
proof's last step, and replace its selected clean joins by the present
2t_F+j_F joins. The clean short demand is paid by

```text
3t_F+3(2t_F+j_F) >= 8t_F+3h_F.                     (40)
```

**Corrected theorem.** For n=3k+2, k>=3, (39)'s T+6 conclusion holds
with arbitrary isolates if every CLEAN through strand is long (at least
five pairs), in a flat packet, or in a backed double fold, AND all four
outer anchors of every flat packet are J_3. The only V_rem retained in
this extension is the explicitly
unrequestable packet charge just proved. No T_rem credit is used.
This is a geometric refinement of the conservative donor certificate,
not an assertion that that certificate already retained arbitrary V/T.

## Audit Countercheck To The Withdrawn Transfer

Delete the preserved vertex (3,0) from the displayed 9 by 7 seed. The
new row y=0 is `FFF..FFFF`; all other rows remain unchanged. Feasibility
is immediate because deleting a preserved vertex only removes forced
edges from the original forest. The inner zero corridor, all four clean
one-pair strands, the singleton (4,2), and all four positive outer
corridors remain.

But the lower outer anchor b=(2,1), in the seed's cell coordinates, is
now a positive J_4 with s=1, not J_3. The grid vertex (3,1) is isolated.
The east and south cells of b are dirty one-bend strands, both leading
to the nonpositive anchor (3,0). This is exactly the sort of positive
J_4 endpoint that may participate in the isolate allocation: its clean
port does not make it a regular J_3 or reserve it for a flat-packet join.

The example can also be embedded in an 11 by 11 square by placing its
unchanged coordinates in [0,8] by [0,6] and taking every additional
vertex to be U. The new forced edges to the padding are pendant edges
from preserved vertices on the old right or top side. No added vertex
has two such preserved neighbours, so this extension is still a forest.
The packet and the specified J_4/dirty-strand neighbourhood remain
inside the old rectangle. Thus the endpoint-classification failure is
not confined to rectangles or to a board below the theorem's size range.

This countercheck invalidates the inference that all positive clean
outer anchors are J_3 and hence the unrestricted transfer/privacy
argument. It does NOT disprove f<=T+6, the z=0 theorem, the protected
inner resource, or the corrected theorem with the explicit outer-J_3
hypothesis. No numerical upper-bound counterexample is claimed.

## Shared Resource With E_C

The packet's protected 3t_F is the SAME resource as the four 3/4 clean-port
slots per packet in the isolate note's endpoint allocation E_C: each
inner regular nonpositive J_3 has bank 3/2 split between its two clean
ports. There are two such inner junctions per packet.

One must use either the aggregate packet allocation in (40), or the
corresponding endpoint-slot allocation, not add both credits. If working
with the refined D_port=D_C-E_C certificate, return any payments already
taken from these packet-inner slots before using their full 3t_F in
(40). Alternatively retain those endpoint payments and use only the
unused remainder of these same slots. The corrected theorem above is
proved from the conservative B_C certificate with this specific inner
resource retained once; it does not also add its E_C contribution.

## Unbacked Two-Pair Contact Alternatives

The following classification does not presume a fold partner. Assume
z=0 and normalize an actual two-pair through strand as above, with

```text
A=(2,1), C=(2,3), B=(0,2) preserved,
u=(2,2) the middle contact hole.
```

Consider the perpendicular contact side opposite the strand, namely
the side to the right of u.

1. If that side is outside the board, u is a genuine boundary contact.
   Its q_bd witness is unique for this strand's middle contact.
2. If the side exists and A or C has an FF extension to the right, it
   has exactly one such extension, not two. Two would force the six-cycle
   between the parallel FF edges. The opposite contact side is then a
   leaf-bend edge and supplies one actual terminal bend counted by e_1.
3. If there is no such FF extension, the two opposite cells are bends
   joined by a contact-type edge. The vertex (3,2) is U, and its north,
   south, and west neighbours are U as well. Since z=0, its east neighbour
   B'=(4,2) must exist and be F.

In case 3, B' cannot extend vertically both up and down. If (4,1)
and (4,3) were both F, the rectangle [2,4] by [1,3] would have its
entire eight-edge perimeter forced: the left side goes through u,
the right side through B', and the horizontal sides join A and C to
the two displayed vertical neighbours. This is a literal cycle.

If exactly one of (4,1),(4,3) is F, one of the opposite contact bends
has a leaf neighbour and is a core endpoint. The other has a knight
partner at B'. Thus the opposite contact edge lies in a PENDANT clean
strand with at least one knight pair. It is not an unseen eligible
through strand. The assertion includes arbitrary continuation beyond
that first pair.

If neither vertical neighbour is F, both opposite contact bends have
knight partners at B'. There are four consecutive bend cells, exactly
the two-pair segment on the right in the double-fold picture. The
remaining path may be:

* A pendant strand with at least two pairs.
* A through strand with at least three pairs.
* An exact two-pair through strand.

These alternatives are exhaustive because bend paths are paths, cannot
cycle, and a bend already in a knight pair is not a core endpoint.
In the last alternative, the endpoint corridors may be nonpositive,
may turn, or may lack the backing FF edges. Neither positivity nor
the backed double-fold condition follows merely from the two-pair
segment. The private payment (35) applies only when its full geometric
hypotheses hold.

## What The Alternatives Do Not Pay

The boundary witnesses in alternative 1 are injective: a boundary
contact has only one valid side. The terminal bends in alternative 2
are also distinct for distinct opposite contact sides. However, e_1
has already participated in the carrier/contact ledger; it is not a
new reserve of one unit per terminal bend.

In alternative 3 the opposite contact EDGE is private, but the entire
opposite bend strand need not be. A through strand with k pairs has
k-1 contact-type edges, and a pendant strand with k pairs has k such
edges. It can therefore receive as many as k-1 or k separate requests
from different two-pair strands on its opposite sides. Calling that
whole strand a private donor per request would be invalid. Its own
contact and long-strand credits have only their previously counted
total values.

This is why the classification does not yet yield a universal
one-and-a-half-unit payment for every unbacked two-pair strand. It
does identify exactly where actual boundary contacts, terminal bends,
pendant paths, and longer opposite strands enter, without using an
arbitrary wider pair window or assuming that every fold is backed.

## Current Remaining Failure

Flat singleton packets pay the same-leaf, fully opposed positive pattern
with the specified central singleton. A southward extension of that
center is a separate, unallocated alternative. Zero-corridor endpoints
with different leaf sides,
turning outer corridors, nonpositive outer anchors, and J_4 fans are
not proved paid by this construction. The four-port J_4 incidence
allowance cannot simply be replaced by a smaller number without its
own geometric proof. The reviewed donor allocation concerns dirty
strands and does not prove that corresponding clean fans are paid.

Even eliminating those ineligible events would leave the all-one-pair
eligible seam-cap placement problem. Its two banks have compatible
monotone orders, and a width-sized terminal loss has not been proved
unavoidable. No explicit feasible counterfamily to the desired global
constant bound has been found; the rectangle above only tests a local
incidence shortcut.

The new result is therefore a simultaneous constant payment for the
specified clean one-pair singleton zero packets and backed two-pair folds
when z=0, with an arbitrary-isolate extension ONLY under the explicit
outer-J_3 hypothesis, plus the unbacked two-pair
classification. It is NOT a universal clean-strand payment and does
not prove `P(3k+2)<=T+C` unconditionally.

Original verification before audit: a direct in-memory check of the displayed 9 by 7 set
confirmed its forest, coverage, (f,c,z)=(22,7,0), zero edge, and four
one-pair strands with positive outer anchors. Separately, 1,800 scalar
arithmetic checks verified the joint packet/fold payment inequalities.
No optimization, larger grid check, or Lean command was run. Only this appendix was written;
the prefix and all other agents' notes were preserved. Independent review
subsequently found the arbitrary-isolate endpoint gap recorded above.

Audit-correction verification: direct in-memory checks reproduced the
deleted-vertex example on both the 9 by 7 rectangle and its U-padded
11-square embedding. They gave (f,c,z)=(21,9,1) and (21,60,52),
respectively. Both retain the inner zero edge, central singleton, four
clean one-pair strands with positive outer corridors, and the specified
positive J_4 with s=1 and two dirty one-bend strands. Whitespace checking
passed. No optimization or Lean ran, and only this note was edited.
The corrected outer-J_3 theorem and these revisions await independent
review; the withdrawn transfer is not restored by these finite checks.
