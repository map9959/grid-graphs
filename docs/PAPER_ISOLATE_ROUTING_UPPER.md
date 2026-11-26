# Isolate Routing Upper Research

Date: 2026-09-08. Paper deductions only. No search, optimization, or Lean
changes. The unrestricted constant-gap bound remains open, including the
unrestricted isolate-free case in `PAPER_DUAL_UPPER_RESEARCH.md`.

## Scope And Notation

Current checkpoint: independent read-only reviews covered the complete
note through Clean Endpoint Resources (original line 1691), with no
mathematical findings. The earlier unresolved isolate debts are superseded
by Simultaneous Donor Allocation. Its conservative clean certificate has
no isolate-count error:

```text
B_C=3(c-z-1)+t_0+3delta/2+C_C,
D_iso_free=max(0,D_C-B_C-3nu_C),
3(f-T)<19+D_iso_free.
```

In particular, if every clean through strand has at least five knight
pairs, then f<=T+6 for n=3k+2, k>=3, with arbitrary globally isolated
holes. The refined endpoint-resource certificate below pays more short
strands. Neither certificate is proved debt-free for all clean short
strands. This is not a theorem allowing an arbitrary isolate-free proof
to be transferred: resources donated here must remain unavailable to the
clean proof. Historical unaudited labels below refer to earlier snapshots.

Use the actual graphs and counts of that note, not a repaired configuration.
On a square let `A=n-1`, `K=r+b+c`, and `beta=c-1`. Let `z` count globally
isolated vertices of the forced forest H. A hole with no preserved neighbour
in a chosen window is not necessarily such an isolate.

We use its once-pruned connected dual C, corridor graph R, corridor count g,
straight-cell count X_2, through-strand count P, and counts
`J_3,J_4,M,e_1,d_MM,t_R,t_M,t_0,w,C_o,q_bd,Z_M,Z_X`.
Set `delta=2+q_bd-C_o/2>=0` and

```text
S=M/4+3w/2+t+c,             K=S+4-3C_o/4 >= S+1.
A^2=3X_2+Q_exc,            Q_exc<=10K.
```

All component and port multiplicities are retained. For `n=3k+2>=11`, put
`T=3k^2+7k`. The source's area conversion says that a physical certificate

```text
X_2<=A L,       3L<=K-2+D,       D>=0
```

implies `3(f-T)<19+D`. In particular `D=0` gives `f<=T+6`.
Exceptional area is already paid here. It must not be charged again as
one full board-length corridor per exceptional cell.

## Exact Isolate Packets

Write `z_i,z_e,z_o` for interior, open-boundary, and corner isolates. Define

```text
eta=2z_e+3z_o.
Z_M+Z_X=4z_i+2z_e+z_o=4z-eta.                       (1)
```

Proof: in a cell incident to an isolate u, its two corners adjacent to u
are U. The opposite corner is either F, giving exactly a bend counted by
Z_M, or U, giving a crossing incidence counted by Z_X. Such a cell cannot
be a leaf. Each interior, open-boundary, or corner vertex has respectively
four, two, or one incident cells. This counts incidences, not distinct
cells; neighbouring isolates are allowed.

In particular every isolate-incident cell survives once-pruning, and none
is a straight crossing cell: the two opposite leaves of a straight
crossing supply an F neighbour to each of its four U corners.

The source identities, valid also for z>0, give

```text
M=e_1+2k_MM+Z_M,       P=k_MM+Z_M-d_MM,
e_1=J_3+2J_4+t_R+t_M-2beta,
2g=t_R+J_3+Z_X,        g+P=J_3+J_4+beta,
q_ct=r-c+z,            2q_ct-e_1=d_MM+q_bd.
```

Combining these with `M=4r-2w-C_o` proves the useful boundary cancellation

```text
w=t_R+t_M/2+delta-2z+(Z_M+Z_X)/2
 =t_R+t_M/2+delta-eta/2.                            (2)
```

Thus interior isolates do not independently increase or decrease this
boundary-interval account. Treating their four incidences as four lost
boundary packets would be wrong. Boundary isolates have the explicit
truncation eta instead.

The same substitution gives an isolate extension of the source's unsplit
strand budget:

```text
S=3g+1+3J_4+3beta+2t_M+t_0+3delta/2+d_MM/2-2P
  -3z-2Z_X+Z_M/2.                                  (3)
```

For example one can first substitute
`M=2g+2J_4+t_M-2beta+2P+2d_MM-Z_X-Z_M` into S,
then use (2) and the rank identity. Equation (3) reduces exactly to the
isolate-free budget when z=0. It is an equality, not a metric estimate.

If F is nonempty, let `c_0=c-z>=1` and `beta_0=c_0-1`. Then
`beta=z+beta_0`, and the combination `3beta-3z` in (3) is exactly
`3beta_0`. The isolate rank reserve has already been spent in this
rewriting; another allocation of z component units would double-count.

## Clean Strands Survive

Call a bend strand clean if none of its bends is counted by Z_M. Every
non-endpoint bend of a clean strand has its unique knight partner in that
same strand. The source's alternating contact/knight proof consequently
applies verbatim on a clean strand, without requiring z=0 elsewhere.
In particular a clean through strand has 2k bends, thin-zigzag geometry,
and the source's terminal parity restrictions.

Call a J_3 junction regular if it has no isolated corner. Locally, if s(v)
counts isolated corners at a junction v, the crossing incidence identity
gives

```text
deg_R(v)=1+s(v)  at J_3,        deg_R(v)=s(v) at J_4. (4)
```

Indeed its bend-port count is `2-s(v)` or `4-s(v)`, respectively.
All of Z_X is at junctions, so `sum_v s(v)=Z_X`. Let i_3 count irregular
J_3 junctions. Then `i_3<=Z_X`.

Declare a through strand eligible here only if it is clean, its two
anchors are regular J_3 junctions with positive corridors, and those
corridors are parallel and point away from one another. This deliberately
does not assume a routing rule inside an isolate patch.

The eligible graph on all J_3 junctions has maximum degree two and is
bipartite: a clean through strand has 2k+1 edges between its anchors.
Let m_E be its edge count, nu its maximum matching size, and n_2E its
number of degree-two vertices. The path/even-cycle calculation proves

```text
sigma=n_2E-2m_E+3nu>=0.
```

The selected joins order disjoint straight-cell intervals on each chain's
one axis, just as in the source's eligible-join proof. Thus, with g_+ the
number of positive corridors and `g_zero=g-g_+`,

```text
L=g_+-nu,       X_2<=A L,       Delta=A L-X_2>=0.     (5)
```

No clean strand claim is made for a strand containing an unmatched
isolate-opposite bend. In particular such bends can break the turn pairing.

## Rank With Actual Branching

Retain all through strands in the connected suppressed graph, not only
the eligible ones. At a J_3 vertex let n_j count through degree j, for
`j=0,1,2`. These are exhaustive even at irregular junctions, by (4).
Let d_4 and d_o be through-port counts at J_4 and o. The full degree sum is

```text
n_2-n_0+d_4+d_o=2beta-t_R+2J_4-Z_X.                (6)
```

The extra `-Z_X` is essential: R now branches at isolate-incident
junctions. Let u_0 count J_3 vertices with eligible degree zero. The same
six-case comparison of eligible and full through degree as in the source
then proves

```text
2P-3nu=u_0+2beta-t_R+2J_4-Z_X-sigma.               (7)
```

For completeness, if b_3 counts ineligible through incidences at J_3,
the two equations used are `2(P-m_E)=b_3+d_4+d_o` and
`u_0=n_0+b_3-(n_2-n_2E)`. Neither assumes through strands are clean.

Split the regular eligible-degree-zero junctions into three classes:

* u_root: their unique R edge goes to o, including zero-length edges.
* N_zero: their unique R edge is a zero-length edge not going to o.
* u_int: their unique R edge is positive and does not go to o.

Their other endpoint need not be regular. Irregular J_3 vertices all
have eligible degree zero by definition. Therefore

```text
u_0=u_root+N_zero+u_int+i_3,
u_root<=t_R,             N_zero<=2g_zero.
```

Substitute (7) in (3), and set

```text
B=J_4+beta+2t_M+t_0+3delta/2+d_MM/2+sigma
  +(3g_zero-N_zero)+(t_R-u_root) >=0,
E_iso=i_3+3z+Z_X-Z_M/2.
```

The resulting exact, isolate-aware endpoint certificate is

```text
S=3L+1+B-u_int-E_iso.                              (8)
D=max(0,u_int+E_iso-B-3Delta/A),
3(f-T)<19+D.                                       (9)
```

To obtain (9), use the nonnegative allowance `X_2/A` in the area
conversion, not a second copy of the removed chain lengths.
This proves a conditional T+6 theorem whenever the displayed signed debt
is nonpositive, with no restriction on the number of actual isolates.
It does not show that this condition is automatic.

If `B=B_0+z` by replacing beta with beta_0, (9)'s signed debt becomes

```text
u_int+i_3+2z+Z_X-Z_M/2-B_0-3Delta/A.               (10)
```

This displays precisely the remaining cost after using the coefficient-one
isolate component reserve. For instance, the crude estimates
`Z_X<=4z` and `i_3<=Z_X` only give an O(z) loss, not closure.
Conversely large Z_M is genuine signed help here and must not be discarded
before combining (10). By (1), its isolate part can also be written
`i_3+6z-3Z_M/2-eta`.

As a bookkeeping check,

```text
u_int+E_iso-B-3Delta/A = 1+3X_2/A-S.
```

Thus changing the eligible matching alone cannot improve the final exact
debt. Joins and the spare length they consume are not independent credits.

## What Suppression Really Proves

There is a topological suppression lemma with no loss of straight cells.
Assume F is nonempty. Around each globally isolated grid vertex all
incident primal edges are UU. Their duals form its facial cycle in D:
an interior four-cycle, an open-boundary triangle through o, or a corner
digon through o. Parallel exterior edges are retained. All these edges
remain in C because their cell endpoints are not leaves.

These z facial cycles are independent in the binary cycle space. One
way to see independence without any drawing convention for the outer
dual face is to identify their edge sets with primal vertex stars.
A sum over a nonempty subset is the edge cut of that subset in the
connected primal grid, hence is nonzero unless the subset is every grid
vertex. Nonempty F excludes that last possibility.

Let W be the union of their dual edges. Its cycle rank is at least z.
Choose a spanning forest of W and extend it to a spanning tree of C.
There are at least z edges of W outside this tree. Delete any z of them.
The resulting graph is connected and has rank `beta-z=beta_0`.
No straight crossing cell or edge incident to such a cell was deleted.
Only isolate-incident cells and o were affected.

This is a rigorous rank suppression, not an isolate-free grid instance.
There are at most `4z-eta` distinct affected cell vertices, but deletion
can create straight degree-two bends, new leaves, or degree-three
crossings with the wrong packet interpretation. It need not preserve
the clean-strand normal forms, physical carrier contacts, or the
width-three corridor partition of the original graph.

In particular the z removed cycles cannot also be offered as unspent
rank in (8). The lemma shows that all isolate topology can be localized;
it does not show a length payment of at most one unit per hole.
Shared edges of neighbouring isolate cycles cause no independence problem,
but prevent assuming disjoint four-cell routing gadgets.

A primal repair is equally nonautomatic. Promoting an isolated hole u to
F adds its `deg_grid(u)` incident edges. It preserves the forest exactly
when its neighbours belong to pairwise distinct old H components: the
new star then joins distinct trees through u. Two neighbours in the same
tree instead create a cycle. Global isolation alone gives no such
distinct-component guarantee.

## Large Isolate Reserve

Large z does admit an unconditional shortcut, independent of any routing.
Each carrier has at most n vertices, so `f<=nr`. Combining this with the
ledger gives

```text
K >= [n^2+4n+3n(b+c)]/(3n+1).                      (11)
```

Indeed `r>=f/n=(n^2+4n-K)/(3n)` and `K=r+b+c`.
For any fixed `d>=0`, (11) proves `K>=n-d` whenever

```text
b+c >= 2n/3-1-(1+1/(3n))d.                        (12)
```

Since `c=z+c_0`, the same test can be expressed using actual isolates
and the other components. In particular `b+z+c_0>=2n/3-1` gives `K>=n`
and hence `f<=T+3` on residue-two squares. When F is empty, f=0 needs no
certificate; otherwise `c_0>=1` as above.

Consequently a putative configuration with `K<n-d` necessarily satisfies

```text
z < 2n/3-1-b-c_0-(1+1/(3n))d.                     (13)
```

This is a useful reduction, but not a bounded-z reduction: the right side
can remain linear in n. If the small-z routing estimate leaves debt a*z
for a fixed positive a, taking its minimum with the large-z test still
allows a linear loss at intermediate z. For example the bounds themselves
do not close when z is a fixed positive fraction below 2n/3 and the other
reserves are small. This is an observation about the inequalities, not a
claim that such grids are realizable.

## Exact Unproved Step

There are two precise ways to state the outstanding isolate obligation.

First, within the actual clean-strand certificate above, outside the
large-reserve regime (12), it would suffice to prove for an absolute D_0

```text
u_int+i_3+2z+Z_X-Z_M/2 <= B_0+3Delta/A+D_0.        (14)
```

Neither (14) nor its z=0 specialization is proved here. Its z=0
specialization retains the source's blocked-cap/nonlocal interval problem;
it is not legitimate to assume all of that case has already closed.

Second, a genuinely modular suppression theorem could work as follows.
After spending the z isolate component units exactly once, supply a
physical length allowance L_base and nonnegative credits D_base,s_save
such that

```text
3L_base <= (K-z)-2+D_base-s_save,
X_2 <= A(L_base+rho),
3rho <= z+s_save+D_iso,                            (15)
```

where rho is a nonnegative actual routing overhead and D_iso is bounded
independently of n and z. Then the area conversion immediately gives
`3(f-T)<19+D_base+D_iso`. A separate proof bounding D_base is still
needed for the underlying isolate-free obstruction. The topologically
suppressed graph above has not been shown to satisfy the first line.

The coefficient in (15) is the key scale: with no other savings, an
isolate may increase the number of full length allowances by at most
one third on average, since those allowances cost three units each.
A statement merely giving one extra full corridor per isolate spends
three component units per hole, not one. More generally a bound of a
fixed multiple of z on the excess or routing debt is insufficient unless
the surplus beyond z has a separately proved, non-reused payment.

What has been proved is (1)--(13), the clean-strand metric extension,
and the rank suppression lemma. What is missing is a geometric allocation
such as (14), or the coefficient-one routing theorem (15) together with
the unresolved base certificate. No universal upper bound is inferred
from finite checks; no grid checks were run for this note.

Verification: the substitutions for (2), (3), and the unsplit form of (8)
also passed exact-rational arithmetic smoke checks on 1,000 formal
parameter tuples. These tuples are not grid configurations, and this
algebra check supplies no geometric or universal-bound evidence. The
proofs are the displayed symbolic substitutions and counting arguments.

## Actual Payment Continuation

This appendix leaves the prefix above unchanged. It proves a new
isolate-payment theorem, not a theorem for every feasible configuration.
Unlike a bound proportional to z, the theorem below permits arbitrarily
many isolates with no isolate error at all in its stated class.

Call a through bend strand dirty when it contains an isolate-opposite
bend, and clean otherwise. A positive endpoint of such a strand means
a junction incident to a positive R corridor. An exterior endpoint is
always classified as nonpositive here: physical exterior bend ports are
not silently joined to exterior corridor ports.

### Dirty Strands Are Local

Every dirty strand consists entirely of bends opposite the SAME isolated
hole. It is through, and has one, two, or three bends.

Proof: the two dual edges of a bend opposite u are precisely its two
edges around u. Across either edge, another bend must also have its F
corner opposite u. The alternative F corner would be a grid neighbour
of u, contradicting global isolation. Thus this property propagates
along the entire bend path. Such a bend cannot have a deleted leaf
neighbour, since every cell incident to u is a crossing or a bend.
The path therefore has two anchor ends. An interior hole has only four
incident cells; four bends would form a separate dual cycle, forbidden
by connectedness of D. A boundary hole has at most two incident cells.

All edges between successive dirty bends are contact-type, not knight
edges. If P_D counts dirty strands and j_s their bend lengths, then

```text
1<=j_s<=3,
Z_M=sum_dirty j_s,
d_MM=d_C+Z_M-P_D,           P=P_C+P_D.             (16)
```

Here d_C counts contact-type edges in clean bend paths; P_C counts clean
through paths. All pendant paths are clean. Consequently

```text
d_C=sum_clean through(k_s-1)+sum_pendant k_a.        (17)
```

This is stronger than cutting an arbitrary long strand at each defective
bend: there are no mixed long strands to cut. Opposite diagonal F corners
around an isolate can give two separate one-bend dirty strands; they are
not counted as one two-bend strand.

### Positive Corridors Cannot Branch Locally

Every junction is incident to at most one positive R corridor, even when
isolates are present.

First, two perpendicular positive corridors are impossible. Put the
junction cell at (0,0), and suppose its east and north neighbours are
the first straight crossing cells of positive corridors. The east one
forces FF edges `(1,2)(2,2)` and `(1,-1)(2,-1)`. The north one forces
FF edges `(2,1)(2,2)` and `(-1,1)(-1,2)`. The two FF edges meeting at
(2,2) make a forbidden carrier turn. Rotation covers the other cases.

Two opposite positive corridors supply an outside F neighbour to every
corner of the junction cell. Thus s(v)=0 in (4). But then its R degree
is one at J_3 or zero at J_4, not two. This also is impossible.

There is a more precise local statement needed for payment:

* A positive irregular J_3 junction has s=1 and exactly one dirty bend port.
* A positive J_4 junction has s=1 or s=2, and exactly two dirty bend ports.

To verify it, orient the positive corridor east. Its first straight cell
forces F at `(1,2),(2,2),(1,-1),(2,-1)`. Hence the north and south cells
of the junction are bends or leaves. Any isolated corner of the junction
must be on its west side. If one of north/south is a leaf, an irregular
J_3 has the other a bend and its west neighbour a crossing or o; its
single isolated corner makes precisely that bend port dirty. If neither
is a leaf, a J_4 has two possibilities. A crossing/exterior west neighbour
leaves both west corners isolated and makes both north/south bends dirty.
A bend west neighbour leaves one west corner isolated; the west bend
and the north or south bend incident to that corner are its two dirty
ports. These exhaust the J_4 cases. A west leaf is not a J_4 case.

In particular, if an isolate has no opposite F corner in any incident
cell, none of its incident junctions can have a positive corridor:
such a corridor would require one of the diagonal F vertices just used
in this coordinate argument.

### Zero Corridors Pay Crossing Incidences

Let a_v be one or zero according as junction v has a positive corridor.
Let a_3 count positive irregular J_3 junctions, and let t_R0 count exterior
ports of zero-length R edges. Counting zero R half-edges gives

```text
2g_zero=t_R0+sum_J3(1+s(v)-a_v)+sum_J4(s(v)-a_v).
```

Define the following actual local bank:

```text
V=3t_R0/2
  +sum_J3 [3/2-s(v)/2-3a_v/2
             +(1/2 if v is positive and irregular, else 0)]
  +sum_J4 [3-s(v)/2-3a_v/2].
```

The preceding local lemma proves termwise nonnegativity. At a nonpositive
J_3 the possibilities s=0,1,2 give 3/2,1,1/2; a positive regular or
irregular J_3 contributes zero. At a nonpositive J_4 the contribution is
at least one. At a positive J_4, s=1,2 gives one or one-half. Exactly,

```text
3g_zero+3J_4-2Z_X=V-a_3/2,          V>=0.           (18)
```

There is a useful injective allocation inside V. Let N_J be the number
of dirty-strand incidences at nonpositive junctions, including both
incidences of a loop. Then

```text
V>=N_J.                                            (19)
```

A nonpositive J_3 with a dirty port has s=1, at most one bend port, and
charge one. At a nonpositive J_4, s=1 allows at most two dirty ports,
because both must border its single isolated corner, and charge 5/2.
For s=2,3,4 there are at most 2,1,0 bend ports, with charges 2,3/2,1.
The case s=0 has no dirty port. These inequalities prove (19) at each
vertex; they do not charge a port once per nearby isolate.

Let N_o be the number of dirty through incidences at o. Each is its own
exterior bend edge, so `N_o<=t_M`. Thus the original `2t_M` budget pays
one unit per such incidence. Put

```text
N_np=N_J+N_o,
V_rem=V-N_J>=0,             T_rem=2t_M-N_o>=0.
```

### A Budget With No Crossing-Isolate Error

Use (16)--(18) in the exact budget (3), and use `beta=z+beta_0`.
The result is

```text
S=3g_++1+3beta_0+T_rem+t_0+3delta/2+V_rem
  +d_C/2-2P_C
  +sum_dirty [j_s-5/2+n_np(s)-a_3(s)/2].           (20)
```

Here n_np(s) counts the strand's nonpositive endpoint incidences,
including exterior incidences. The quantity a_3(s) counts its positive
J_3 endpoint incidences. Each positive irregular J_3 has exactly one
dirty port, so `sum_s a_3(s)=a_3`; no endpoint has been reused.

All growing `Z_X` and z terms have disappeared from (20) by an actual
local zero-length payment, not by discarding an error. The remaining
dirty-strand summands have a short, physical classification.

### Safe Dirty Joins

Every two-bend dirty strand with two positive endpoints joins parallel
corridors pointing away from one another. Normalize its hole to (0,0)
and its F corners to `(-1,1),(1,1)`. Its crossing anchors are the cells
`(-1,-1),(0,-1)`. A positive corridor at the first can only point west,
and at the second only east. A southward first straight cell would require
an F corner in the other crossing anchor. The inward horizontal edge
is between these two anchors and has zero length. The north ports go
to the dirty bends. This proves the direction assertion. The straight
intervals are ordered, with a gap between their projections.

For a one-bend dirty strand, put its F corner at (1,1) and its isolate
at (0,0). Its anchors are `(-1,0),(0,-1)`. Their positive directions,
if present, are respectively west/north and east/south. North/east
would require perpendicular FF extensions at (1,1). West/south would
require perpendicular FF extensions at (-1,-1). Both are forbidden.
The remaining west/east or north/south pair is parallel and points away.
It also requires F at (-1,-1). There is consequently a second one-bend
dirty strand between the same two anchors. Both positive anchors have
two dirty ports, so they are J_4, not J_3.

A three-bend dirty strand is a loop at its sole remaining crossing cell.
If that anchor is positive it is not J_3, since it has two dirty ports.

Let m_D count one- or two-bend dirty strands having two positive ends.
Their join graph has maximum degree two: positive J_3 vertices have one
dirty port and positive J_4 vertices have two. It is bipartite even though
one-bend dirty strands do not reverse cell checkerboard parity. Within
each component the corridor axis is fixed, and every join connects
opposite pointing directions. These directions give the bipartition.
Loops are absent; parallel one-bend links are retained.

Thus this graph has a matching of size `nu_D>=ceil(m_D/2)`. Selecting it
gives safe ordered joins saving `nu_D` full length allowances. A selected
join never uses a regular junction, so it is endpoint-disjoint from
any selected clean eligible joins in the prefix. Their combined chains
still have one axis and ordered straight intervals; no closed chain is
possible. If nu_C clean joins were also selected, then

```text
X_2<=A(g_+-nu_C-nu_D).                              (21)
```

### Which Dirty Strands Are Fully Paid

The dirty summand in (20) has the following rigorous lower bounds.

| Length and endpoint type | Lower bound |
|---|---:|
| One bend, no positive end | 1/2 |
| One bend, one positive J_3 end | -1 |
| One bend, one positive J_4 end | -1/2 |
| One bend, two positive ends | -3/2 |
| Two bends, at most one positive end | 0 |
| Two bends, two positive ends | -3/2 |
| Three bends | 1/2 |

These follow simply by inserting n_np and a_3 in (20), using the
J_4-only assertion for a doubly positive one-bend strand and for a
positive three-bend loop. In the last row a nonpositive loop only adds
credit. Exterior anchors are included in the nonpositive cases.

The selected dirty matching pays all doubly positive strands together:
their total debit is at most `3m_D/2<=3nu_D`. Strands with no positive
ends, two-bend strands with one positive end, and all three-bend strands
are already paid termwise. This is a simultaneous allocation from one
budget, not a separate use of the same rank or component units.

For a compact exact statement, define

```text
E_one = number of one-bend dirty strands with exactly one positive J_3 end
        +(1/2) * number with exactly one positive J_4 end,

D_C=(1/2)sum_clean through max(5-k_s,0),
C_C=(1/2)sum_clean through max(k_s-5,0)
     +(1/2)sum_pendant k_a,
C_rest=3beta_0+T_rem+t_0+3delta/2+V_rem+C_C.
```

Then (17), (20), and the dirty matching prove

```text
S >= 3(g_+-nu_D-nu_C)+1
     +C_rest-D_C+3nu_C-E_one.                      (22)
```

All terms of C_rest are nonnegative. Positive dirty summands and excess
dirty matching credit have only been discarded in this weaker inequality.
Together with (21) and the original `Q_exc<=10K`, it gives the sufficient
residual

```text
D_new=max(0,D_C+E_one-C_rest-3nu_C),
3(f-T)<19+D_new.                                   (23)
```

In particular, this is an actual error-free isolate-payment theorem:

> If there is no one-bend dirty strand with exactly one positive end,
> and every clean through strand has at least five knight pairs, then
> `f<=T+6` on `n=3k+2>=11`. The numbers of isolates, dirty strands, and
> clean through strands are unrestricted.

The clean-through hypothesis can instead be replaced by the sufficient
payment `D_C<=C_rest+3nu_C`, with no restriction on clean strand lengths.
For example, eligible clean short strands of lengths two through four
are paid by their own half-matching exactly as in the source. Dirty and
clean matching endpoints are disjoint, so those two actual joins can be
used together.

This includes all cases with Z_M=0 whose clean certificate closes, and
all cases with only two- and three-bend dirty strands whose clean
certificate closes. In particular growing z, or growing Z_X, is not
itself an unpaid obstruction in this theorem.

### Remaining One-Sided Event

The continuation has not proved that E_one is paid in general. It is
strictly more specific than an arbitrary isolate or a branching junction:
it requires a single bend around one isolate, exactly one attached
positive corridor, and no second positive corridor at the other anchor
with which to make the local safe join.

For an interior isolate, one diagonal F corner gives one such possible
strand. Two opposite diagonal F corners give two one-bend strands with
the same anchors; if exactly one anchor is positive it is J_4, and their
total E_one is one, not two. Two adjacent or three diagonal F corners
instead give a two- or three-bend strand. Boundary isolates also have
at most two incident bend cells. Consequently `E_one<=z`, but this
inequality alone is NOT a final payment: the z component units were
already included through `beta=z+beta_0` in deriving (20).

To finish the isolate part using this construction, one needs a new,
non-reused payment for these one-sided events. With actual spare length
`Delta_new=A(g_+-nu_C-nu_D)-X_2`, a sufficient combined obligation is

```text
D_C+E_one <= C_rest+3nu_C+3Delta_new/A+O(1).        (24)
```

The large-b+c shortcut (12) still applies independently. Neither that
shortcut nor `E_one<=z` proves (24) in the intermediate-z regime. No
claim that they do is made here. The clean term D_C also remains a
separate pre-existing obstruction when its own strand certificate fails.

Thus the new completed step is a genuine zero-error payment for every
isolate strand except the specified one-sided one-bend events, with
arbitrarily many already-paid isolates permitted. The unrestricted
isolate routing theorem is still unproved. This appendix used coordinate
arguments and graph counting only, with no grid search or optimization.

## One-Sided Payment Continuation

Status: new paper continuation, not independently reviewed here. The
preceding prefix and appendix are unchanged. This continuation closes
the J_4 part of E_one with an actual simultaneous payment. It also gives
a local classification for the remaining J_3 part, but does not claim
that the resulting local donors can all be used simultaneously.

Write `E_one=E_3+E_4`, where E_3 counts the one-sided one-bend strands
at positive J_3 junctions and E_4 is half their number at positive J_4
junctions. A positive irregular J_3 has only one dirty port, so E_3
also counts distinct positive junctions. Continue to assume F nonempty;
the empty case needs no upper-bound argument.

### Positive J4 Credit Is Still Available

The positive J_4 contribution to V_rem is exactly

```text
1    if s(v)=1,
1/2  if s(v)=2.                                    (25)
```

It has not been used in paying N_J: that allocation was only at
nonpositive junctions. Nor was it needed for the dirty half-matching
payment, which used the three units per selected join.

A positive J_4 with s=1 has its two dirty ports around the same isolated
corner. If a one-bend dirty strand occurs there, the other dirty port
is another one-bend strand to the SAME other anchor. This follows by
walking around that hole: the two neighbouring incident cells are bends;
the fourth is either a crossing, giving two one-bend paths, or a bend,
giving a three-bend loop. Thus the one-sided debit at this vertex is
either zero or one. The unit in (25) pays it entirely.

At a positive J_4 with s=2, zero or one one-sided strands cost at most
one-half and are paid by (25). Only the case with two one-sided strands
has a shortfall: its cost is one, its available positive charge is
one-half. Call such a vertex a double requester. Its remaining request
is one-half, not one unit per incident isolate.

### Backing Cells For Double Requesters

Orient a double requester's positive corridor east and put its cell v
at (0,0). Its two isolates are (0,0),(0,1), and its dirty bends are
the south and north cells. Since both dirty paths have one bend, their
other anchors are

```text
(-1,-1), (-1,1),
```

and both anchors are nonpositive crossings. The cell w=(-1,0) immediately
behind v is also a crossing. The edge vw is a zero R edge. In particular
w is a literal cell; an exterior west neighbour of v would make the
one-bend path's other anchor exterior rather than either of the displayed
cell anchors, so that boundary situation needs its own payment below.

For an interior backing cell w, three of its neighbours are now fixed:
east is v, and north/south are the two nonpositive anchors. Its west
neighbour can be a leaf, bend, crossing, or o. The corresponding unused
local charge, after N_J has been paid, is

```text
west leaf:       J_3, s=2, V_rem(w)=1/2;
west bend:      J_4, s=3, V_rem(w)=1/2;
west X or o:    J_4, s=4, V_rem(w)=1.               (26)
```

In the middle case the west bend is dirty and uses one of the original
3/2 units at w; the remaining half is the one displayed. No dirty port
exists in the first or last case. Also w itself is nonpositive: its
north, south, and east neighbours are junctions, and a westward first
straight cell would require F in one of the two displayed crossing
anchors. Thus (26) is available in V_rem, not in the already used N_J.

If v has exterior rather than cell backing, the two one-bend dirty
strands terminate at o. They use two distinct t_M ports, so N_o includes
two incidences here. The residual `T_rem=2t_M-N_o` retains at least one
unit per dirty exterior incidence. Reserve half a unit from either one
of these two ports for this request. Different such boundary requesters
have different dirty strands and exterior edges. This is an injective
payment and uses no fictitious coordinate for o.

### Shared Donors Give Safe Joins

An interior backing cell can back at most two double requesters, and if
there are two they are opposite. Indeed a requester immediately east
of w makes w's north and south neighbours nonpositive. They therefore
cannot themselves be requesters. Only a requester west of w remains
possible.

If two occur, their positive corridors point respectively east and west.
Joining them through their two zero R edges and w orders their straight
intervals on one row, hence saves one full A-unit length allowance.
There is no overlap of the straight projections. The vertical case is
the rotation of this argument.

Every double requester has just one backing location. These pairs are
therefore vertex-disjoint. Neither vertex participates in the earlier
dirty matching: both its dirty strands have only one positive end.
Nor can it participate in the clean matching, whose junctions are
regular. All these joins can consequently be made simultaneously.

Pair every two requesters sharing a backing cell. Let nu_B be the number
of these new joins, and let q_B count unpaired requests, including
exterior-backed ones. The remaining interior backing locations are
distinct. Pay each remaining half-unit request by (26), or by its
reserved exterior-port half unit. A backing cell is nonpositive, so
these donations are disjoint from every positive charge in (25).

Let p_4 be the total payment made from positive J_4 charges: pay one at
each s=1 vertex with one-sided debit, and one-half at each s=2 vertex
with at least one such strand. Set

```text
R_4=p_4+q_B/2.
```

This is an allocation from specified, disjoint terms of C_rest, so
`C_rest-R_4>=0`. Exactly,

```text
E_4=p_4+(q_B+2nu_B)/2=R_4+nu_B.                   (27)
```

Each new join supplies three units; its two remaining half-unit requests
cost only one in total. Thus it even leaves two units of surplus. This
payment does not use beta_0, z, or an additional copy of c.

### The J4-Free Residual

Put

```text
L_B=g_+-nu_C-nu_D-nu_B.
```

The new and old joins are endpoint-disjoint and preserve their chain
axes, so `X_2<=A L_B`. Substituting (27) into (22) gives

```text
S >= 3L_B+1+(C_rest-R_4)+2nu_B-D_C+3nu_C-E_3.
```

Consequently

```text
D_B=max(0,D_C+E_3-(C_rest-R_4)-2nu_B-3nu_C),
3(f-T)<19+D_B.                                    (28)
```

This proves the following strengthened zero-isolate-error theorem:

> Suppose no one-bend dirty strand has exactly one positive J_3 end,
> and every clean through strand has at least five knight pairs.
> Then `f<=T+6` for `n=3k+2>=11`, with arbitrary isolates and arbitrary
> numbers of one-sided J_4 events.

The clean-length premise may instead be replaced by its displayed
payment in (28). This closes E_4, not just E_4 up to a multiple of z.

### J3 Backing-Cell Classification

Here is a further local deduction for E_3. It is stated separately
because a local donor inequality is not yet a global allocation.

Normalize a remaining event so that its positive J_3 cell is v=(0,0),
its corridor points east, its deleted leaf is north, and its dirty bend
is south. The forced labels include

```text
F at (0,2),(1,2),(2,2),(1,-1),(2,-1),
isolated hole u=(0,0),
dirty bend b=(0,-1),
nonpositive crossing anchor h=(-1,-1).
```

The dirty bend's F corner is (1,-1), and h is its other anchor. If the
west neighbour of v is an exterior port, the isolate u is on the west
boundary and the dirty bend has o as its other anchor instead. In that
case the dirty exterior incidence retains a whole unit in T_rem, which
pays this E_3 event. Such incidences are distinct from the dirty ports
used for the exterior-backed J_4 events. They belong to different dirty
strands and positive endpoints.

Now consider the interior-backing case. Write w=(-1,0). Its east and
south neighbours are v and h, both crossings. Its north cell contains
F at (0,2), and is therefore a leaf or bend. The west neighbour may
be a cell of any permitted type or o. Direct local counting gives:

| North neighbour of w | West neighbour of w | V_rem(w) |
|---|---|---:|
| Leaf | Bend | 1 |
| Bend | Leaf | 1 |
| Bend | Bend, at least one of these bends clean | 1 |
| Leaf | Crossing or o | 1/2 |
| Bend | Crossing or o | 1/2 |
| Bend | Bend, both dirty | 0 |

Two perpendicular leaves are forbidden, so the table is exhaustive.
For the bend/bend rows the allowed west F corner is either (-2,1),
giving one clean and one dirty bend, or (-2,0), giving two dirty bends.
Two clean bends do not actually occur in this normalization. The table
uses V after subtracting its actual dirty incidences, not a second copy
of the junction's original charge.

In the first three rows, w has precisely one positive neighbouring
junction, namely v: north/west are non-crossing cells and south is h.
Hence another event cannot use w as its backing cell. Nor can w be a
J_4 donor in (26), since such a donor has at least three crossing/exterior
neighbours, whereas these rows have two non-crossing cell neighbours.
These E_3 events are therefore paid injectively by their whole units at
w. This payment is simultaneous with the preceding J_4 payment.

The exterior-backed E_3 events and these three full-unit rows give
additional completely paid classes. Let R_3 count them and subtract
their specified units from `C_rest-R_4`. Removing the same R_3 events
from E_3 in (28) is valid and introduces no growing error.

### What The Half-Unit Rows Supply

In either crossing/exterior west-neighbour row, w has two isolated
bottom corners, u=(0,0) and u'=(-1,0). Its south neighbour h has those
two isolates as its upper corners and has the original dirty bend to
its east. This forces h to be J_4. Its unused charge satisfies

```text
V_rem(h)>=1/2,
```

except when h's west neighbour is a dirty bend with F corner (-2,-1).
In that exception `V_rem(h)=0`. The exceptional west bend is a one-bend
dirty strand around u', between h and the cell t=(-2,0). Existence of
the west bend and of w ensures that t is a board cell, not an exterior
anchor. It is a crossing by the crossing/exterior row of the
backing-cell table.

To verify the assertion, h already has one F-neighbour incidence at its
lower-right corner from (1,-1). Its lower-left corner either has none,
giving s=3 and one dirty port with spare charge one-half, or has its
unique F neighbour west or south. A west F at (-2,-1) gives a second
dirty port and spare charge zero. A south F at (-1,-2) gives a clean
bend port and spare charge one. No leaf is possible: its additional F
endpoint would neighbour u' or conflict diagonally with (1,-1).

If t is a nonpositive junction, the exceptional one-bend dirty strand
has two nonpositive ends and contributes an additional half unit in
(20). This is a real surplus discarded in (22).
If t is positive, its corridor must point west. A northward first
straight cell would require F at (0,1), a neighbour of the original
isolate u. Its south neighbour is the exceptional dirty bend, while
its east neighbour is w, so no other positive direction is possible.
Its corridor and the one at v have ordered horizontal projections and
admit a safe join through the backing region.

Thus a single half-unit-row event has the following physical prospects:
half at w and half at h; half at w and the surplus of a nonpositive
one-bend strand; or a safe join to an opposite positive corridor. This
is not an appeal to the component credit z.

### What The Zero-Unit Row Supplies

In the last row of the table, w's north and west bends have F corners
(0,2),(-2,0). Both point to the same additional isolated hole (-1,1).
The opposite cell t=(-2,1) is either a bend or a crossing.

If it is a bend, these form a three-bend dirty loop at w. Both loop
incidences are nonpositive, so its summand in (20) is

```text
3-5/2+2=5/2,
```

more than the unit needed by this local event. If t is a nonpositive
crossing, the two one-bend dirty strands between w and t each have two
nonpositive ends and together have surplus one. If t is positive, its
corridor must point west: a northward first straight cell would force
F at (0,3), making a forbidden turn with the already forced horizontal
FF edge `(0,2)(1,2)`. The east/south directions go to the two bends.
Again t's westward corridor can be joined safely to v's eastward one.

This identifies actual surplus or a metric join in every local
zero-unit-row case. It does not assign the same two-strand surplus
independently to a second event backed at t.

The three-bend-loop subcase can in fact be paid simultaneously now.
Its only anchor is w, and that w has only one positive neighbouring
junction: v, since its north/west neighbours are bends and its south
neighbour is h. Thus at most one E_3 event asks this loop for payment.
Use one of its 5/2 surplus units for that event. Such loops have no
selected dirty join, and all their positive surplus was discarded in
(22), so this neither reduces C_rest nor reuses an earlier payment.
The E_3 count in (28) can therefore be reduced by the number of these
loop-backed events without a corresponding subtraction from C_rest.

### Unresolved Joint Allocation

The remaining obstacle is now genuinely simultaneous, not the absence
of a local candidate payment. The half-unit and zero-unit rows can
request a bank at another junction, a surplus on a dirty strand, or a
new safe join. Those objects can also occur in another event's candidate
set, in the J_4 backing allocation, or at an endpoint used by an earlier
matching. A complete proof must replace, rather than add to, any old
allocation that it reroutes.

For example the half-unit at h can also be the half-unit backing donor
for a J_4 double requester to its west. Claiming half for each request
would spend a single half unit twice. The geometry in this situation
offers opposite positive corridors, but a simultaneous selection and
payment theorem is still required. Likewise, the surplus of two
nonpositive one-bend strands between w and t is one total unit, not one
unit for each anchor.

A precise sufficient next step is a capacitated allocation using the
remaining unspent local V_rem/T_rem tokens and the positive dirty
summands retained from (20), together with a replacement collection of
safe clean/dirty/backing joins. Every token must have its actual capacity,
and each positive corridor-end junction may be used by at most one join.
The needed conclusion is a payment for all remaining E_3 events with
only an absolute error, while retaining the clean-strand debt separately.
No Hall inequality, degree-two reduction, or rank argument establishing
that conclusion is proved here.

In particular the existence of the local alternatives just listed is
not by itself a proof of such an allocation. The completed new results
are the full E_4 payment (25)--(28), the exterior, full-unit, and
three-bend-loop E_3 payments, and the remaining E_3 local classification.
The unrestricted arbitrary-isolate payment still awaits the joint
allocation; no new universal constant-gap claim is made. No grid optimization or finite
grid checks were used in this continuation.

## Simultaneous Donor Allocation

Status: new paper proof, not independently reviewed here. All preceding
text is left unchanged. This continuation proves an isolate extension
relative to the explicitly retained clean budget below. It does not
prove the unrestricted clean-strand certificate or the unrestricted
constant-gap upper bound.

The allocation is rebuilt from (20), not from an irrevocably frozen
choice of the J_4 backing donations in (27). In particular old backing
joins nu_B and their donations are returned before making the choices
below. The clean matching nu_C and the doubly-positive dirty matching
nu_D can be retained. None of the new join endpoints is used by either
of those matchings.

### The Resources Before Allocation

Retain separately the following resources from the exact equation (20):

* The local values V_rem(v) at individual nonpositive junctions.
* The local positive J_4 values one and one-half from (25).
* One unit at each dirty exterior incidence inside T_rem.
* One-half at each one-bend dirty strand with two nonpositive ends.
* Five-halves at each three-bend dirty loop with a nonpositive anchor.

The last two are positive dirty summands discarded in (22), not additional
copies of V_rem. They are available after the one-unit payments to dirty
incidences in N_J and N_o. The remaining part of T_rem is nonnegative.
No resource in this list uses beta_0 again.

Pay the p_4 positive-junction charges exactly as in the preceding
continuation. The still-unpaid demands are:

```text
one unit at each positive J_3 one-sided event;
one-half at each positive J_4 double requester.     (29)
```

All these demands are attached to distinct positive corridor-end
junctions and have size at most one. Positive J_4 vertices with one
one-sided strand have already been paid; those with s=1 and two such
strands have also been paid. Some of these paid vertices will be free
auxiliary endpoints for new joins.

Boundary demands use the distinct residual dirty exterior incidences
identified above. A loop-backed J_3 event uses one unit of its private
five-halves loop surplus. These payments are disjoint and are made first.
Leave the full-unit backing-cell J_3 donations uncommitted for now:
their donors can also be requested by a half-unit-row event.

### Two Elementary Direction Rules

Two physical rules will be used to control donor multiplicity.

First, a positive irregular junction having a zero R edge has that edge
on the axis of its positive corridor, behind the corridor. This follows
from the eastward normal form in the positive-port lemma: a positive
irregular J_3 has its only other R edge west; a positive J_4 with s=2
has the same two R directions. A positive J_4 with s=1 has no zero R edge.

Second, two perpendicular positive rays cannot start at two neighbours
of the SAME backing cell and point away from it. Put that backing cell
at (0,0). East and north rays would have their first straight cells at
(2,0),(0,2). These force the FF edges

```text
(2,2)(3,2),       (2,2)(2,3),
```

making a forbidden carrier turn. This is the distance-two version of
the earlier local nonbranching argument. It also holds near the boundary:
existence of the straight cells requires the displayed leaf cells and
their F vertices to exist.

Consequently a cell has at most two positive neighbouring junctions
whose corridors point away from it; if there are two, they are opposite.

### Direct Joins Are Disjoint

Consider first the local J_3 alternatives in which a proposed surplus
strand instead reaches a positive junction t. These must be settled
before constructing donor requests.

In the half-unit-row normal form, t=(-2,0) points west, while the original
event v=(0,0) points east. If the upper neighbour of w=(-1,0) is a leaf,
then F(-1,2) is present. The first straight cell west of t forces
F(-2,2), so t also has a north leaf. It is a positive irregular J_3,
with a one-bend dirty path to h=(-1,-1). It is precisely the symmetric
half-unit-row event whose positive alternative is v. This gives a pair
of J_3 demands, not a new unclassified endpoint.

If the upper neighbour of w is a bend, F(-1,2) is absent. The same
westward corridor at t forces F(-2,2). The north bend of t and the
north bend of w form a two-bend dirty strand around (-1,1). Thus t is
a positive J_4 with exactly a one-bend dirty strand to h and a two-bend
dirty strand to w. Both other ends are nonpositive. Its one-sided
debit was paid by its positive one-half charge, and it is a free
auxiliary endpoint. Its unique one-bend dirty port and corridor
direction determine the original event v uniquely.

In the zero-unit-row normal form, a positive t=(-2,1) has the two
one-bend dirty paths to the nonpositive w=(-1,0). It is a positive J_4
with s=1, already paid by its positive unit. The only possible original
event is a positive neighbour of w. Its other two neighbours are bends,
and the direction rule excludes having two such positive neighbours.
Hence this auxiliary endpoint also belongs to just one direct pair.

The three types of pairs cannot overlap: a J_3 direct partner is the
mutual half-unit-row partner; the J_4 auxiliary types have respectively
one one-bend and one two-bend dirty strand, or two one-bend dirty strands
around one isolate. Each is uniquely assigned as just described.

Select all these direct joins. They have ordered horizontal projections
in the normal forms, and rotations give the other cases. A pair contains
either two demands or one demand and a previously paid auxiliary vertex,
so its remaining cost is at most two. Its three-unit join saving pays
that cost completely. Delete the paid demands from the donor problem.
None of these vertices had a doubly-positive dirty strand or was regular,
so no clean or old dirty join is lost.

### The Remaining Demand Bundles

Every remaining demand now has a bundle of actual resources of exactly
its size. The bundles are fixed by the local classification:

| Demand | Requested bundle |
|---|---|
| Full-unit-row J_3 | One unit at its backing cell |
| Half-unit-row J_3, spare charge at h | Half at w and half at h |
| Half-unit-row J_3, zero spare at h | Half at w and half at the exceptional nonpositive one-bend strand |
| Zero-unit-row J_3, opposite anchor nonpositive | Half at each of the two parallel nonpositive one-bend strands |
| Interior J_4 double requester | Half at its backing cell |

The direct-join step ensures that all strand resources in this table
really have two nonpositive ends. Exterior and loop-backed demands
were already handled privately.

It remains to show that every overload in these bundles can be removed
by vertex-disjoint safe joins. No generic inference from the existence
of one bundle per demand is being made.

### Junction Donor Multiplicity

A junction resource can be requested in two ways:

* As a backing cell by an adjacent positive junction.
* As h by a half-unit-row J_3 event.

The second role requires at least two isolated corners and a dirty
one-bend port to that event's positive junction. When its spare charge
is positive, the local classification of h gives exactly

```text
J_4, s=3, one dirty port, spare 1/2; or
J_4, s=2, one dirty and one clean port, spare 1.     (30)
```

In particular there is at most one request of the second kind at a
given donor: its sole dirty port determines that event.

For backing requests, the direction rules allow at most two, opposite.
A full-unit-row backing cell has two non-crossing neighbours, so cannot
back a second positive junction. A half-unit-row backing cell with an
opposite positive neighbour was one of the direct-join cases and no
longer has that J_3 demand: in its normal form that neighbour's first
straight cell forces F(-2,-1), precisely the exceptional zero-spare
case at h. The only remaining two-backing-request case
is two opposite J_4 double requesters. Their donor has four crossing
neighbours, hence s=4, no dirty port, and spare charge one. Their two
half requests fit exactly and there is no request of the second kind.

There is one further exclusion: a half-unit-row backing cell cannot
also be a positive-cap donor of the second kind. If its north neighbour
is a leaf, it has no dirty port. If that neighbour is a bend, it is its
only dirty port. In the normal form its possible one-bend partner is
the cell (-2,1). A positive north corridor there would require F(0,3),
turning the already horizontal carrier through (0,2). A positive west
corridor would require F(-2,0), a corner of the crossing cell immediately
west of w. Both are impossible. If that cell is outside the board,
there is no positive partner there either. A longer dirty path cannot
give the second-kind request, which specifically uses a one-bend path.

Thus only a full-unit-row backing request or a J_4 double request can
collide with an h request. Their geometry is exact. Normalize the latter
event to v=(0,0), pointing east, so h=(-1,-1). Its east neighbour is the
original dirty bend, its north neighbour is the nonpositive w, and its
upper two corners are isolates.

A positive neighbouring back requester can only lie west of h. A south
ray would have first straight cell (-1,-3), forcing F(1,-2), which turns
the already horizontal FF edge `(1,-1)(2,-1)`. The north and east
neighbours are already unavailable. By the axial rule a west requester
points west, opposite to v.

In the spare-one-half case of (30), that west requester is a J_4 double
requester: its north and south bends are one-bend dirty strands to the
nonpositive north and south neighbours of h. The latter south neighbour
cannot be positive: its zero edge north to h would force a southward
positive direction, excluded by the same FF-turn argument.

In the spare-one case of (30), the west requester is a J_3 full-unit-row
event. Its south neighbour is a leaf, forced by F(-1,-2) and the FF
edge required by its first westward straight cell. Its north dirty bend
is one-bend with nonpositive other anchor w. Its backing h has one clean
and one dirty bend, exactly the full-unit row of the table.

The complete overload list for junction donors is therefore

```text
capacity 1/2: one half-row J_3 asks 1/2,
              one double J_4 asks 1/2;
capacity 1:   one half-row J_3 asks 1/2,
              one full-row J_3 asks 1.              (31)
```

In either case the two positive corridors are parallel, point away,
and have disjoint ordered projections. Join them. The two demands cost
at most two, so the three-unit saving pays them without taking anything
from their proposed donors.

These collision pairs are vertex-disjoint. A half-row event has at most
one collision, at h, since its own backing donor has no competing
second-kind request and no remaining opposite backing request. A
full-row event or a double requester has only its one backing request
and is not itself a half-row event. At that backing cell there is at
most one h request. Thus the junction-overload graph is a matching,
not an arbitrary graph for which an unproved Hall bound is needed.

### Strand Donor Multiplicity

The half-unit strand donor in a half-row bundle is never one of a pair
of parallel one-bend dirty strands. In that normal form its isolate is
u'=(-1,0), its F corner is (-2,-1), and the opposite possible F corner
would be (0,1). But (0,1) neighbours the original isolate u=(0,0), so
it is U. The two other diagonal corners also lie in the specified
crossing anchors. This donor belongs to an isolate with just one
incident bend.

Such a donor can be requested by at most one half-row event. Normalize
its isolate to (0,0) and F corner to (-1,-1). The two possible requesting
events have cell positions and directions

```text
(1,0), eastward;       (0,1), northward.
```

These are the two reflections of the half-row construction that preserve
the specified isolate and F corner. If both existed, their first straight
cells (2,0),(0,2) would force the forbidden FF turn at (2,2). Thus its
half-unit donation is private. This is a geometric multiplicity bound,
not a choice to assign the donor to whichever event is considered first.

It follows also that half-row strand donors and zero-row strand donors
are disjoint classes: the latter require two opposite F corners and two
parallel one-bend dirty paths around the SAME isolate.

For a zero-row pair, both anchors w,t are nonpositive. At each anchor
there are two perpendicular bend neighbours. At most one of the other
two neighbours can be a positive back requester, by the distance-two
direction rule. Therefore at most two zero-row events request this
pair's one unit of total surplus, one at each anchor.

If both requests occur, they give a safe join. In the earlier zero-row
normal form the first event is v=(0,0), pointing east, w=(-1,0),
t=(-2,1), and F(0,2) already extends horizontally to (1,2). A positive
back requester north of t would have its first straight cell (-2,3),
forcing F(0,3) and a forbidden turn. The second requester must therefore
be west of t and point west. Its straight interval and v's interval
are ordered and disjoint in their horizontal projections.

Join the two requesters and pay their two units with the three-unit
saving. This pair is disjoint from every junction-collision pair:
zero-row events request only this pair of strand donors, not junction
donors. It is disjoint from other strand-collision pairs because each
zero-row event has only one such pair. If only one request occurs,
its two half donations fit the one-unit strand capacity exactly.

### A Simultaneous Allocation Theorem

The construction can now be assembled without an augmenting-path loss:

1. Pay positive J_4 credits, private exterior demands, and private loop demands.
2. Select the disjoint direct joins and remove their paid demands.
3. Form the fixed resource bundles for all remaining demands.
4. Select the disjoint junction-overload and strand-overload joins, and
   remove both demands of each selected pair.
5. Pay every remaining bundle from its specified donors.

The capacity proofs above show that step 5 has no overloaded donor.
The selected pairs in steps 2 and 4 are disjoint. All their endpoints
are irregular one-sided positive endpoints or the explicitly classified
free auxiliaries, so they are also disjoint from the retained clean and
doubly-positive dirty matchings. All new joins preserve one corridor
axis and order their straight intervals. Hence their union with the old
joins has no closed chain and no repeated corridor-end junction.

This is a finite demand-donor allocation proof. The only overloaded
resource components are the two-demand components explicitly classified
in (31) and the two-anchor zero-row pairs. No assumption that a generic
forest-shaped incidence graph satisfies Hall is used. In fact ordinary
acyclicity alone would not prove that assertion: arbitrarily many demand
leaves could share one small donor in a star. Here the forced FF turns
exclude those multiplicities before the matching is chosen.

Let nu_N count the new joins. Each pays at most two units of remaining
demand out of its three-unit saving. Every other payment comes from a
disjoint part of V_rem, T_rem, or a positive dirty summand in (20).
There is consequently no remaining E_3 or E_4 debt. There is no charge
proportional to z, and no isolate component credit is spent again.

### The Retained Clean Certificate

Here is an explicit conservative consequence that does not assume the
old clean certificate can still spend donated junction or port resources.
Put

```text
B_C=3beta_0+t_0+3delta/2+C_C,
L_N=g_+-nu_C-nu_D-nu_N.
```

The physical joins give `X_2<=A L_N`. Return to (20), use the dirty
half-matching payment for doubly-positive strands, and use the simultaneous
allocation above for all one-sided dirty events. Discard all unused
V_rem/T_rem resources, all unused positive dirty surplus, and the at
least one-unit surplus of every new join.

For an explicit algebra check, let Q_D be the sum of the nonnegative
dirty summands excluding the one-sided one-bend strands and the
doubly-positive one- or two-bend strands. The resource allocation proves

```text
E_one<=V_rem+T_rem+Q_D+3nu_N,
sum_dirty summands>=Q_D-E_one-3nu_D.
```

These inequalities, with `d_C/2-2P_C=C_C-D_C`, give

```text
S >= 3L_N+1+B_C-D_C+3nu_C.                         (32)
```

In particular the sufficient residual is now purely clean:

```text
D_iso_free=max(0,D_C-B_C-3nu_C),
3(f-T)<19+D_iso_free.                              (33)
```

No magnitude or sign of E_one is assumed in (32),(33). These deductions
use the unchanged physical exceptional-area bound Q_exc<=10K and
K>=S+1. F empty is trivial; for nonempty F the identity
`beta=z+beta_0` used in (20) is valid with beta_0>=0.

**Isolate-extension theorem.** For n=3k+2>=11, if every clean through
strand has at least five knight pairs, then f<=T+6, with arbitrary
globally isolated holes and arbitrary dirty strands. More generally,
the same conclusion holds whenever `D_C<=B_C+3nu_C` for a valid clean
eligible matching.

For example, clean short through strands of two through four pairs,
all eligible, are paid by their own half-matching: their individual
debits are at most 3/2, and each selected join supplies three units.
All longer clean strands are already paid. This combines with the
isolate extension without any bound on z or on the number of dirty
one-bend terminal events.

The retained bank B_C deliberately excludes V_rem and T_rem, which may
have been consumed in paying isolates. Thus this theorem does not claim
to preserve a clean certificate that had already spent those same
resources. It is an unconditional isolate extension relative to the
displayed, non-reused clean certificate, not to an unspecified stronger
isolate-free hypothesis.

### Status After Allocation

The growing isolate error is eliminated in (33). What remains for a
global constant-gap theorem is the pre-existing clean short-strand
problem: a uniform payment for D_C from the retained bank, safe clean
joins, or further actual length loss. The clean one-pair and ineligible
two- to four-pair cases have not all been closed here.

This appendix uses only exact packet budgets, finite graph matching,
and the displayed coordinate exclusions. No grid optimization, finite
grid feasibility checks, or Lean work was performed. The simultaneous
allocation is a new paper claim and should be reviewed as such; it is
not described as independently audited or formally verified.

## Clean Endpoint Resources

Status: new continuation. The user reports independent audit of the
arbitrary-isolate allocation through the preceding line 1383. This
section preserves that prefix and does not extend its audit status to
the new claims below. The unrestricted constant-gap theorem remains open.

There are substantive clean-strand resources left by the isolate proof.
In particular its conservative B_C discarded some entire classes of
clean ports, some nonpositive junction charges, and at least one unit
per newly selected isolate join. Recovering these does not require
claiming that every nonpositive anchor is free or rebuilding the already
audited donor assignment.

The definitions of clean/dirty paths, positive junctions, nu_D, nu_N,
D_C, C_C, and B_C are unchanged. Write a_C(v),a_D(v) for the numbers
of clean and dirty bend ports at a junction, including pendant clean
ports. Thus

```text
a_C+a_D=2-s(v) at J_3,
a_C+a_D=4-s(v) at J_4.
```

Every port refers to its actual incident edge, not an arbitrarily chosen
endpoint of a carrier. Through loops contribute two distinct incidences.

### Clean Exterior Ports Are Untouched

Split `t_M=t_MC+t_MD` according as the exterior bend edge belongs to a
clean or dirty path. All dirty paths are through, so `t_MD=N_o`. Exactly,

```text
T_rem=2t_M-N_o=2t_MC+t_MD.                          (34)
```

The audited allocation spends exterior tokens only from the dirty
incidences in the last term. In particular it never spends the two units
at a clean exterior bend edge. This remains true for a clean pendant
path, and for a through strand with two exterior anchors: its two ports
are distinct physical edges even though both abstract endpoints are o.

Consequently every clean short through strand touching o can pay its
entire debit from that port, since its debit is at most two. Different
strands use different ports. This is a simultaneous payment for arbitrary
numbers of exterior clean strands, with arbitrary isolates; it is not
an extra use of the aggregate boundary count b.

### Untouched Junction Types

For a nonpositive junction, its local contribution after the original
N_J payment is exactly

```text
V_rem(v)=1/2+a_C(v)/2-a_D(v)/2       at J_3,
V_rem(v)=1+a_C(v)/2-a_D(v)/2         at J_4.         (35)
```

The audited isolate allocation requests a nonpositive junction bank only
as a backing cell or as the other anchor h of a half-row event. The
coordinate classifications in the prefix show that all such requests
are among the following types:

```text
J_3: s=1 or s=2;
J_4: (s,a_D)=(2,1),(2,2),(3,1),(4,0).
```

The zero-spare (2,2) case actually donates strand surplus, not a positive
local charge. Keeping it in this list is harmless. No token from another
nonpositive type is used by the isolate allocation. In particular an
anchor with no isolated corner is never an isolate backing donor.

The following per-clean-port credits are therefore available jointly.
A row with a_C=0 is not used. The value is deliberately rounded down
in one row to keep the allocation simple.

| Anchor type | Number of clean ports | Credit per clean port |
|---|---:|---:|
| Nonpositive J_3, s=0 | 2 | 3/4 |
| Nonpositive J_4, s=0 | 4 | 3/4 |
| Nonpositive J_4, s=1, a_D=0 | 3 | 3/4 |
| Nonpositive J_4, s=1, a_D=1 | 2 | 3/4 |
| Nonpositive J_4, s=1, a_D=2 | 1 | 1/2 |
| Nonpositive J_4, s=2, a_D=0 | 2 | 1 |
| Nonpositive J_4, s=3, a_D=0 | 1 | 3/2 |

Multiply the last column by the middle column and compare with (35).
The results are at most the corresponding local bank in every row.
For example s=1,a_D=0 at J_4 has bank 5/2 and needs only 9/4.
This distributes one actual vertex bank across its ports; it does not
offer the whole bank independently to every strand meeting that vertex.

There is one additional positive-junction credit. A positive J_4 with
s=1 has one clean port and local bank one. If its two dirty ports are
NOT one-sided one-bend strands, this unit is untouched and may be assigned
to its clean port. Indeed the dirty ports either form a three-bend loop,
or two one-bend strands to the same anchor. In the latter case the other
anchor is positive under the stated exclusion. Neither case has a p_4
payment or uses this vertex as a direct auxiliary in the audited
allocation. Its participation in a dirty matching uses a length saving,
not this local unit.

We do not give this unit to a positive J_4 with two one-sided one-bend
strands. Its bank may already have been spent in p_4.

### Zero Exterior Corridors Retain Their Port Charge

The definition of V in (18) contains a separate term `3t_R0/2`. The
audited donor requests use local junction contributions, not that
exterior half-edge term. It too remains unspent.

In particular let v be a nonpositive regular J_3 whose unique zero R
edge goes directly to o. Its local bank is 3/2 and that exterior edge
supplies another 3/2. Its two clean ports can therefore each receive
credit 3/2, replacing their ordinary 3/4 credit in the preceding table.
The R edge and its exterior incidence are unique at v. Different such
vertices use different exterior edges, including multiplicity at o.

This gives a genuine one-positive-end payment for a two-pair clean
strand ending at such an anchor: its entire 3/2 debit is paid there.
The other endpoint may have any permitted type or direction. Neither
endpoint is falsely treated as an eligible join.

Only these specified exterior R incidences are allocated in this
refinement. Other unused t_R0 charge is simply left unspent. A clean
exterior bend port and an exterior R port are different actual edges,
so their two allocations cannot coincide.

### Private Clean Strand Payments

For each clean through strand s let

```text
d_s=max(5-k_s,0)/2.
```

Give each of its endpoint incidences the credit alpha from the preceding
table, its zero-exterior-corridor refinement, or its clean exterior bend
port. For a permitted positive J_4 clean port use alpha=1. Give all
unlisted types alpha=0. These are port credits, so loops are handled by
their two distinct incidences.

Put

```text
e_s=min(d_s,alpha_first(s)+alpha_last(s)),
E_C=sum_clean through e_s,
D_port=sum_clean through (d_s-e_s)=D_C-E_C.         (36)
```

Pay e_s from its two endpoint slots, using at most the assigned alpha
at either end. For example first take the smaller of d_s and the first
slot, then take the remaining required amount from the second. Every
port belongs to one path, so this is an injective simultaneous allocation.
Unused slots at pendant paths or long through strands are not claimed
as payments to unrelated short strands.

The construction proves the following actual short-strand payments:

* Every short clean strand with an exterior bend anchor is fully paid.
* A two-pair strand is paid by two endpoint slots of at least 3/4, or
  by one slot of at least 3/2, irrespective of its endpoint directions.
* A three-pair strand is paid by two half-unit slots or one unit slot.
* A four-pair strand is paid by one half-unit slot.
* A one-pair strand is paid whenever its two slots sum to at least two,
  for example an exterior bend port, or a zero-exterior regular J_3
  endpoint together with any listed half-unit endpoint.

The two-positive regular-J_3 strands have no credit from this table.
Their length joins or some other geometric payment are still needed.

### Isolate Joins Donate Their Actual Surplus

There is also a nonlocal retained resource, but it is already quantified
by the audited allocation rather than postulated from component counts.
Every new isolate-allocation join pays at most two units of demands,
out of its three-unit length saving. Thus the isolate resource inequality
can be strengthened to

```text
E_one <= V_rem+T_rem+Q_D-E_C+2nu_N.                (37)
```

Here E_C is subtracted because its endpoint payments use resources that
the audited allocation never requests. If some of those payments use
the separately retained `3t_R0/2` term, that term is already part of V_rem
in the aggregate notation of (20); only its local allocation was absent.
All other unused resources on the right of (37) are retained merely as
upper bounds on the isolate payment.

More explicitly, write the actual allocation as private-resource
payments plus payments for selected pairs. The former avoid the E_C
slots just proved private. Each selected pair costs at most two, even
if it contains two J_3 demands; an already-paid auxiliary costs zero
additional demand. Summing proves (37). This does not count the removed
endpoint insets as another length saving.

Let m_D count doubly-positive one- or two-bend dirty strands, as before.
The dirty half-matching leaves the nonnegative slack

```text
sigma_D=3nu_D-3m_D/2>=0.
```

It too may be retained: their total debit is at most 3m_D/2, rather
than the weaker 3nu_D used in (32). This slack is part of the same
matching payment, not a new rank credit.

### The Refined Clean Certificate

Let j_C count any selected collection of safe joins at regular positive
J_3 ends, with endpoint nonreuse and ordered straight projections. This
can be the earlier eligible matching. It can instead be the distinct
backing-FF joins from the opposed-double-fold construction in
PAPER_GLOBAL_CAP_PAYMENT.md. A combination is permitted only when its
endpoints are actually disjoint; their separate counts cannot simply
be added.

All such ends are disjoint from the dirty and isolate-allocation joins.
Consequently the same physical chain argument proves

```text
L_*=g_+-j_C-nu_D-nu_N>=0,
X_2<=A L_*.
```

Use (37) and the stronger dirty debit bound in the exact budget (20).
With the unchanged retained clean bank `B_C=3beta_0+t_0+3delta/2+C_C`,
the result is

```text
S >= 3L_*+1+B_C+nu_N+sigma_D-D_port+3j_C.           (38)
```

Hence the sufficient residual is

```text
D_*=max(0,D_port-B_C-nu_N-sigma_D-3j_C),
3(f-T)<19+D_*.                                     (39)
```

The endpoint payments E_C, the isolate-join surplus nu_N, and the dirty
matching surplus sigma_D have been allocated from distinct, explicitly
unspent parts of (20). Equations (38),(39) do not spend the already
donated V_rem or T_rem tokens again.

**Endpoint-payment theorem.** On n=3k+2>=11, if every clean short through
strand is paid by the endpoint slots above, then f<=T+6, with arbitrary
isolates, dirty strands, and clean pendant or long through paths.

One can also allow any additional eligible clean two- through four-pair
strands. At their regular positive ends the slot credits are zero, so
their remaining costs are at most 3/2 each. Their own half-matching pays
them simultaneously. Alternatively, additional short strands may all
belong to actual backed double folds: the fold incidence bound in the
separate cap note
gives at least one private backing join per fold, paying the two
3/2-debit strands together. These are two sufficient alternatives;
combining overlapping eligible and fold joins requires a new joint
selection argument.

These results newly permit unbounded numbers of noneligible clean
strands with zero or one positive end. They are not consequences of
assuming those strands were eligible or had at least five pairs.

### What Still Prevents Closure

The new allocation does not pay every short clean strand. Its remaining
deficits have concrete examples at the level of the proved credits:

```text
one pair, two ordinary nonpositive regular J_3 ends:
    debit 2, available endpoint credit 3/2, remainder 1/2;
one pair, one regular positive end and one ordinary nonpositive
    regular J_3 end:
    debit 2, available endpoint credit 3/4, remainder 5/4;
two pairs, same-facing regular positive ends:
    debit 3/2, endpoint credit zero, no direct eligible join.
```

These are deficits of the sufficient allocation, not asserted feasible
families or counterexamples. In the all-one-pair eligible case, E_C=0
at all through endpoints; with z=0 there are no new isolate joins to
donate nu_N. Thus this continuation does not evade the known difficult
case by relabelling it as an isolate payment.

The tempting uniform extension 'one unit per nonpositive clean port'
is not supported by the available bank. A nonpositive regular J_3 has
two such ports and only 3/2 local units. Worse, a nonpositive J_3 with
s=1 and its one clean port can have its whole unit already assigned to
an isolate cap. A J_4 with s=2, one clean and one dirty port can have the
same problem. Such excluded nodes need a joint rebuilt allocation, not
an independent clean-port donation.

No proof here forces enough backed partners for the same-facing folds,
or enough private width loss at the remaining clean seam ends. The
global cap note's scalar and planar-order counterchecks remain relevant:
ordinary forest acyclicity and a count of deletion components do not
supply the missing metric width. The next required input is an actual
join/donor rule for the residual clean events that respects (38), or a
new low-K geometric restriction ruling them out in aggregate.

Only this new section was appended. No grid optimization, finite grid
checks, or Lean work was performed. The new results are the protected
clean endpoint slots, the retained isolate/matching surplus, and their
simultaneous non-reusing certificate, not an unconditional global bound.
