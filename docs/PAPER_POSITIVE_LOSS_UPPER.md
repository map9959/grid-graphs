# Paper Positive-Loss Upper Research

Date: 2026-09-07. Paper deductions, a refuted universal candidate, and
unresolved restricted candidates.
No global constant-gap upper theorem, independent review, or Lean verification
is claimed. Only this note was edited; no build or grid search was run.

## Scope

Use the fixed orientation and actual-component conventions of
[Half Coefficient](PAPER_HALF_COEFFICIENT_UPPER.md),
[Packing Stability](PAPER_PACKING_STABILITY.md), and
[Zero Loss](PAPER_ZERO_LOSS_UPPER.md). In particular,

```text
n=3k+2, k>=3, Q=k-1, N=3Q+1, T=3k^2+7k,
e=f-T (signed), GOOD=3Q^2-Lambda,
4e+c+h+K+Lambda+Omega=2Q+13,
Omega=b+p-8-BAD>=0, K>=5.
```

The objective is a bound independent of both Q and Lambda. This note proves
a joint local bound for bad edges and derives a boundary-aware contact target.
The original universal nonnegative-loss target (8) is **refuted** by the
explicit feasible family below, checked from its coordinates and disjoint
supports. Its positive-excess restriction remains open. An estimate `e<=C Lambda+C'`
would not finish the problem and is not presented as its solution.

## Bad Edges Consume Step Budget

Keep the scheduled sets A_t, vertical axes V_t, vacancies w_t, and run count
rho_t from the companion notes. Write

```text
delta_t=3(Q-|V_t|)-|A_t|,
sum_t delta_t=3Lambda.
```

Let j_t be the number of bad vertical edges at step t, so j_t is 0, 1, or 2.
Let B_t be the edge-left-column set of the bad horizontal edges on deep row 1
when t=1, and on deep row N when t=N-1; take B_t empty otherwise. Put
H_t=|B_t|. The two boundary steps are distinct in our range.

The following uses actual bad edges, without deleting them or changing d.

**Claim.** At every step,

```text
2 H_t + 3 j_t <= 2 delta_t.                         (1)
```

Here is the joint resource proof. At step 1 the assigned good rows are 2
and 3. At step N-1 they are N-2 and N-1. Thus B_t is disjoint from A_t by
the parallel-edge four-/six-cycle exclusions. Every edge of B_t is compatible
with V_t. The endpoint union of A_t union B_t therefore has

```text
|A_t|+H_t+rho(A_t union B_t)
```

columns, all outside the good vertical blocks.

A bad vertical edge at column 2 excludes horizontal endpoints at columns 2
and 3. It also excludes good vertical axes at 3 and 4. Consequently the two
columns {2,3} are outside both the good vertical blocks and the horizontal
endpoint union. At the other extreme the two excluded columns are
{3Q+1,3Q+2}. These pairs are disjoint. The horizontal compatibility assertion
holds for every scheduled row, and also for the boundary bad horizontal row
at its assigned endpoint step: in each case t is in its four-step shadow.

If A_t union B_t is nonempty, counting these disjoint resources in I gives

```text
3|V_t|+|A_t|+H_t+rho(A_t union B_t)+2j_t <= 3Q+1,
delta_t >= H_t+2j_t.                               (2)
```

If that union is empty, H_t=0 and

```text
3|V_t|+2j_t <= 3Q+1.
```

For j_t=1 or 2, integrality forces |V_t|<=Q-1, so delta_t>=3.
For j_t=0, ordinary packing gives delta_t>=0. These three cases prove (1).
Notice the exceptional inactive case j_t=2: it costs at least three units,
not the four units that an unjustified vacancy-only argument would demand.

Summing (1), with BAD_H and BAD_V denoting the two orientation counts, proves

```text
2 BAD_H + 3 BAD_V <= 6Lambda,
BAD <= 3Lambda.                                    (3)
```

There is a stronger bound `BAD_H+2 BAD_V<=3Lambda` if no step carrying a bad
vertical edge has A_t union B_t empty. No such hypothesis is assumed globally.
In particular (3) independently excludes all bad edges at Lambda=0, without
the global band classification.

This is only a boundary-edge estimate. Its constants alone do not pay the
contact errors: substituting BAD<=3Lambda into the desired final ledger loses
the entire useful sign of the Lambda term.

## Boundary-Aware Contact Ledger

Let H_A be the actual forced annulus graph, including isolates; let c_A and
r_A be its forced and induced-preserved component counts. Let C_o and C_i
count its preserved outer and inner corners. The annulus identity, which does
not require zero loss, is

```text
c_A=2K-8-r_A+C_o-C_i.
```

The following nonnegative quantities retain slack dropped in the zero-loss
numerical argument:

```text
beta=b-K=E+4-C_o >= 0,
R=r_A-p-h >= 0,
gamma=4-C_o+C_i >= 0.                              (4)
```

Here E is the scalar next-ring occupancy. Pure and shallow carriers remain
distinct annulus components, proving R>=0 even when a deep carrier's annulus
intersection splits into several pieces.

Suppose a literal contact selection has m=2d-L contacts, with L>=0. Contacts
are direct edges from deep F to the annulus or two-edge paths through a deep
hole between distinct retained components, at least one of which is deep F.
The latter definition also permits a two-edge contact to the annulus; this
enlarges the original selection class without changing its rank argument.
Require distinct physical edges, disjoint interior holes,
and no interior in a retained component. These are hypotheses, not conclusions
of positive-loss packing. Forest rank then gives

```text
c_A >= d-L+1,
2K >= r+5-L+R+gamma.                               (5)
```

An empty selection with L=2d is always legal, so the notion makes sense for
every configuration. The issue is its quantitative cost.

The actual deep mass identity and global forest ledger give, exactly,

```text
e=6+d-Q-K+BAD-Lambda,
d=e+Q+K-6+Lambda-BAD,
4e+p+h+K+b+c+Lambda-BAD=2Q+21.                     (6)
```

Substitute d into (5), obtaining

```text
K >= e+Q+p+h-1+Lambda-BAD-L+R+gamma.
```

Use this twice in (6), with b=K+beta. The result is

```text
6e+3p+3h+c <= 23+2L+3BAD-3Lambda-beta-2R-2gamma.    (7)
```

This improves the proposed defect-only target: beta, R, and gamma must not
be discarded before checking whether contacts can be paid.

The following original universal candidate is **REFUTED**, not merely unproved:

> There is an absolute constant C_*>=0 such that every feasible configuration
> admits the physical contact selection above with
>
> `2L+3BAD <= 3Lambda+beta+2R+2gamma+C_*`.             (8)

Its intended implication via (7) was the genuinely global conclusion

```text
e <= floor((22+C_*)/6)  for k>=3.
```

That implication does not rescue its false premise. The live restricted
candidate is:

> For k>=5 and e>0 only, there is an absolute C_*>=0 and a valid selection
> with `2L+3BAD <= 3Lambda+beta+2R+2gamma+C_*`.         (8+)

In this branch the existing missing-side closure supplies p>=4. If (8+) were
proved, (7) would give `e<=floor((10+C_*)/6)`; the e<=0 branch is harmless.
This would give a constant bound for k>=5, with k=3,4 already bounded by the
half-coefficient theorem. This is a conditional consequence, not an established
bound. A cardinality-maximum-only version is also not refuted by the family
below, but no such version is proved here.

The exact boundary reserve can also express the left-over cost in (8) as

```text
2L+2b+3p+K-24-3Omega-3Lambda-2R-2gamma.
```

This is substitution of BAD=b+p-8-Omega and beta=b-K, not a second source
of credit. In particular Omega and the bad-edge mirror count cannot both be
spent independently. Mirror UU edges remain unforced and cannot be used as
contacts in (5).

## A Canonical Physical Rank Version

There is a useful way to retain all contacts, including a signed surplus
beyond two per deep component. Contract every actual
deep F component and every component of H_A in the full forced forest. Keep
every deep hole as a vertex. This contraction creates no cycle, loop, or
parallel edge. Its anchors number d+c_A.

Let a count direct edges between a deep F component and the annulus. A deep
hole u has g(u) incident forced edges to anchors; there are no edges between
deep holes. Let z count the deep holes with g(u)=0. These are actual global
isolates, not virtual boundary components. Set

```text
S=a+sum_{deep holes u} max(g(u)-1,0),
D=2d-S,                    (D is signed),
eta=c-z-1 >= 0.                                   (9)
```

There is always at least one component containing an annulus vertex, proving
eta>=0. Counting edges minus hole vertices in this contracted forest gives

```text
S=c_A+d-c+z,
c_A=d-D+1+eta,
2K=r+5-D+R+gamma+eta.                             (10)
```

Thus the analogue of (7) is an exact equality:

```text
6e+3p+3h+c
  =23+2D+3BAD-3Lambda-beta-2R-2gamma-2eta.          (11)
```

In this feasible grid, g(u)<=2. Every forced edge at a hole has a preserved
neighbor. Two perpendicular preserved neighbors are diagonally opposite in
a unit cell and force its four-cycle. Thus two preserved neighbors must be
opposite, and three or four are impossible. Contracting the anchors cannot
increase the incident-edge count. The earlier discussion of degree-three or
degree-four holes was a generic graph allowance in the formula, not a
possibility in this grid, and was misleading in this application.

Consequently S has the concrete contact interpretation

```text
S=a+#{deep holes u : g(u)=2}=m_all.
```

Each degree-two hole gives one two-edge path with that unique interior hole.
Its anchors are distinct, since otherwise there is a forced cycle. At least
one anchor is deep F: two opposite neighbors of a deep vertex cannot both
belong to the annulus when N>=7. Thus these paths and all a direct edges are
legal contacts in the enlarged selection class above. Their interiors and
physical edges are automatically distinct, though endpoints may be shared.
They exhaust that contact class. In particular,

```text
minimum nonnegative selection loss = max(0,2d-S)=max(0,D).
```

When S>2d, select any 2d contacts to obtain L=0, but this discards the signed
connection bonus D<0. A degree-one hole contributes no contact. The rank
inequality (7) also holds with signed L=D if all S contacts are retained;
the exact equality (11) additionally retains eta.

Consequently a signed alternative, not refuted by the example below, is

```text
2D+3BAD <= 3Lambda+beta+2R+2gamma+2eta+C_*.          (12)
```

This is also unproved. Since (11) is exact, (12) asks for a constant bound on
the weighted quantity `6e+3p+3h+c`. That is stronger than a constant bound on
e alone, and it is not evidence that either bound holds.
Its value is that D has a canonical, wholly physical local-star definition
against which an endpoint/turn charging argument can be tested. It avoids the
truncation to nonnegative selection loss in (8). This does not supply the
missing geometric estimate.

## Universal Candidate Refuted

Take any Q>=2, N=3Q+1, n=N+4=3Q+5, and k=Q+1. Use local deep coordinates
(x,y) in {1,...,N}^2, corresponding to physical (x+1,y+1). Preserve precisely

```text
F={(x+1,y+1): 1<=x<=N, y=1,4,...,3Q+1}.
```

There is no preserved annulus vertex. Each full bar has N preserved vertices,
N-1 internal edges, 2N vertical leaf edges, and two horizontal endpoint leaf
edges. Its forced support is a tree on 3N+2 vertices with 3N+1 edges. Bar rows
are three apart, so their three-row support bands are disjoint. Every forced
edge belongs to one of these supports; remaining vertices are isolates.
This proves feasibility directly, for every Q, without a computational
certificate or an assumption about local exclusions being sufficient.

There are Q+1 deep components. The first and last bars each have N-1=3Q bad
edges; all Q-1 remaining bars contribute good edges only. Hence

```text
f=(Q+1)N=3Q^2+4Q+1,
T=3Q^2+13Q+10, e=-9Q-9,
d=Q+1, BAD_H=BAD=6Q, BAD_V=0,
GOOD=3Q(Q-1), Lambda=3Q,
p=h=r_A=E=C_o=C_i=0,
K=4n-4=12Q+16, b=4n=12Q+20,
beta=4, gamma=4, R=0, Omega=6Q+12.
```

Each bar admits two distinct direct outward endpoint contacts, so L=0 is
attainable. But every nonnegative L in (8) satisfies

```text
2L+3BAD >= 18Q,
3Lambda+beta+2R+2gamma+C_* = 9Q+12+C_*.
```

For any proposed absolute C_*, choose Q>(12+C_*)/9. Thus (8) fails even with
the best nonnegative selection loss, and even in the enlarged contact class.
This is a paper counterexample to the universal lemma, not a counterexample
to a constant upper excess: its own excess is strictly negative and linear
in Q. It does not refute (8+) or a maximum-only version.

The canonical signed counts explain the discarded credit. The two horizontal
endpoints of each bar give 2(Q+1) direct annulus edges. The first and last bars
also have N outward vertical edges each. Every deep hole lies in one of the
two rows between consecutive bars and has exactly one preserved neighbor.
Therefore

```text
a=2(Q+1)+2N=8Q+4, #{g=2}=0, z=0,
S=8Q+4, D=2(Q+1)-(8Q+4)=-6Q-2.
```

The disjoint supports occupy (Q+1)(3N+2) vertices. There are
n^2-(Q+1)(3N+2)=16Q+20 remaining isolated vertices, all in the annulus. Thus

```text
c=(Q+1)+(16Q+20)=17Q+21,
c_A=|A|=8n-16=24Q+24,
eta=c-z-1=17Q+20.
```

As a check, both sides of (11) equal -37Q-33. Already the signed version of
the budget without eta has left side `2D+3BAD=6Q-4`, below
`3Lambda+beta+2R+2gamma=9Q+12`. Truncating D to L=0 destroys this credit and
creates the false universal demand. None of these checks proves a signed
budget for other configurations.

## Where Propagation Stops

The proved continuation estimate is

```text
sum_{valid o(y)} |E_y minus E_sigma(y)| <= 3Lambda.
```

It counts column-labelled terminal events, not all affected rows. As a purely
set-theoretic illustration, place one left-column label on M successive rows
of a residue-one chain and then terminate it. The directed difference sum is
one, while M rows carry the label. This is not asserted to be a feasible grid
or a counterexample to (8+) or (12). It demonstrates exactly why a bounded
difference sum cannot justify charging every later affected row separately.

Nor are the continuation budget and the vacancy/run budget independent:
both are bounded by the same sum delta_t. The bad-edge proof above also uses
that sum. Adding three separately valid upper bounds does not produce a
balanced allocation of its units.

A proof of (8+) needs an allocation of the nonnegative loss max(0,D)
to defects on its restricted domain, with the stated weighted balance.
A proof of (12) can instead
work with hole-star surplus, but must show how terminal events, fragmented
runs, and vertical interruptions change that surplus, jointly with the
boundary terms. Degree-one attachments are the precise obstacle: forest
acyclicity allows arbitrarily many of them in one tree. Existence of many
replacement carriers is not a rank credit.

Deleting every defective step and applying zero-loss geometry to the pieces
does not fix this. A cut can expose order-Q carrier ends, while its delta_t
can be constant; the new cut is not the physical annulus. No bound on those
artificial contacts follows from counting the number of defective steps.
Similarly, monotone repairs of row-edge sets may alter a long continuation;
the repaired set has not been shown feasible or to preserve physical rank.

The universal allocation (8) is impossible by the bar family. The remaining
unsuccessful step is the restricted allocation (8+), or a signed-surplus
estimate such as (12). Neither follows from (1), fourth-step propagation,
and the local tiling identity by any argument given here. No counterexample
to these remaining candidates is claimed.

## Outcome

The established positive-loss additions are (1)--(3), the boundary-refined
conditional contact inequality (7), and the unrestricted physical-star
identity (11). They retain actual bad edges and actual annulus components.

The original universal candidate (8) is refuted by a fully specified feasible
family, not left open. The live whole-gap obligations are (8+) or a signed
estimate such as (12), with an absolute constant rather than a coefficient
times Lambda. There is no endpoint/turn-to-defect allocation proving either
here. The zero-loss paper bounds and the unconditional half-coefficient bound
are unchanged. No global T+O(1) result is claimed.
