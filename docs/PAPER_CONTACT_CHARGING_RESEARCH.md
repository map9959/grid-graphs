# Paper Contact Charging Research

Date: 2026-09-08. Paper research only; no Lean, optimization, or grid search.
Independent read-only review found no mathematical errors. **The global upper
bound `P(3k+2)<=T+O(1)` is not proved here.**

## Scope And Target

Read together with [Positive Loss](PAPER_POSITIVE_LOSS_UPPER.md),
[Zero Loss](PAPER_ZERO_LOSS_UPPER.md), and
[Packing Stability](PAPER_PACKING_STABILITY.md). All carriers and contacts
below are actual, and all component counts include the isolates specified
in those notes. Keep their fixed orientation and notation:

```text
n=3k+2, k>=3, Q=k-1, N=3Q+1, T=3k^2+7k,
e=f-T, r=p+h+d, sum_t delta_t=3Lambda,
beta=b-K, R=r_A-p-h, gamma=4-C_o+C_i.
```

Contract the actual deep preserved components and the components of the
actual forced annulus. Write `a` for direct deep-component/annulus edges,
and `g(u)` for the degree of a deep hole in this contracted forest. The
local cell obstruction gives `g(u)<=2`. Put

```text
S=a+#{deep holes with g=2}, D=2d-S,
z=#{deep holes with g=0}, eta=c-z-1.
```

Each degree-two hole supplies its unique physical contact. Together with
the direct edges these exhaust the contact class in the positive-loss note.
In particular there is no selection problem left when using signed `D`.
Use all the contacts, even when `S>2d`.

The exact ledger is

```text
6e+3p+3h+c
  =23+2D+3BAD-3Lambda-beta-2R-2gamma-2eta.             (1)
```

The appropriate weaker target, retaining the requested component credits,
is the existence of an absolute constant `C` such that

```text
2D+3BAD <= 3Lambda+beta+2R+2gamma+2eta
                        +3p+3h+c+C.                (2)
```

By (1), (2) is **equivalent** to `6e<=23+C`, not merely sufficient.
Thus it would give `P(3k+2)<=T+floor((23+C)/6)` in this range. Unlike
candidate (12) in the positive-loss note, it does not additionally demand
a constant bound on `3p+3h+c+6e`. The additive constant here is not asserted
to be zero, and (2) is not asserted to be proved.

The nonnegative-loss candidate (8) remains refuted. Nothing here truncates
`D`, promotes a UU mirror edge to a physical edge, or spends `Omega` as
an independent second copy of the bad-edge reserve.

## An Exact Endpoint Count

There is a physical endpoint representation of `D` valid without a phase
classification. Give each nontrivial deep carrier its two outward axial
ports. Give each singleton either its two horizontal or its two vertical
ports, choosing one pair once and for all. A port is a direction based at
the corresponding endpoint vertex; the two singleton ports are distinct.
There are exactly `2d` ports.

A port is served if its outgoing ray begins one of the canonical contacts:

- An immediate step out of the deep square is a direct annulus contact.
- Otherwise its first vertex is a deep hole. It is served precisely when
  that hole has a second preserved neighbor opposite the port's base.
  That second neighbor can be deep or in the annulus.

The first interior neighbor cannot be deep preserved, since the base is
an endpoint of an actual deep carrier. The cell obstruction rules out a
perpendicular second preserved neighbor at a hole. Thus these criteria
neither omit an axial contact nor introduce a nonphysical one. In
particular, an annulus hole two steps away does not serve a port: the
second edge would be UU.

Let

```text
M = number of unserved ports;
J = number of canonical contacts serving two ports;
U_0 = number of canonical contacts serving no port.
```

Here `J` counts duplication, not an extra contact; it is renamed to avoid
collision with the existing boundary occupancy `B`. A contact serves at
most two ports, one at each of its deep preserved endpoints. A direct
annulus edge serves at most one. Two ports on the same deep component
cannot meet through one hole, since that would be a forced cycle.

If `S_i` counts contacts serving exactly `i` ports, then

```text
2d=M+S_1+2S_2, S=S_0+S_1+S_2,
J=S_2, U_0=S_0,
D=M+J-U_0.                                         (3)
```

This is an exact signed endpoint count. It automatically subtracts contacts
not seen by axial endpoint rules, and corrects the double use of an
end-to-end contact. It needs no global separation of gap columns or nested
axis sets. Changing singleton orientations changes the three counts but
not their combination in (3).

Consequently the exact unpaid geometric obligation is

```text
2M+2J+3BAD <= 2U_0+sum_t delta_t+beta+2R+2gamma
                            +2eta+3p+3h+c+C.       (4)
```

This is equivalent to (2) for every port choice. Optimizing the singleton
choices alone cannot improve the total signed demand. It could only make
an eventual charging construction easier to describe.

Two tempting simplifications are invalid. Counting only missing ports
drops the positive duplication term `J`. Counting only served ports and
then truncating the surplus drops `U_0`. The zero-loss construction avoids
duplication by a geometric choice of ports and contacts; its separation
argument is not available merely from positive-loss packing.

## Continuations Really Telescope

There is an exact interval count behind the fourth-step inequality. For
each edge-left-column label `x`, split its occurrences in each residue
class of good rows into maximal chains of consecutive occurrences three
rows apart. Orient residue-two chains upward and residue-zero and
residue-one chains downward, as in the omitted-step map. These chains
are combinatorial intervals, not paths in the grid.

Let `I_H` be their total number, counting column labels separately, and put

```text
L_H=sum_{valid o(y)} |E_y minus E_sigma(y)|.
```

Each interval has exactly one terminal occurrence in its directed order.
Its terminal is either counted in `L_H`, or reaches an end at which the
omitted step is invalid. The latter possibilities are precisely row `2`
in residue two and row `N-1` in residue zero. The residue-one chain ends
with the valid comparison into the empty row `N`, so has no free terminal.
It follows that

```text
I_H=L_H+|E_2|+|E_(N-1)|,
I_H<=3Lambda+|E_2|+|E_(N-1)|.                       (5)
```

An interval persisting for any number of bands is counted once, not once
per row. Equivalently, on a directed chain with successive sets
`X_1,...,X_m`,

```text
sum_i |X_(i+1) minus X_i| - sum_i |X_i minus X_(i+1)|
   = |X_m|-|X_1|.                                  (6)
```

Equations (5)--(6) are legitimate telescoping potentials for the labelled
edge sets. The boundary term in (5) can be order `Q`; it is not an absolute
constant and has not been paid by the annulus credits in (4).

More importantly, a labelled interval is not a contact or a carrier.
There is a feasible saturated example making this distinction physical.
In local deep coordinates `1<=x,y<=N`, preserve only

```text
{(x,y): 1<=x<=N, y=2,5,...,3Q-1},
```

and preserve nothing in the annulus. Each of the `Q` full bars has a tree
support consisting of the bar, its vertical leaves, and its two outward
horizontal endpoint leaves. Their three-row support bands are disjoint,
so this is a forced forest for every `Q>=2`.

Every one of the `3Q` edge-column labels persists through all `Q` upper
bands. Nevertheless different bars lie in different forced components:
between successive bars the middle edge on a same-column route joins two
holes and is unforced. The exact counts are

```text
GOOD=3Q^2, BAD=Lambda=0,
I_H=|E_2|=3Q, L_H=0,
d=Q, S=2Q, D=0.
```

The two endpoint contacts of each bar, not the continuation labels, pay
for its component contribution. This is not a counterexample to (4).
It proves that identifying a persistent labelled interval with a connected
physical object is invalid even at zero loss. A usable potential must
allow repeated births of distinct bars while balancing their actual
contacts, rather than declaring that a constant phase has no events.

## A Local Physical Audit

The following exact deletion calculation tests the coefficients and the
role of `eta`. It is not a repair theorem or an upper-bound argument.

Delete one preserved vertex `v` strictly inside the deep square, so all
four neighbors are deep. Let `q` be its number of preserved neighbors.
The straight-carrier property gives `q in {0,1,2}`, with opposite neighbors
when `q=2`. All `q` lost FF edges are good. Among its `4-q` hole neighbors,
let `t` have degree two before the deletion; the others have degree one.

Deletion preserves feasibility. The `q` edges to preserved neighbors stay
forced. Exactly `4-q` edges to holes disappear, so the full forest component
count increases by `4-q`. The new hole at `v` has degree `q`; its former
hole neighbors each lose one incident edge. Direct counting gives

```text
Delta f=-1, Delta d=q-1, Delta Lambda=q, Delta BAD=0,
Delta c=4-q,
Delta z=4-q-t+1_{q=0},
Delta eta=t-1_{q=0},
Delta S=max(q-1,0)-t,
Delta D=2(q-1)-max(q-1,0)+t,
Delta(D-eta)=q-1.                                  (7)
```

The annulus, `p`, and `h` are unchanged. For the latter assertion, a split
carrier has two surviving deep pieces, while deleting a deep singleton
strictly inside the deep square cannot leave an annulus piece of that
carrier. Thus `beta,R,gamma` are unchanged too.

Define the retained-credit signed demand

```text
W=2D+3BAD-3Lambda-beta-2R-2gamma-2eta-3p-3h-c.
```

The physical changes in (7) give, without any inequality,

```text
Delta W=2(q-1)-3q-(4-q)=-6.                         (8)
```

This agrees with `W=6e-23` from (1). In particular when `q=2`, splitting
a rod creates one new contact but can destroy `t` transverse contacts.
The apparent additional deficit in `D` is exactly canceled by the increase
of `eta`. A purported local rule that charges all destroyed contacts to
packing loss while dropping `eta` misses this compensation.

This audit is also a warning: reversing (8) is useful only when the added
vertex is feasible. Filling holes can create forced cycles. No argument
here transforms an arbitrary configuration to zero loss by feasible
insertions or otherwise pays for the insertions needed. Deleting down to
the empty configuration just reproduces the mass identity.

## Why The Discharging Attempt Stops

The endpoint formulation (4) is global and physical, and the continuation
count (5) handles persistence without a per-row charge. They do not yet
combine into a proof. The missing assertion is a **joint weighted
allocation** of the left side of (4) to its displayed right side, with
absolute residual cost. In particular:

- A terminal edge-column label need not be an unserved carrier port, and
  an unserved port need not be a terminal label. Vertical interruptions
  and deep singletons also have to enter the allocation.
- A contact serving two ports is still just one forest edge after
  suppression. Its duplication debit must be paid, not counted twice as
  a merger. Contacts serving no ports are real negative demand.
- The bound `L_H<=sum delta_t`, the vacancy/run identity, and
  `2BAD_H+3BAD_V<=2 sum delta_t` spend the same step resources.
  They do not give three independent purses. For example `BAD<=3Lambda`
  alone allows `3BAD-3Lambda` as large as `6Lambda`.
- A cut across a persistent phase may expose order-`Q` ports. These are
  neither physical annulus contacts nor a constant-size boundary term.
  Any cut potential must retain their signed credit until genuine closure.
- Rank tracks physical joins, but a new one-ended attachment can remain
  in an existing tree indefinitely. A frontier connectivity count alone
  does not charge that attachment to a vacancy or to a final component.

The rank part cannot supply the missing inequality by itself: its exact
identity is

```text
D-eta=d+1-c_A.
```

Thus telescoping rank without a geometric estimate simply replaces the
contact demand by the deep-component count and the annulus ledger. It
returns (1), not a sign bound. Equations (3), (5), and (7) isolate genuine
endpoint, continuation, and surgery cancellations, but no bounded-range
potential coupling all three has been established.

There is a useful rigorous range reduction. The existing global identity
and `K>=5,c>=1` imply

```text
4e<=2Q+7-Lambda.
```

Consequently `Lambda>=2Q` already gives `e<=1`. The reviewed zero-loss
paper handles `Lambda=0`. For a global constant upper excess it therefore
suffices to settle the positive-loss range `1<=Lambda<2Q`; one may also
restrict to `e>0`, using `p>=4` when `k>=5`. None of these restrictions
supplies the missing allocation in (4), and a bound proportional to
`Lambda` would still leave an unbounded gap in this range.

## Result

Established here, at independently reviewed paper level: the exact axial-port identity
`D=M+J-U_0`, the exact labelled-interval telescoping formula (5), the
feasible persistent-bar audit, and the local deletion changes (7). They
retain signed surplus, actual contacts, `eta`, and `3p+3h+c` throughout.

**Remaining gap:** prove (4), or a genuinely weaker sufficient estimate
on the positive-excess range, by a joint geometric allocation with a
constant residual. No such allocation, endpoint bound, or globally bounded
telescoping potential is proved here. No counterexample to (2) or (4) is
claimed. Candidate (12) is not used as a stronger substitute for the
requested target. Only this research note was created; no existing file
was edited and no optimization of any size was run.
