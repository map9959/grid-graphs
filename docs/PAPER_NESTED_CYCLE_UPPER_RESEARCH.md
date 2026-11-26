# Nested Cycle Upper Research

Date: 2026-09-08. Independent paper investigation, with explicit-example
checks on sides at most 14. No Lean changes or verification. No unrestricted
constant-gap upper bound is proved.

## Result

The proposed local nested-cycle route has two precise obstructions:

1. Assigning two distinct credits to each nested square cycle, with carriers
   and forced components required to meet the cycle and boundary credits
   kept at the outer cycle, fails even for feasible, isolate-free,
   inclusion-maximal parallel-rod sets. Maximum matchings on sides 8, 11,
   and 14 leave respectively 1, 1, and 3 slots unpaid.
2. Allowing arbitrary carrier/component assignments does not repair locality:
   any such two-credit assignment for this family must move boundary credits
   to depth at least `n/6-O(1)`, with total depth `n^2/36-O(n)`.
   These conclusions still hold if a fixed number of slots are exempted.

A separate explicit family refutes constant-error monotonicity of
`r+b+c` under peeling one square boundary. The decrease can be `12-4n`,
not a bounded negative exception.

These are counterexamples to specified proof lemmas, NOT to the desired
upper bound. Both families have ample global reserve. In particular they
do not rule out a charging theorem restricted to hypothetical low-reserve
counterexamples. The useful output is a quantitative nonlocality requirement,
not a claim that nested cycles cannot work.

## Model

Let `Q=[0,n-1]^2`, let `F` be preserved, and let `H` contain every grid edge
with at least one endpoint in `F`. Feasibility means that `H` is a forest.
Use the actual counts from [Half Coefficient](PAPER_HALF_COEFFICIENT_UPPER.md):

```text
r = number of components of the induced graph on F,
c = number of components of H, including isolated holes,
b = sum_(u outside F) (4-deg_Q(u)),
S = r+b+c,
3|F|+S = n^2+4n.
```

Thus `S>=n-C` implies `|F|<=n^2/3+n+C/3`. On a `w` by `h` rectangle the
same edge count gives `3|F|+S=wh+2w+2h`. Failure of a proposed lemma on
squares also defeats its unrestricted rectangular version.

Carriers are straight filled intervals. A hole has at most two preserved
neighbors, opposite when there are two. The proof below retains long rods,
actual components, and all boundary weights; it does not normalize roots
or promote UU edges to forced connections.

The [Dual](PAPER_DUAL_UPPER_RESEARCH.md) and
[Projection](PAPER_PROJECTION_UPPER_RESEARCH.md) notes already explain why
ordinary complement connectivity and component bounding boxes are
insufficient. The new tests here concern nested-cycle resource matching
and the metric cost of transporting boundary credits.

## Cycles And Credit Matching

Put `K=floor(n/2)`. For `0<=j<K`, let `C_j` be the perimeter cycle of
`[j,n-1-j]^2`. Its side is at least two, so even the last cycle is a literal
grid cycle. The cycles are vertex-disjoint. There are `2K=n-O(1)` slots
if each cycle is to receive two credits.

Every `C_j` contains a UU edge: otherwise its entire cycle belongs to `H`.
This guarantees distinct physical missing edges on different cycles, but
does not make their associated carrier or component labels distinct.

Here is a precise, generous local credit lemma to test, denoted **LC**:

```text
Tokens: one per actual carrier, one per actual H component,
        and b boundary tokens (two for a corner hole).
Demand: two distinct tokens at every C_j; no token is reused.
Eligibility:
  a carrier token can serve C_j if the carrier meets C_j;
  a component token can serve C_j if the component meets C_j;
  a boundary token can serve C_0 only.
Claim LC: every feasible set admits such an assignment.
```

LC is already more permissive than charging only labels immediately beside
a chosen UU witness: any intersection with the cycle suffices. In the
outer cycle all boundary tokens are allowed without requiring proximity
to the chosen witness. LC would prove `S>=2K`, but is false.

For a set `J` of cycle indices, a necessary condition is the Hall inequality

```text
number of tokens eligible for at least one C_j, j in J >= 2|J|.       (1)
```

This counts a rod crossing many cycles just once. Indeed the full set of
Hall inequalities is sufficient too: duplicate each cycle into two slots
and apply ordinary bipartite matching. Thus (1), unlike a count of UU
edges or of rod-cycle incidences, directly tests nonreuse.

## An Isolate-Free Hall Obstruction

Take `n=3s+2`, `s>=1`, and preserve exactly the complete rows

```text
y=0,3,6,...,3s.
```

Each row forces a tree consisting of its horizontal spine and the adjacent
rows of pendant holes. The corresponding row bands are disjoint and
partition the board: the first band is rows 0 and 1, and the subsequent
bands are `[3a-1,3a+1]`, `1<=a<=s`. Edges between bands are UU. Therefore
the forest and carrier counts, without any appeal to an upper bound, are

```text
f = n(s+1),   r = c = s+1,   isolated holes = 0,
b = 7s+4,    S = 3n.                                            (2)
```

For `b`, the preserved vertices have total deficiency `n+2(s+1)`:
the top row contributes its side deficiency and each rod contributes its
two end deficiencies. Subtract from total deficiency `4n`.

These sets are also inclusion-maximal. Every hole has a horizontal hole
neighbor in its own rod tree, even at the left or right board edge. Making
the hole preserved adds that missing edge to an already connected pair,
creating a cycle. Thus maximality alone cannot exclude the example.

Apply (1) to ALL interior cycles `J={1,...,K-1}`. Exactly `s` carrier
tokens are eligible: the top rod never enters the inner square, while
every other rod meets `C_1`. All `s+1` component tokens are eligible,
including the top tree through its row-1 leaves. No boundary token is
eligible. Hence

```text
eligible tokens = 2s+1,
required tokens = 2K-2,
Hall shortage   = 2K-2s-3.                                     (3)
```

For even `s` this shortage is `s-1`; for odd `s` it is `s-2`. It grows
as `n/3-O(1)`. In particular no fixed number of exceptional cycles repairs
LC for arbitrary `n`. This is an existential-assignment obstruction, not
just an unfortunate choice that keeps selecting the same UU witness.

The observed finite maximum matchings below attain exactly the bound from
(3). No arbitrary-size equality formula for the maximum matching is needed
or claimed; the Hall upper bound alone refutes LC.

## Boundary Transport Is Macroscopic

Now relax LC much further: allow every one of the `r+c=2s+2` nonboundary
tokens to serve ANY cycle, whether or not it meets that cycle. Permit
boundary tokens to move inward. The following obstruction therefore does
not depend on the precise witness-adjacency convention for rods.

At least

```text
D = 2K-2s-2                                                   (4)
```

of the `2K` slots must receive boundary tokens. Regard assigning a boundary
token to `C_j` as incurring depth `j`. Every physical grid path from the
outer boundary to `C_j` has at least `j` edges. A boundary hole of weight
two gives two tokens, not an unlimited supply.

There are only two slots at each depth. To minimize total depth of `D`
boundary assignments, fill depths `0,0,1,1,2,2,...` in that order. Therefore

```text
maximum assigned boundary depth >= ceil(D/2)-1   (when D>0),
sum of assigned boundary depths >= floor((D-1)^2/4).             (5)
```

For `D=2q`, the sum is `q(q-1)`; for `D=2q+1`, it is `q^2`.
Since `D=s` when `s` is even and `D=s-1` when `s` is odd, (5) gives
the `n/6-O(1)` depth and `n^2/36-O(n)` total-depth bounds stated above.
Allowing a fixed number `E` of unpaid slots replaces `D` by
`max(0,2K-E-2s-2)` and leaves both asymptotic conclusions unchanged.

Equivalently, if boundary credits may reach depth at most `R`, then even
this relaxed scheme necessarily satisfies

```text
2K <= 2s+2 + 2(R+1) + E.                                      (6)
```

No fixed `R,E` works for the family. A bounded-width annular rule cannot
assign all ring credits directly to nearby global resources.

This does NOT say transport must consume fresh resources at each step.
It says exactly why that additional assertion would be untenable: `S=O(n)`
in (2), whereas the sum of the required travel distances is `Omega(n^2)`.
Long corridors must be allowed to carry credit without unit cost per unit
length, or a proof must avoid this assignment scheme or exclude this
high-reserve family first. A different routing model sharing edges is not
bounded below by the sum in (5); (5) counts token travel, not a union of
physical routing edges.

## Peeling Does Not Supply Fresh Credits

Another possible implementation would telescope the actual restricted
ledgers. Let `S_j` be `r_j+b_j+c_j` computed afresh on the square
`Q_j=[j,n-1-j]^2`, with `F_j=F intersect Q_j`. In particular `c_j` counts
all components of `H(F_j)` on `Q_j`, not just restrictions of ambient
component labels. Restricted feasibility holds because this graph is
exactly the induced subgraph `H[Q_j]`.

If the outer square has side `L` and `a_j=|F intersect C_j|`, subtracting
the two exact ledgers gives

```text
S_j-S_(j+1) = 4L+4-3a_j.                                     (7)
```

Equation (7) by itself supplies no positive per-ring increment. The
candidate `S_j>=S_(j+1)+2-C`, for an absolute `C`, is false even for `j=0`.

For an explicit counterexample take `n=3s+1`, `s>=1`, and again preserve
full rows `0,3,...,3s`, now including both top and bottom. Their disjoint
tree bands cover the square. For the ambient and the once-peeled squares:

```text
Ambient side n:
  r=c=s+1, b=4s, S_0=2n, no isolated holes.

Inner side m=n-2=3s-1:
  r_1=s-1,
  c_1=s-1+2m,
  b_1=4m-2(s-1),
  S_1=6m.

S_0-S_1 = 12-4n.                                             (8)
```

To verify the inner components, the remaining rods are the `s-1` rows
strictly between the deleted outer rods. Their bands leave the first and
last inner rows uncovered. Every vertex of these two rows becomes an
isolated hole: `2m` isolates. In the ambient graph they were pendant leaves
of the two deleted rods. This is precisely the source of the large change
in component accounting. For `s=1` there are no remaining rods and the
inner 2 by 2 square consists of four isolates; the same formulas hold.

The removed boundary contains `a_0=8s` preserved vertices, also checking
(8) directly in (7). Thus straightness does make the number of surviving
carriers nonincreasing under convex trimming, but it does not make the
combined credit `S_j` nonincreasing. Interior artificial boundary weights
and newly exposed isolates cannot be counted as fresh ambient credits.

## Bounded Checks

An in-memory `python3 -B -c` command constructed only the displayed
families. It enumerated all physical grid edges, inserted forced edges
into union-find while asserting that none closes a cycle, and separately
computed induced-F components, boundary deficiency, and ambient isolates.
Every case checked the exact global ledger. No script or data file was
written. The initial `python` invocation was unavailable; the checks below
were completed with `python3`.

For the `3s+2` family it also built every literal ring, checked a UU edge
on each ring, duplicated each ring into two matching slots, and computed
a maximum bipartite matching by augmenting paths with LC's eligibility:

```text
n    f   r   b   c   isolates   slots   matched   shortage
8   24   3  18   3      0         8       7         1
11  44   4  25   4      0        10       9         1
14  70   5  32   5      0        14      11         3
```

For the `3s+1` peeling family, separate forced-graph checks on the inner
square gave:

```text
n   outer (f,r,b,c)   inner (f,r,b,c)   inner isolates   S_0-S_1
7      (21,3,8,3)       (5,1,18,11)         10            -16
10    (40,4,12,4)      (16,2,28,18)         16            -28
13    (65,5,16,5)      (33,3,38,25)         22            -40
```

All assertions passed. These are explicit-example and matching checks,
not cardinality optimization, exhaustive feasibility enumeration, or a
substitute for the arbitrary-size proofs. No board above side 14 was
instantiated. The growing-family statements are symbolic.

## Remaining Scope

The square-cycle fact gives about `n/2` nonreused missing EDGES, but does
not automatically give twice as many nonreused global CREDITS. LC fails
by a linear Hall deficiency. Even assigning all carrier and component
tokens without geometric restrictions leaves a macroscopic boundary
transport requirement. Peeling instead of matching does not evade the
issue: it manufactures linearly many components from a single deleted rod.

A viable continuation could restrict to `S<n-C`, handle the already-safe
high-`S` families separately, and prove a nonlocal credit-routing theorem
in that restricted class. Alternatively it could telescope an interface
potential recording how many exposed holes still belong to the same
ambient rod tree. Such a potential cannot have universally bounded
magnitude: the discrepancy (8) is linear in the side length. Its initial
and terminal costs would need genuine control.

Neither construction here has low `S`, so neither countertests those
restricted proposals. No diagonal-sweep or min-link theorem is asserted,
and no improvement to the existing unconditional half-coefficient upper
bound follows. The completed result of this attempt is the refutation of
LC and bounded-locality variants, the quantitative transport lower bound,
and the explicit failure of bounded-error ledger peeling.
