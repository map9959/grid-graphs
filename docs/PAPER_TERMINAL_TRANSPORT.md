# Terminal Transport On Actual Carriers

Date: 2026-09-08. Independent paper attempt. The global bound
`f <= T+O(1)` for `n=3k+2` is NOT proved.

Independent read-only review covered the entire note (original lines
1--239), with no mathematical findings. The port loads in the countercheck
are assigned loads, not claimed to arise from a geometric seam decomposition.
This is a paper audit, not Lean verification.

Read both current clean notes through their ends, including the
full-height two-root moving-seam theorem. The new result here is a sharp
port-transport lemma and an arbitrary-size feasible obstruction to a
FOREST-ONLY bounded-potential shortcut. It is not a counterexample to
the upper bound, to a low-K-only transport theorem, or to transport of a
properly constructed geometric seam demand.

## What Was Attempted

Retain the actual carrier contact forest, color its nonsingleton vertices
by rail bank, and try to move signed terminal coordinate terms through
that forest. Only actual connected carrier subgraphs may be contracted.
Reserve each original carrier, boundary, and component coupon once;
retain small-bank refunds only in their original allocation.

The hoped-for cancellation was that internal contact-tree vertices conserve
flow, leaving only physical-boundary terms and one bounded residual per
closed tree component. The obstruction below occurs BEFORE any contraction
of a whole bank: even a single actual straight carrier cannot be treated
as a metrically costless flow-conserving vertex.

Contacts at different positions on that carrier have different coordinate
potentials. Forest acyclicity controls paths and rank, but not their
longitudinal congestion. The distinction is necessary even when every
contact edge carries at most one unit and there are only two bank colors.

## Exact Port Lemma

Let C be one actual straight carrier. Give its axis the increasing
coordinate x. Aggregate all signed injections at each distinct port,
and write their positions and amounts as

```text
x_1 < ... < x_p,       alpha_1,...,alpha_p,
sum_i alpha_i = 0,
S_j = sum_(i<=j) alpha_i,       1<=j<p.
```

Positive alpha denotes an injection into C and negative alpha a withdrawal.
Balance is precisely the conservation law at the vertex obtained by
contracting C. Nevertheless,

```text
sum_i alpha_i*x_i
  = -sum_(j=1)^(p-1) S_j*(x_(j+1)-x_j).             (1)
```

Furthermore the minimum total absolute longitudinal transport along C is

```text
L_C = sum_(j=1)^(p-1) |S_j|*(x_(j+1)-x_j).          (2)
```

Here transport cost means amount times distance, with arbitrary splitting
of amounts allowed. This is a statement about transport along the actual
carrier, not about adding paths to H.

Proof of (1). Set S_0=S_p=0 and substitute
`alpha_i=S_i-S_(i-1)`. Collect the coefficient of every S_j. It is
`x_j-x_(j+1)`, which gives (1).

Proof of (2). Cut any open interval `(x_j,x_(j+1))`. Its left side has
net injection S_j, so every transport must move net amount S_j across
the cut. Its absolute amount is at least |S_j|. Integrating these lower
bounds over the disjoint intervals gives the right side of (2).
Conversely put signed flow S_j on that interval, directed toward
increasing x when positive. Its divergence at each port is alpha_i.
This realizes the stated transport with no simultaneous counterflow and
attains the lower bound. QED.

For the coordinate potential `phi=x/A`, the uncontracted terminal term
is the left side of (1) divided by A. It need not vanish when the
contracted carrier has zero net injection. Its absolute value is at most
`L_C/A`, and that bound is attained when all nonzero S_j have one sign.

In particular `|S_j|<=1` suffices to transport through one carrier for
at most one normalized length unit, since its span is at most A. Unit
loads on the individual CONTACT EDGES do not imply this cumulative-load
condition. Nor does a bounded range for phi: that range must be multiplied
by the transported amount, which need not be one.

This identifies the missing term in a carrier-vertex potential telescope.
Assigning a single potential to C makes cancellation algebraically true
only after replacing all physical port potentials by that single value.
The replacement errors sum to exactly (1), independently of the chosen
single value, because `sum alpha_i=0`.

## A Feasible Two-Color Obstruction

For every integer m>=1 put

```text
k=2m, n=6m+2, A=n-1=6m+1,
y_j=2+3j,       0<=j<2m.
```

Use (x,y) vertex coordinates. Preserve exactly

```text
C = {(0,y): 0<=y<=A},
P_j = {(x,y_j): 2<=x<=A-2},       0<=j<2m.
```

Thus C is one complete left boundary spine and the P_j are its teeth.
All other vertices are U.

This is feasible at every size. The forced support of one straight tooth
is a tree. Supports of different teeth are disjoint: their preserved
rows differ by at least three, while their supports extend only one row
on either side. Each tooth support meets the spine support in exactly
the vertex `(1,y_j)`. These meeting vertices are distinct. Gluing the
tooth trees to the spine tree at these single vertices gives one tree;
all vertices outside its support are genuine ambient isolates.

The actual carrier contact forest on carriers is exactly the star

```text
C -- P_j,       0<=j<2m.
```

The contact path is the actual two-edge path through `(1,y_j)`. No bank
has been contracted. The teeth constitute ONE horizontal rail bank:
successive rows differ by three and have identical nonempty FF intervals.
The spine constitutes ONE height-zero vertical bank. Their axial widths
are A-4 and A, respectively, both greater than A/3 even when m=1.

Put a unit source at each of the first m tooth contacts and a unit sink
at each of the last m tooth contacts. Equivalently, at the spine ports set

```text
alpha_j = +1 for 0<=j<m,
alpha_j = -1 for m<=j<2m.
```

Each actual contact edge carries one unit in absolute value, and the
contracted spine vertex is balanced. But its cumulative longitudinal
loads between ports are

```text
1,2,...,m-1,m,m-1,...,2,1.
```

Consecutive ports are three apart. Therefore (1)--(2) give exactly

```text
sum_j alpha_j*y_j = -3m^2,
L_C/A = 3m^2/(6m+1) -> infinity.                    (3)
```

All the cumulative loads are positive, so this is also an unbounded
SIGNED coordinate-potential residual, not merely an overestimate from
taking absolute transport costs. The potential `y/A` has range at most
one on C throughout this example.

Consequently the following proposed implication is false:

> On an actual carrier contact forest with a bounded number of bank
> colors, balanced unit contact loads can be telescoped through each
> carrier with a bounded total coordinate-potential error depending only
> on the number of colors and routed tree components.

There are two colors and one routed tree component here, but (3) is
unbounded. Even one protected original unit for the boundary spine does
not pay its longitudinal transport in this example. The same obstruction
is present if one proposes a bounded residual per routed closed flow
component: the displayed source-sink flow is balanced on its one tree.
This is a statement about closed FLOW, not a claim that this tree avoids
the physical boundary.

## Scope Of The Obstruction

The sources and sinks above are deliberately specified port loads. They
are NOT proved to be terminal demands produced by a decomposition of
actual wide-bank packets. This qualification is essential. A geometric
decomposition might force interlacing signs, provide refunds for their
failure to interlace, or send demands directly to separate boundary
witnesses rather than through this spine. None of those possibilities
is refuted by (3).

The configurations are also far outside the hypothetical regime K<n.
For general k in the same comb construction, direct counts give

```text
r=k+1, f=3k^2+k+2, b=9k+4, c=11k+1,
K=r+b+c=21k+6.
```

For completeness, b counts the holes on the three unpreserved sides,
with corner deficiency counted twice. The nontrivial forced component
is the single comb tree just proved. Its edge count is
`4f-(3k+4)-(f-r)=3f-2k-3`: the preserved boundary vertices have total
degree deficiency n+2=3k+4, and `f-r` counts the FF edges counted twice
in the degree sum. Thus `c=n^2-(3f-2k-3)=11k+1`, as displayed.

These many genuine isolates can provide global payment in other
arguments. They were not erased or replaced by deletion components.
The example disproves only the implication from colored forest structure
and vertex conservation to bounded transport cost. It does not disprove
payment from all available original resources.

## Failure Of This Attempt

The exact port calculation is the new deduction. It prevents silently
discarding metric terms even in a legal contraction of a CONNECTED
carrier, a different issue from the already forbidden contraction of a
whole bank.

I did not obtain a decomposition assigning actual packet terminal
demands to the contact forest with controlled cumulative port loads.
In particular, neither forest rank nor the at-most-thirteen-wide-bank
bound supplies the needed control: the counterexample proves their
insufficiency for unrestricted unit contact loads, while leaving open
the essential extra constraints on genuine seam loads.

Closed ambient components still have only their original c coupons.
Small-bank refunds still have only their original fractional value.
Routing through the carrier or component owning such a coupon does not
reissue it at every port or every traversal. No injection from the
uncontrolled longitudinal cost (2) to those once-owned resources was
proved. The full-height boundary theorem avoids this problem by proving
and paying its two terminal widths directly; it cannot be transported
to internal terminals merely by vertex conservation.

Thus no new universal K>=n-O(1), no partial-seam terminal payment, and no
global f<=T+O(1) follow from this pass. The rigorous failure is specifically
the unproved geometric congestion control and the demonstrated falsity
of its forest-only replacement, not a purported contradiction to the
target theorem.

Verification: the port lemma and comb feasibility proof hold for all m.
Direct in-memory checks on n=8 and n=14 verified forced-forest feasibility,
the displayed counts, the original ledger, and both identities in (3).
No optimization or Lean ran. Only this document was written; all existing
worktree changes were left untouched.
