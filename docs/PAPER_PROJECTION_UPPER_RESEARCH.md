# Projection Upper Research

Date: 2026-09-08. Paper deductions only; no Lean changes or verification.
Independent read-only review found no mathematical errors and separately
recomputed the explicit parallel-rod and two-comb examples.

## Outcome

The unrestricted bound `P(3k+2)<=3k^2+7k+C` is **not proved here**.
This note gives an exact carrier-contact reduction, an exact projection
accounting, explicit counterexamples to disjoint-component-box accounting,
and an exact maximum-specific insertion/exchange test. It also proves the
stronger weighted estimate `r+b+c>=3n` for full parallel-rod configurations.
None of the counterexamples refutes the desired unrestricted bound.

Inputs read were the [half-coefficient upper](PAPER_HALF_COEFFICIENT_UPPER.md)
and [fault-line analysis](PAPER_FAULT_LINE_ANALYSIS.md), with the zero-loss
and moving-phase cap notes consulted for context. In particular, the
variable-rail five-column certificate does not apply to arbitrary mixed
tilings, and bounded packing loss does not imply one fixed global phase.
No optimization, exhaustive enumeration, or build was run in this
investigation. The explicit parallel-rod and two-comb constructions were
checked on sides 8, 11, and 14 as recorded below. All arbitrary-size
examples below are symbolic constructions, not searches on larger boards.

## Ledger And Objective

Use coordinates `[0,n-1]^2`, with `n=3k+2`, and put `T=3k^2+7k`.
The forced graph `H` contains every grid edge incident to the preserved
set `F`; feasibility means that `H` is a forest. Write `f=|F|`, `r` for
the number of induced F components (carriers), `c` for all components of
`H`, including isolates, and

```text
b = sum_(u outside F) (4-deg_grid(u)),
S = r+b+c.
```

The exact ledger from the half-coefficient note is

```text
3f+S = n^2+4n,
S = n+10-3(f-T).                                    (1)
```

Thus `S>=n-D` gives `f<=T+floor((D+10)/3)`. Conversely,
`f<=T+C` gives `S>=n+10-3C`. Proving this for a maximum is enough:
by (1), maximum cardinality is exactly minimum S over all feasible sets.
This is an equivalence of optimization problems, not an independent
source of a lower bound on S.

## Exact Contact Reduction

Every carrier is a straight filled interval, including possible singletons.
Every hole has at most two F neighbors, and two such neighbors are opposite.
Indeed, two perpendicular F neighbors are diagonal corners of a unit
square, all four of whose edges are forced. Three neighbors contain such
a pair.

Let `u_i` count holes with exactly `i` F neighbors, for `i=0,1,2`.
Contract every carrier, discard the `u_1` pendant holes, and suppress each
degree-two hole to one edge. Discard the `u_0` isolates separately. The
result is a forest J whose vertices are the r actual carriers and whose
edges are the `u_2` physical contacts. A suppressed edge joins distinct
carriers: the two opposite F neighbors cannot lie in the same filled
interval across a hole. Parallel contact edges are impossible, since
they would lift to a cycle in H. Contraction and suppression preserve
acyclicity.

With `m=u_2`, `z=u_0`, and t the number of components of J, including
isolated carrier vertices, this proves

```text
m = r-t,
c = t+z,
S = 2r-m+z+b.                                      (2)
```

For `F=empty`, take `r=m=t=0` and `z=n^2`; the formulas still hold.
The desired geometric statement can therefore be written exactly as

```text
2r - m + z + b >= n-O(1).                           (3)
```

This distinguishes resources a projection argument must not conflate.
A physical contact REDUCES the weighted count by one when r, z, b are
held fixed. A contact is not a new component available to pay for a line.
The elementary forest estimate `m<=r-t` is already equality here; using
it again cannot supply an additional reserve. Long rods and mixed
orientations are retained without normalization.

## Full Parallel Rods

Here is one completely closed subclass illustrating the compensation
missing from an `r>=n` claim. Suppose F consists of a full-height vertical
rod on every column of a set A and no other vertices. Let `a=|A|`, and
let q be the number of selected boundary columns (zero, one, or two).

For `n>=2`, distinct selected columns must be at least three apart.
Distance one gives a unit-square cycle; distance two gives the six-cycle
around a width-two, height-one rectangle. Conversely, separation at least
three suffices: the closed neighborhoods of the rods are disjoint, and
each rod forces a path with pendant neighbors.

Their covered column sets have total size `3a-q`. Every remaining vertex
is an isolated hole. Boundary deficiency on F is `2a+nq`: each rod has
its two end deficiencies, and each boundary rod has an additional n side
deficiencies. The exact counts are therefore

```text
f = na,   r = a,
z = n(n-3a+q),   c = a+z,
b = 4n-2a-nq,
S = n(n+4-3a).
```

Spacing gives `a<=ceil(n/3)=k+1`. Consequently

```text
S >= 3n,
f <= n(k+1) = T-2k+2.                              (4)
```

The selection `A={0,3,...,3k}` attains equality: `r=c=k+1`,
`z=0`, and `b=7k+4`. Thus r really is only about `n/3`, even with
complete neighborhood coverage and no ambient isolates. Rotating proves
the same result for full-width horizontal rods. Equation (4) is not a
bound for interrupted rods, arbitrary singletons, or mixed tilings.

## What Span Counting Actually Gives

For a component C of H, use edge-length spans

```text
w_C = max_C x-min_C x,   h_C = max_C y-min_C y.
```

Let `e_x(C),e_y(C)` count its horizontal and vertical edges. Connectivity
implies `e_x(C)>=w_C` and `e_y(C)>=h_C`: every integer cut strictly
between the appropriate extrema must be crossed. More precisely, if
`q_C(i)` counts horizontal edges of C crossing `x=i+1/2`, then

```text
e_x(C)-w_C = sum_(min_C x <= i < max_C x) (q_C(i)-1).
```

There is the analogous vertical formula. Hence, defining the nonnegative
integer `eta_C=e_x(C)+e_y(C)-w_C-h_C`, the exact global identity is

```text
sum_C (w_C+h_C) = n^2-c-sum_C eta_C.                (5)
```

This counts repeated physical cut crossings, not carriers. It has the
wrong direction for converting large spans to many components unless
one also controls those repeated crossings. It is just tree edge
accounting with its projection slack exposed.

Even one straight interior carrier makes that slack large. Take
`F={(x_0,y):a<=y<=a+L-1}` with its entire closed neighborhood interior.
Its nontrivial component has `3L+2` vertices, `3L+1` edges, spans
`w=2`, `h=L+1`, and

```text
eta = 2L-2.
```

That component contains one carrier and meets no boundary hole, while
its span and projection slack are unbounded. Therefore no componentwise
inequality `w_C+h_C<=A(r_C+1+b_C)` with fixed A can hold when `b_C`
counts only boundary holes in C. The many OTHER components and boundary
holes of this example are precisely why this does not refute (3).
Any successful use of spans must allow genuinely global compensation.

### Two Overlapping Boxes

Bounding boxes of distinct actual tree components cannot be used as a
disjoint physical decomposition, even approximately up to O(n) area.
Here is an explicit mixed-orientation example for every `n=3k+2>=8`.
Preserve two full vertical spines at columns 0 and `n-1`. At rows
`y=3j`, for `0<=j<=k`, add a horizontal bar as follows:

```text
j even:  x=2,...,n-4  (attach to the left spine),
j odd:   x=3,...,n-3  (attach to the right spine).
```

All other vertices are holes. Each bar has distance two from its own
spine and distance three from the other. Its closed neighborhood meets
its own spine neighborhood in exactly one vertex, the intervening hole
at that bar's row. Different bars have vertical distance at least three,
so their closed neighborhoods are disjoint. The two spine neighborhoods
are disjoint. Each rod neighborhood forces a tree; attaching every bar
tree at its single shared vertex therefore gives exactly two nontrivial
tree components and possibly isolated holes, with no other forced edges.
This proves feasibility, including at the top and bottom of the board.

Both parities occur. The left component has bounding box
`[0,n-3] x [0,n-1]`, and the right component has bounding box
`[2,n-1] x [0,n-1]`. Their intersection has

```text
(n-4)n vertices.
```

Their actual vertex sets are disjoint. In particular, disjointness of
components or acyclicity of the carrier-contact graph does not imply
disjointness of their boxes or of their projected line sets. Both
components project onto all n rows. Charging each projected row to a
distinct global line resource loses multiplicity on every row here.

For scale, this example has `r=k+3` and
`f=2n+(k+1)(n-5)=3k^2+6k+1=T-k+1`, so by (1)
`S=6k+9`. It violates no proposed constant upper bound. Its role is to
refute box disjointness and nearly disjoint box-area bookkeeping, not
every possible inequality involving boxes.

## Maximum-Specific Exchanges

### Exact Single Insertion Test

Fix a feasible F and a hole u. Let W be the set of grid neighbors of u
which are also holes. Promoting u to F adds exactly the edges `uv` for
`v in W`; its edges to F neighbors already belong to H.

Write `[v]` for the actual component of v in H. The promotion is feasible
if and only if

```text
[v] != [u] for every v in W,
[v] != [w] for all distinct v,w in W.               (6)
```

Proof: contract the existing trees. New edges form a star with center
`[u]`. A leaf in `[u]` closes an existing path; two leaves in the same
other component close a cycle through that tree and u. If neither
occurs, the star joins distinct trees and is acyclic. Empty W causes
no difficulty.

Thus inclusion maximality gives a precise witness for every hole: either
one hole neighbor lies in its own component, or two hole neighbors share
another component. Maximum cardinality implies this property, but is
stronger than it. The witness is about actual connectivity, not merely
distances, spans, or nominal carrier labels.

This criterion alone does not make the witnesses countable at unit cost.
For example, in the equality family of (4), every hole is beside a full
rod. It has a vertical hole neighbor in the same rod tree, including at
the board's top and bottom (use the inward vertical neighbor there).
So every hole is blocked by the first witness in (6); these configurations
are inclusion-maximal. A single long rod supplies such witnesses at
linearly many positions. No distinct-component or distinct-carrier
injection follows from maximality.

### Exact Replacement Test

For a deletion set `D subset F`, let `H'=H(F minus D)` and let L count
the physical edges removed from H. Since H is a forest on the same
vertex set,

```text
c(H') = c(H)+L.
```

For an insertion set `A subset U`, list each new physical edge of
`H((F minus D) union A) minus H'` once. Contract the components of H'.
The replacement is feasible exactly when these new edges form a forest
in the resulting multigraph, with no loops or parallel-edge cycles.
This follows by inserting the physical edges one at a time, testing
whether their endpoints are already connected. In particular, merely
counting new edges against available components is necessary but not
sufficient: every subset must avoid closing a cycle.

For a maximum F, every feasible such replacement satisfies `|A|<=|D|`.
This is a rigorous starting point for an exchange proof, but does not
establish that some improving replacement exists whenever `S<n-D_0`.
The latter implication is the missing substantive theorem.

### A Neutral Exchange Cannot Raise S

For ANY two feasible sets F and G on the same board, (1) gives

```text
S(G)-S(F) = -3(|G|-|F|).                            (7)
```

Consequently all maxima have the same S, and every equal-cardinality
exchange leaves S exactly unchanged. A tie-break minimizing r can only
increase `b+c` by the amount it decreases r; it cannot directly create
weighted reserve. Normalizing a maximum might still make (3) provable
from geometry, but it requires a genuine normal-form theorem and its
weighted estimate. An assertion that neutral exchanges improve S is
algebraically impossible. Improving cardinality, when feasible, actually
decreases S rather than increasing it.

## Bounded Verification

A Python command executed in memory, without writing a script, constructed
the parallel-rod and two-comb examples on sides 8, 11, and 14. It inserted
every physical forced edge into union-find, rejected cycles, and checked
f, r, b, c and the global ledger. For the two-comb examples it also checked
that exactly two components contain F and computed their bounding boxes
from all their vertices, including holes. The results were:

```text
n   family       f   r   b   c
8   parallel    24   3  18   3
8   two combs   25   5   9   7
11  parallel    44   4  25   4
11  two combs   46   6  12   9
14  parallel    70   5  32   5
14  two combs   73   7  15  11
```

All assertions passed, including the displayed box formulas. These are
checks of explicit examples, not optimization or a substitute for the
symbolic proofs. No literal board had side larger than 14.

## Remaining Obligation

The exact contact formulation (3) is unrestricted and retains isolates,
boundary weights, long rods, and both orientations. The projection
identity (5) and exchange criteria (6)--(7) are likewise unrestricted.
They do not yield `2r-m+z+b>=n-O(1)`.

Specifically, simple line/box accounting must address both repeated cut
crossings within a tree and quadratic overlap between boxes of different
trees. Maximum-specific reasoning must control reuse of actual
connectivity witnesses, or prove a count-improving physical replacement;
neutral changes of carrier labels or counts cannot improve the objective.
These are explicit limitations, not assertions that all projection or
exchange methods fail. The global half-coefficient bound remains the
available unconditional bound from the input notes; no new unrestricted
constant C is claimed here.
