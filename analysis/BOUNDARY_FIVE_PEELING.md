# Exact Peeling At Boundary Deficiency Five

Date: 2026-09-05. Status: partially formalized, independently audited paper
proof. No grid search or optimization was used. The bound b>=5 is proved in
`lean/GridGraphs/Accounting/BoundaryFiveBudget.lean`. The corner/boundary counts, unique
perimeter gap, and all-U next ring (Sections 1-2) are now proved in
`lean/GridGraphs/Accounting/BoundaryFiveEquality.lean` on Lean 4.33.1. The concrete
canonical frame tree, its exact inner-attachment iff, and counted extension
are now checked in `BoundaryFiveFrame.lean`, `BoundaryFiveAttachment.lean`,
and `BoundaryFiveConstruction.lean`. The formal attachment criterion uses the
once-cropped square on the ambient vertex type. Normalization of arbitrary b=5
patterns and equivalence to the separate deep-square Q formulation below still
have paper-level steps; no inner target family has been constructed.

## 1. Setup

Use coordinates `1..n`, with n>=7. Let F be feasible: the graph H of every
grid edge incident to F is acyclic. Write U for its complement and assume
`b=sum_(u in U)(4-deg_grid(u))=5`.

There are exactly five noncorner boundary U vertices and no U corners. Four
are one witness from each corner's pair of boundary neighbors. The fifth is
adjacent to exactly one witness; the unique perimeter UU edge is their edge.
See `RESIDUE_TWO_COMPONENT_BUDGET.md` for the equality argument.

Normalize this edge by a grid symmetry to

```text
(1,2)--(1,3).
```

Thus `(1,2)` is a corner witness and `(1,3)` is the extra vertex. This does
not fix the choices at the other three corners, nor assume different corners
belong to different maximal preserved intervals.

## 2. The Next Ring Is Unpreserved

On the top side, the only possible U indices are `2,3,n-1`. On other sides
they are a subset of `2,n-1`. For n>=7, no two possible U positions on any
one side differ by two. Therefore every noncorner outer-boundary vertex p
has a lateral F neighbor q.

If p's inward neighbor x were F, q and x would be opposite vertices of a
unit cell. All four cell edges would be forced, a contradiction. Hence

```text
F intersect boundary([2..n-1]^2) = empty.
```

This is why the threshold here is n>=7, not merely n>=6. At n=6 the possible
side positions `2,3,5` leave a vertex flanked by two U vertices. The argument
above does not handle that case.

## 3. The Outer Tree And The One Free Vertex

The forced perimeter edges form a spanning perimeter path. Add all forced
spokes from the outer boundary to the next ring.

Each corner of the next ring has two outer-boundary neighbors, exactly one
of them F, so has exactly one forced spoke. Each noncorner next-ring vertex
has one possible spoke. Only

```text
w=(2,3)
```

lacks it, because its outer neighbor is the extra U vertex. Edges along the
next ring are not forced. Thus H restricted to the outer two rings consists
of one tree T and the isolated vertex w. T contains every other vertex of
those rings.

## 4. An Exact Smaller Problem

Let `D=[3..n-2]^2`, of side `m=n-4`, and let `z=(3,3)` be its top-left
corner. For a candidate `F_D subset D`, let H_D contain every edge of the
smaller grid incident to F_D, on ALL vertices of D.

The necessary and sufficient conditions for extension through the specified
boundary-five frame are:

1. H_D is a forest.
2. The three corners of D other than z are not in F_D.
3. Every component of H_D contains at most one vertex of `F_D intersect boundary(D)`.

Necessity: an ordinary deep corner, if preserved, has two distinct forced
attachments to T, immediately closing a cycle. The exceptional corner z has
one attachment to T and one to w, so it is permitted. Every other deep
boundary F vertex has one attachment to T. Two such boundary F vertices in
the same H_D component would also close a cycle through T.

Sufficiency: start with H_D, T, and w disjoint. Each H_D component with a
boundary F vertex attaches to T by exactly one edge. If z is F, attach w to
z as a leaf. Every edge of H is accounted for and no step creates a cycle.

For a concrete converse frame, choose exactly these outer-boundary U vertices:

```text
(1,2), (1,3), (2,n), (n,n-1), (n-1,1).
```

Make the whole next ring U and insert F_D. Any F_D satisfying conditions 1-3
then gives a feasible full-grid F with b=5. Other corner-witness choices give
the same deep conditions after normalization.

Let Q(m) be the maximum |F_D| under conditions 1-3, with a designated
exceptional corner. We obtain the exact restricted recurrence

```text
max_(F feasible, b(F)=5) |F| = 4n-9 + Q(n-4),    n>=7.
```

This is NOT `4n-9+P(n-4)`: the attachment condition is essential. Nor does
it prove that an unrestricted optimum has b=5.

## 5. Exact Component Accounting

Write `f_D=|F_D|`, let r_D be the number of induced F_D components, and
let c_D count H_D components INCLUDING isolated vertices. Put

```text
t = |F_D intersect boundary(D)|,
e = 1 if z is in F_D, otherwise 0.
```

The outer perimeter has `4n-9` preserved vertices in four F-runs, since
its five U vertices form four blocks. The all-U next ring separates these
runs from D. The attachment construction gives

```text
f = 4n-9+f_D,
r = 4+r_D,
c = c_D+2-t-e,
B = r_D+c_D+11-t-e.
```

Each of the t attachments joins a distinct inner component to T, and the
additional e attachment joins w. These are physical edges, not repeated
counts of a shared resource. The root restriction implies c_D>=t, so

```text
c=1 iff e=1 and c_D=t.
```

Equivalently, z is preserved and EVERY H_D component has exactly one preserved
boundary root. In particular, isolated U vertices are forbidden in this
connected subclass.

## 6. The Stable Construction Target

For the optional outer class

```text
n=3k+2, b=5, c=1, f=3k^2+7k,
```

the exact inner problem is

```text
m=3k-2,
f_D=3k^2-5k+1=(m^2-m-3)/3,
r_D=3k+2,
z in F_D,
every H_D component has exactly one preserved boundary root.
```

The three ordinary corners must each have exactly one F neighbor: none
would leave an unrooted isolated U corner; two would connect two roots.
The exceptional corner is a singleton induced F component, since an adjacent
boundary F vertex would be a second root in its component. Distinct preserved
boundary roots cannot be adjacent or separated by one boundary vertex.

These are actual coordinate and attachment constraints, not an abstract
target-count skeleton. Existence at the required score remains open.

## 7. A Further Construction Constraint

In the fully rooted inner class, every U vertex has an F neighbor. In local
coordinates `1..m`, suppose a horizontal preserved interval lies on row 3,
from column a to b, with length ell>=2. Every vertex of row 2 above it is U,
by the diagonal-pair cell obstruction.

At most one top-boundary vertex directly above this interval can be F:
two would join the interval component to two roots. For each strict interior
column of the interval, the top-boundary vertex cannot be dominated from
below, so it must itself be that one root or be a horizontal neighbor of it.
Thus `ell-2<=3`, giving

```text
ell<=5.
```

If ell>=3, the component must be rooted on the top side directly above it.
The rotated statements hold on the other three tracks two steps from a side.
Long rails close to a parallel boundary therefore cannot be repaired just by
giving their component a remote root. This restriction assumes the fully
rooted class, not arbitrary feasible F or arbitrary b=5 constructions.

## 8. Explicit Improved Inner Family (Formalized)

The following coordinate construction is now formalized in
`lean/GridGraphs/Constructions/ResidueTwo/ResidueTwoStaircase.lean` and `ResidueTwoStaircaseForest.lean`.
Lean checks the actual count, placement, support geometry, forced acyclicity,
and unconditional bound transfer. It improves the affine arbitrary-width lower
score but does not attain the stable target. No finite search was used.

Use deep coordinates `1..m`, with `m=3s+1` and `s>=2`. Start with

```text
z=(1,1),
R_j={(3j+2,c): j+3<=c<=m},       0<=j<=s-1,
L_j={(3j+4,c): 1<=c<=j+2},       0<=j<=s-2.
```

Their forced supports are pairwise disjoint. The closest interleaved interval
pairs have center distance three; each horizontal interval is a path with
pendant neighbors and has exactly one preserved deep-boundary endpoint. The
singleton z is the permitted corner. The baseline size is

```text
1 + sum_(j=0..s-1)(3s-j-1) + sum_(j=0..s-2)(j+2) = 3s^2.
```

Add two alternating families, with t a nonnegative integer:

```text
B={(m,   s+1-4t): s+1-4t>=2},
P={(m-1, s-1-4t): s-1-4t>=2}.
```

Their columns interleave as `s+1,s-1,s-3,...` down to the last value at
least two. Consequently

```text
|B|=floor((s+3)/4), |P|=floor((s+1)/4),
|B|+|P|=ceil(s/2).
```

Here is the actual attachment check, not just a density argument:

- Each B star is disjoint from the baseline supports. Its distance to the
  final right interval, on row m-2 and columns s+2..m, is at least three;
  its distance to the final left interval, on row m-3, is also at least three.
- A P center `(m-1,c)` has `2<=c<=s-1`. Its star intersects precisely the
  final left interval's star, at the single vertex `(m-2,c)`.
- B centers and P centers within their own families are at least four columns
  apart. A B/P pair has column difference congruent to two modulo four and
  row difference one. All these added stars are pairwise support-disjoint.
- Each B creates a new component with its sole preserved boundary root at B.
  Each P is interior and merely adds a branch to the final left-rooted tree.
  Its bottom boundary neighbor is U, not an additional preserved boundary root.
  The other three deep corners remain U.

Thus the deep forest and the one-preserved-boundary-root condition hold.
Equivalently, in the full ambient frame, each baseline interval attaches once
to the frame tree, each B star attaches once to that tree, and each P star
attaches once to its left-interval component. The exceptional z picks up w as
a leaf as before. This also gives a direct interval-star gluing proof route.

For k=s+1, place each deep coordinate `(r,c)` at ambient zero-based `(r+1,c+1)`.
The full preserved score is

```text
3s^2+ceil(s/2)+4n-9
  = 3k^2+6k+2+floor(k/2),                 k>=3, n=3k+2.
```

This is a lower bound, NOT an optimum formula. It exceeds the affine score
`3k^2+6k+5` for k>=8, and equals it at k=6,7. Its stable target deficit is
`floor((k-1)/2)-1`. In particular, at k=8 (side 26), it gives score 246
versus affine 245 and conjectured 248; this example is arithmetic substitution,
not a computation on a 26x26 grid.

The empty P case s=2 needs no special repair: B consists of `(7,3)` and the
deep score is 13. At s=3 and s=4 the added counts are two, with P attached
at `(8,2)` and `(11,3)` respectively. These are direct coordinate checks,
not exhaustive optimization. No addition-only optimality claim is needed here.

## 9. Next Gates And Limits

1. Equality classification, the all-U next ring, the canonical outer tree,
   both directions of its attachment theorem, and the actual extension count
   are checked. The remaining canonical lower gate is the input A, not another
   general gluing interface.
2. The explicit improved family is now formalized through actual interval-star
   gluing. Seek the additional vertices needed for the exact target; do not
   label the improved score an exact result.
3. A successful Q family at that count supplies the outer lower bound even
   without c=1; do not retain full rootedness if it unnecessarily blocks a
   feasible target-score construction.
4. For upper bounds, this class alone is insufficient: configurations with
   b>=6 remain unaddressed. A normal-form theorem reducing all optima to b=5
   is not known and must not be assumed.

No target family, matching upper bound, or explanation of the k=5 threshold
has been proved here. The canonical lower construction now has a checked
counted reduction; the full Q identity above retains its stated paper-level
normalization and coordinate-translation obligations.
