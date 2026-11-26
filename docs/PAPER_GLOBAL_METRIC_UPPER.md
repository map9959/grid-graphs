# Global Metric Upper Attempt

Date: 2026-09-08. Independent paper investigation. No unrestricted
constant-gap bound is proved. No optimization or Lean work was performed.

## Outcome

Current review status: independent read-only audits covered the full note
through the wider-mismatch continuation (original line 736). One scope
overstatement about low K was corrected below; the mathematical deductions
otherwise passed review. Historical unaudited-status paragraphs describe
the time of their respective appendices, not the current review status.
No unconditional constant-gap theorem is established.

The new obstruction concerns the suggested planar rectangular-partition
route, rather than another local cap payment:

* Every rectangular cut creates exactly twice its length in artificial
  `r+b+c` budget. Even a sharp short-side theorem for both children of a
  square gives a negative lower bound after this artificial budget is removed.
* An explicit feasible pinwheel family has `r+b+c=O(n)` and only `O(n)`
  exceptional dual cells, but every first guillotine cut splits at least
  `(n-4)/9` positive corridors. Its corridor strips are physically disjoint;
  overlapping component boxes are not the cause of the obstruction.

Thus noncrossing geometry does not automatically provide either a
corridor-preserving guillotine decomposition or a decomposition with only
`O(1)` initial corridor fragments. A successful partition proof needs a
length-sensitive interface theorem, not the sum of short-side bounds on
the pieces. The example has ample reserve and does NOT rule out such a
theorem restricted to `r+b+c<n-O(1)`.

Inputs read: the complete [dual checkpoint](PAPER_DUAL_UPPER_RESEARCH.md),
including its final cap appendix; the
[half-coefficient note](PAPER_HALF_COEFFICIENT_UPPER.md); and the relevant
projection and nested-cycle investigations. The present note changes none
of those files and claims no independent audit or formal verification.

## Target And Length Conversion

Let `H` contain exactly the grid edges incident to the preserved set `F`,
and assume `H` is a forest. Use the actual carrier count `r`, boundary-hole
deficiency `b`, and component count `c`, including isolates. Put

```text
K=r+b+c,  f=|F|,  A=n-1.
3f+K=n^2+4n.
```

For `n=3k+2` and `T=3k^2+7k`, this is

```text
K=n+10-3(f-T).
```

In the once-pruned dual, let `X_2` count straight crossing-origin cells,
equivalently the sum of the numbers of internal straight cells of actual
corridors. The checkpoint proves, without an isolate-free hypothesis,

```text
A^2=3X_2+Q_exc,  0<=Q_exc<=10K.                     (1)
```

Consequently a genuine metric estimate

```text
3X_2 <= A(K+C),  C>=0 fixed,                        (2)
```

would give the explicit unconditional conclusion

```text
(A+10)K >= A^2-AC,
K >= A-10-C+(100+10C)/(A+10) > n-11-C,
3(f-T)<21+C.                                       (3)
```

In particular `C=0` would prove `f<=T+6`. This calculation keeps the
exceptional area in the same budget, not in a stronger auxiliary target.

There is also a useful converse warning. If `K>=n-D`, with fixed `D>=0`,
then `3X_2/A<=A<=K+D` by (1). Thus a bounded-error version of (2) is,
up to the explicit constant loss in (3), equivalent to the desired theorem.
Integrating straight-cell indicator functions over parallel cuts gives
exactly `X_2`; that integration alone is not an extra inequality. The
substantive input must bound the resulting integral by the natural budget.

## Exact Rectangular Cut Ledger

Consider a feasible configuration on a `w` by `h` vertex rectangle. Its
ledger is

```text
3f+K=wh+2w+2h.
```

Split its vertex set between two consecutive columns into rectangles of
widths `a` and `w-a`. There are `h` original grid edges across the cut.
Write `N_FF,N_FU,N_UU` for their three types, with `FU` unordered, and
compute each child's counts using its OWN grid degrees and components.
Then

```text
r_left+r_right = r+N_FF,
c_left+c_right = c+N_FF+N_FU,
b_left+b_right = b+N_FU+2N_UU,
K_left+K_right = K+2h.                             (4)
```

Proof: deleting an edge of a forest increases its component count by one.
Apply this to the induced `F` forest and to `H`. Restriction creates one
new unit of boundary deficiency at each hole endpoint of a cut edge.
Summing counts each of the `h` cut edges twice, whatever its type. This
also proves (4) when restriction exposes many new isolated holes.

For any partition into vertex rectangles, let `L` be the total number of
original grid edges between distinct parts. The same argument gives

```text
sum_parts K_part = K+2L.                           (5)
```

Neither actual tree components nor carrier labels may be silently retained
across the cuts while using the children's rectangular ledgers.

### Why Short-Side Induction Does Not Close

Suppose, even optimistically, that every piece of a guillotine partition
is already known to satisfy `K_part>=min(w_part,h_part)-C`, with `C>=0`.
Its summed consequence is only

```text
K >= sum_parts min(w_part,h_part)-2L-C*(number of parts).          (6)
```

After the FIRST vertical cut of an `n` by `n` square, the two short sides
sum to `a+(n-a)=n`, while `L=n`. Thus even with `C=0`, (6) gives `K>=-n`.

Further cuts cannot repair this bound. For a vertical cut of a `w` by `h`
rectangle, the change in the short-side sum obeys

```text
min(a,h)+min(w-a,h)-min(w,h) <= h.
```

If `w<=h` the left side is zero; otherwise each of the first two terms
is at most `h`. The interface subtraction increases by `2h`. Hence the
right side of (6) decreases by at least `h`, before its additional error
term. The horizontal case is identical.

This is a precise failure of this induction scheme, not a failure of the
short-side target. Area divided by the long side is the short side, so
using that version of a strip-capacity estimate has the same problem.
Any useful induction must retain more interface information than the
children's unrestricted `K` bounds.

## A Feasible Nonslicing Corridor Family

Here is a symbolic construction for every integer `s>=2`. Put

```text
n=9s+4,
coordinates x,y in {0,...,9s+3}.
```

Preserve the following five families of rods, and nothing else:

| Family | Preserved vertices | Rod count | Rod length |
|---|---|---:|---:|
| Top | `y=3j`, `0<=x<=6s`, `0<=j<=s` | `s+1` | `6s+1` |
| Right | `x=6s+3+3j`, `0<=y<=6s`, `0<=j<=s` | `s+1` | `6s+1` |
| Bottom | `y=6s+3+3j`, `3s+3<=x<=9s+3`, `0<=j<=s` | `s+1` | `6s+1` |
| Left | `x=3j`, `3s+3<=y<=9s+3`, `0<=j<=s` | `s+1` | `6s+1` |
| Center | `y=3s+3+3j`, `3s+3<=x<=6s`, `0<=j<s` | `s` | `3s-2` |

### Feasibility And Budget

Distinct rods have grid distance at least three. Within a family this is
their spacing. For neighboring outer families the separating coordinate
gap is three: for example Top ends at `x=6s` and Right begins at `x=6s+3`,
while Top ends at `y=3s` and Left begins at `y=3s+3`. Opposite families
are farther apart. The central family is separated by three from the
nearest rods of all four outer families.

Their closed grid neighborhoods are therefore vertex-disjoint. Every
single rod forces a path with pendant neighbors, a tree; there are no
forced edges between these supports. All remaining vertices are isolated
holes. This proves feasibility for all `s`, not by finite evidence.

Directly,

```text
f=4(s+1)(6s+1)+s(3s-2)=27s^2+26s+4,
r=5s+4.
```

For the deficiency on preserved vertices, each outer family contributes
`6s+1` along its full boundary rod and `s+1` at its transverse boundary
ends. Corners correctly contribute in both directions. The central rods
are interior. Thus

```text
4n-b=4(7s+2),
b=8s+8,
K=n^2+4n-3f=30s+20,
c=17s+8,
z=c-r=12s+4.                                       (7)
```

In particular `K=O(n)`, not quadratic. By (1), `Q_exc=O(n)` as well.
The central rods are included precisely to avoid leaving an uncovered
quadratic-area central square. Isolates have not been discarded.

### Every First Cut Fragments Many Corridors

Use cell coordinates given by their lower-coordinate corner. For two
parallel rods on rows `u,u+3` with a common horizontal `FF` interval,
the intervening cells on row `u+1` are straight crossing-origin vertices:
their two perpendicular neighbors are dual leaves. Thus this construction
contains the following straight corridor portions:

```text
Top:    y=3j+1,       x=0,...,6s-1,       0<=j<s;
Bottom: y=6s+4+3j,    x=3s+3,...,9s+2,    0<=j<s;
Right:  x=6s+4+3j,    y=0,...,6s-1,       0<=j<s;
Left:   x=3j+1,       y=3s+3,...,9s+2,    0<=j<s.
```

They are portions of actual positive corridors, not arbitrary line segments
drawn through exceptional cells. The width-three bands assigned to these
portions are disjoint physical cell sets.

Split the vertex board between columns `a-1` and `a`, where
`1<=a<=9s+3`. Its geometric cut line passes through cell column `a-1`.
If `a<=6s`, it meets all `s` Top straight portions. If `a>=3s+4`, it meets
all `s` Bottom portions. These two ranges cover every possible `a` for
`s>=2`. A horizontal cut has the identical property using Right and Left.

Therefore EVERY possible first full guillotine cut meets at least `s`
distinct positive corridors in their straight portions. Their `s+1`
bounding rods also cross that cut; adjacent bands share a bounding rod,
so those rods must not be counted twice. Consequently the first cut crosses
at least `s+1` distinct `FF` edges, so (4) creates at least `s+1` additional
carrier fragments. This is an actual fragmentation count,
not a consequence of overlapping boxes or a fictitious common exterior
port location.

The family also obstructs cutting the cell array along full grid lines
between cell centers: Top corridor edges span cuts `1,...,6s-1`, and Bottom
edges span `3s+4,...,9s+2`; these ranges again cover all internal cuts for
`s>=2`. Thus switching between vertex and cell partitions does not produce
a free first separator.

This proves that neither noncrossing strips nor a linear exceptional area
forces a guillotine first cut with only `O(1)` corridor intersections.
Nonslicing rectangular arrangements genuinely occur in feasible forced
forests, even without contacts between distinct carrier supports.

## Scope Of The Obstruction

The pinwheel has `K=(10/3)n+20/3`, so it satisfies the desired bound with
large reserve. It is not a counterexample to (2), nor to any global
constant-gap upper bound. It also does not exclude an arbitrary nonslicing
rectangular completion of the corridor bands. What it excludes is the
inference that planarity supplies a corridor-preserving recursive full cut,
or that the cost of its first fragmentation is an absolute constant.

A metric averaging argument may still transport credit across these cuts
without charging every fragment a new full-board length. Equations (4)--(6)
show the exact interface cancellation it must achieve. In particular,
one cannot both use all the artificial boundary/component credit in the
children and omit the `2L` subtraction when returning to the original board.

For the original problem, the outstanding theorem remains a genuinely
global, length-weighted inequality such as (2), possibly after excluding
configurations already having `K>=n-C`. The local cap bank and the matching
invariant in the dual checkpoint do not supply it, and this partition
attempt does not supply it either. No unconditional constant `C` has been
obtained; the established half-coefficient upper bound is unchanged.

All arbitrary-size claims above have symbolic proofs. As an arithmetic and
feasibility check only, an in-memory command constructed the same rod
formulas at `s=1`, side 13, inserted every physical forced edge into
union-find, and checked

```text
(f,r,b,c,z)=(57,9,16,25,16).
```

The forest test and all count formulas passed. The universal-separator
claim requires `s>=2` and is proved symbolically above, not inferred from
this smaller seed. No board search, optimization, build, or Lean
verification was run; no board above side 13 was instantiated.

## Low-Budget Continuation

This appendix reads the subsequent scalar continuation of
[Global Cap Payment](PAPER_GLOBAL_CAP_PAYMENT.md) and the actual dirty-strand
payment in [Isolate Routing](PAPER_ISOLATE_ROUTING_UPPER.md). The previous
pinwheel is not used against the hypothesis `K<n`.

No unconditional constant is obtained in this continuation. There is a new
spatial width inequality, however: sufficiently long overlaps of parallel
carriers at distance FOUR consume actual isolated vertices at coefficient
one, globally and in both orientations together. This is not an endpoint
count or a rearrangement of the scalar ledgers. A boundary-window version
also retains the cost of perturbing a nearly full boundary interval.

### Distance-Four Width Theorem

Consider any two horizontal preserved carriers on rows `a` and `a+4`.
Let their common column interval be `I=[u,v]`, of vertex length
`ell=v-u+1>=2`. Define its middle strip to be the actual vertex set

```text
J={ (x,a+2): x in I }.
```

Let `z_J` count globally isolated H vertices in J, and let `epsilon_J`
indicate whether J contains a preserved vertex. Then

```text
epsilon_J in {0,1},
ell <= z_J+2+3epsilon_J <= z_J+5.                  (8)
```

Proof: all vertices of rows `a+1` and `a+3` above or below I are U.
For each such vertex, an adjacent-column F vertex of the corresponding
carrier gives the forbidden diagonal if it were F. At an endpoint of I,
use its inward neighbor; `ell>=2` is needed here.

There cannot be two F vertices `(x,a+2),(x',a+2)` with `x<x'` in J.
Each would give an entirely forced vertical path between the two carrier
rows: its outer edges are forced by those rows, and its middle edges by
the middle F vertex. The two paths and the top and bottom carrier intervals
form the perimeter cycle of `[x,x'] x [a,a+4]`. This proves the assertion
about epsilon_J without assumptions on external connections.

Every nonisolated vertex of J must consequently be either its sole F
vertex or a horizontal neighbor of an F vertex on that same middle row.
The F vertex inside J accounts for at most three vertices of J, including
itself. F vertices outside J can reach only its two endpoints. There are
no F neighbors above or below J. This proves (8). Vertices counted by z_J
are isolates in the ORIGINAL H, not merely uncovered in a restricted strip.

Rotation gives the vertical theorem. It applies to interior rails as well
as boundary rails, and permits arbitrary F elsewhere on the board.

### Simultaneous Nonreuse

Retain ALL horizontal and vertical distance-four carrier pairs whose
overlap has at least two vertices. Their middle strips are pairwise
vertex-disjoint.

For two horizontal strips, an intersection requires the same middle row,
hence the same two carrier rows. At an intersecting column, the preserved
vertex in each bounding row belongs to just one actual carrier. The two
pairs are therefore identical. The vertical case is identical.

For a horizontal and a vertical strip, suppose their intersection were
`(x,y)`. The horizontal pair has F on rows `y-2,y+2` over a common interval
containing x. Since that interval has length at least two, choose
`sigma in {-1,1}` such that it also contains `x+sigma`. Similarly choose
`tau in {-1,1}` so that the vertical pair's common interval contains both
y and `y+tau`. In particular the two vertices

```text
(x+sigma,y+2tau),  (x+2sigma,y+tau)
```

are F. They are diagonal corners of one unit cell, forcing its four-cycle.
This contradiction proves cross-orientation disjointness. No bounding-box
disjointness or assumption about distinct H components is used.

Let `N_4` count these pairs, `W_4` be their total overlap length, and `E_4`
count those with an F vertex in their middle strip. Summing (8) therefore
proves the unconditional physical inequality

```text
W_4 <= z+2N_4+3E_4 <= z+5N_4.                     (9)
```

The coefficient on z is ONE, not two for the two orientations. This is a
new restriction on actual interval placements; the aggregate data in the
cap note's synthetic scalar family do not specify W_4 or E_4.

The theorem is sharp at the level of its growing width cost. Two full
parallel rows at distance four, joined by one middle singleton, leave all
but three vertices of the middle row isolated when there are no outside
endpoint suppliers. Thus a long such gap really can cost its entire width
in isolates, with only a constant endpoint correction.

### Consequence Under K<n

Write `c_0=c-z` for the number of H components containing F. Under `K<n`,
F is nonempty and `c_0>=1`. For any selected subcollection of these pairs
with overlap lengths at least an integer `L>5`, let `N_L,W_L` be its
count and total width. Disjointness and (8) give

```text
(L-5)N_L <= z = K-r-b-c_0 < n-r-b-c_0,
W_L <= z+5N_L <= z*(1+5/(L-5)).                    (10)
```

In particular a macroscopic distance-four overlap cannot be treated as a
bounded-cost cap. For `L>=epsilon*n`, the number of such overlaps is
bounded in terms of epsilon, and their total width is at most `z+O(1)`
under `K<n`, for fixed epsilon and sufficiently large n.

This is a metric consequence of the low-budget hypothesis, not a conclusion
that every remaining corridor can be joined. The z units used in (9) or
(10) are the original component resource. They must not also be offered as
unspent credit in the isolate note's routing account.

### Perturbed Boundary Windows

There is a self-contained robust version when the outer rail is not full.
Suppose a horizontal preserved carrier on row four contains `I=[u,v]`,
with `ell>=2`, and let h be the number of boundary holes `(x,0)` for x in I.
Let `J^o` be row two over the strictly interior columns of I, and let
`z_I` count global isolates there. Then

```text
ell <= z_I+7h+5.                                   (11)
```

To prove this, row three over I is entirely U, by the diagonal exclusion
against the row-four carrier. Let m_2 count F vertices on row two over I.
The F vertices on the boundary interval form at most `h+1` runs. For each
such run, at most one of its columns can also be F in row two: two such
columns would give the height-four perimeter cycle from the proof of (8),
using that boundary run and the full row-four carrier. The h columns with
a boundary hole can contribute at most h further row-two vertices. Hence

```text
m_2 <= 2h+1.
```

Let m_1 count F vertices on row one over the interior columns of I. Each
requires its upper-right diagonal boundary vertex to be U; these vertices
are distinct and remain in I. Thus `m_1<=h`. Every nonisolated vertex of
J^o is covered by a row-one F neighbor or by a row-two F vertex within one
horizontal step. All these latter columns lie in I, and row three supplies
none. Therefore

```text
ell-2-z_I <= m_1+3m_2 <= 7h+3,
```

which proves (11). This proof permits arbitrary centers in rows zero, one,
and two and does not fix their component partition.

For simultaneous four-side use, restrict each longitudinal interval to
coordinates `5,...,n-6`, retaining intersections of length at least two.
Use horizontal carriers on rows four and `n-5`, and vertical carriers on
columns four and `n-5`. The resulting five-row or five-column windows are
disjoint. So are their boundary-hole witnesses and their isolate witnesses.
If R counts the selected intervals and W their total length, (11) gives

```text
W <= z+7b+5R.                                      (12)
```

No carrier contributes to two selected intervals: the relevant rows and
columns are distinct for `n>=11`, and the selected carriers have their
specified nonsingleton axes. Clipping can lose lengths near corners, but
no claim about those lost lengths is needed for (12).

The existing five-column variable-rail theorem in
`PAPER_FAULT_LINE_ANALYSIS.md` gives a stronger optional version. In each
window its row three is U, its row-four mass is ell, and its boundary mass
is `ell-h`. Its bound `TOTAL_F<=2ell+2` consequently gives
`m_1+m_2<=h+2`, where m_1 here includes all columns of I. The same domination
count on J^o then yields

```text
ell <= z_I+3h+8,
W <= z+3b+8R.                                      (13)
```

Equation (11) has the elementary proof above; (13) additionally uses that
existing finite-state paper theorem. Neither is asserted to have been
independently audited or formalized in this continuation.

### What Still Blocks Closure

A phase change that presents a long depth-four rail to an almost full
parallel boundary must now pay its actual exposed width, by (11) or (13).
If that boundary is full, the coefficient-one isolate tax (9) applies.
Thus one cannot complete a proposed sloping-seam layout by declaring its
wide terminal gap to have only a constant endpoint cost while retaining
both rails. Filling the middle row at many columns would create literal
cycles, not merely violate an abstract scalar allowance.

This does not establish that EVERY near-complete low-K corridor packing
presents enough such parallel overlaps. Its terminal regions can change
orientation, interrupt the bounding carriers, or move the interface away
from this four-step spacing. The current scalar data do not determine the
total widths after those changes. In particular, the one-sided dirty
one-bend event in the isolate note does not by itself assert the existence
of a long distance-four pair.

What this continuation proves is the global spatial restriction (9), its
low-budget consequence (10), and the jointly allocated boundary-window
bounds (12)--(13). It does NOT infer a lower bound on W_4 or W from the
near-complete area partition. That missing inference would require a new
rectangulation/interface argument tracking the actual replacement carriers
and their connectivity. No unconditional `K>=n-C` or constant excess has
been proved here, and no new scalar residual is offered as its replacement.

Verification for this appendix: an in-memory command checked 128 explicit
feasible configurations on sides 11 and 14. The inputs were two-rail
constructions, their rotations, and prescribed vertex deletions; there was
no optimization or search for a large preserved set. It checked every
physical forced edge for cycles, extracted the actual carriers and global
isolates, and verified 249 distance-four pair inequalities and their mutual
strip disjointness. It also checked 127 boundary windows against (11) and
(13). All checks passed. The arbitrary-size arguments are the proofs above,
not inferences from these checks. No board above side 14 was instantiated,
no Lean command was run, and only this appendix was written.

## Wider Mismatch Continuation

This continuation tested the proposed extension from separation four to
separation `3q+1`. It does not prove the unconditional constant-gap bound.
The completed deductions identify an actual change of payment resource at
separation seven, prove a width-sized carrier payment for an explicit
orientation-changing strip even under arbitrary feasible extension, and
exhibit the nonreuse problem for summing arbitrary wider mismatch pairs.
These are physical constructions and restrictions, not synthetic budgets.

### Separation Seven Does Not Force Isolates

Let `W=4m+1`, `m>=1`, on a W by 8 vertex rectangle. Preserve the two full
rows zero and seven. In the four middle rows preserve exactly

```text
column x=0 mod 4:  (x,2), (x,4);
column x=2 mod 4:  (x,3), (x,5).
```

Columns of odd index have no middle preserved vertices. Rows one and six
are U. The five-column prefix is

```text
FFFFF
.....
F...F
..F..
F...F
..F..
.....
FFFFF
```

The pattern repeats by four columns. Its exact counts are

```text
f=3W+1,  r=W+3,  b=8,  c=2,  z=0,
K=W+13.                                            (14)
```

Here is an arbitrary-width forest and coverage proof. At each column
`x=0 mod 4`, the two middle stars meet at `(x,3)` and attach to the top
rail through `(x,1)`. Their union is a single branch of the top rail tree.
At each column `x=2 mod 4`, the corresponding two stars meet at `(x,4)`
and attach through `(x,6)` to the bottom rail tree. The two types have
preserved-set distance at least three from one another, so their forced
supports are disjoint. Distinct branches of the same type meet only their
own rail support, at their distinct attachment holes. There are therefore
exactly two nontrivial trees and no forced edges between them.

At an even column all four middle vertices are covered by its two stars.
At an odd column, the adjacent even columns supply the four middle-row
neighbors, alternating between the two trees. The first and last columns
are even, so this covers every vertex, including both ends. Hence z=0.

There are W+1 middle F vertices, all singleton carriers in this displayed
configuration, and the two rail carriers. The only boundary holes are the
four middle/near-rail holes on each short side; the long boundary rows are
full. These observations prove every count in (14) directly.

Thus even with both facing rails full, at separation seven an arbitrary
width cannot be charged to isolates or ambient components with a bounded
error: both z and c remain bounded. New carriers, not those two resources,
are essential. More quantitatively, any such universal strip estimate

```text
W <= alpha*r_middle + beta*c + gamma*z + C(q)
```

with fixed beta, gamma and q=2 must have `alpha>=1`, since
`r_middle=W+1` here. Equivalently, formal carrier endpoints cannot be
offered at a coefficient below one half each in this proposed payment.
This does not refute the coefficient-one carrier-plus-component version.

### The Interior Carriers Cannot Be Merged Away

The carrier payment in this example is not an artifact of stopping the
configuration at the window. Suppose any larger feasible set retains all
its displayed F vertices, with arbitrary further choices inside and outside
the window. Every middle F vertex at an even column

```text
2<=x<=W-3
```

must still be an actual singleton carrier. There are W-3 such vertices,
so the larger configuration satisfies

```text
r >= W-3.                                          (15)
```

For proof consider a column `x=0 mod 4`, whose middle centers are on rows
two and four. A putative horizontal F neighbor of either center would be
diagonal to one of the centers on rows three and five in the neighboring
even column. These four horizontal extensions are forbidden.

The row-one neighbor is U by the diagonal obstruction against the top
rail. Promoting `(x,3)` or `(x,5)` would add both horizontal edges to its
two odd-column neighbors. Both of those neighbors already lie in the same
bottom rail tree: they are leaves of the displayed centers at `x-2` and
`x+2`. The existing path in that tree and the two new edges form a cycle.
Consequently neither vertical extension is possible. This uses an actual
path already present in the displayed subset; adding distant centers
cannot remove it.

For `x=2 mod 4`, exchange top and bottom. The row-six neighbor is forbidden
by the bottom rail, and promoting a neighbor on row two or four would join
two existing leaves of the top rail tree. The same argument excludes every
extension. The restriction on x guarantees that both adjacent even columns
used in this proof lie in the window.

This proves (15) without assuming that the two rail trees remain separate
after an extension. Their already existing internal paths suffice. A copy
of longitudinal width `W>=n-d` inside a square consequently proves the
actual bound `K>=n-d-2`, since c>=1, irrespective of all other geometry.
The unresolved issue is existence of enough appropriate windows, not the
payment of this particular one once present.

### Wider Pair Widths Are Not Jointly Private

The disjointness theorem for distance-four middle strips does not extend
to summing all `3q+1` rail-pair widths, even in a square with z=0 and only
linear exceptional area.

For any integer s>=0 put `n=6s+11`. Preserve the full horizontal rails

```text
upper bank: y=3i,           0<=i<=s;
lower bank: y=3s+7+3j,      0<=j<=s+1.
```

In their sole seven-step gap, add the preceding middle pattern, translated
by `3s` in y. Its formulas make sense for any odd n: when the final even
column is of the other type, its own two stars still cover that column.
Do not add any other F vertices.

All the three-step gaps are covered by the disjoint supports of their
bounding rails. The seven-step gap has the two-tree coverage just proved.
Its stars attach only to its two bounding rail trees. Therefore the whole
square is a forced forest with no isolates, and its exact counts are

```text
t=2s+3                    (number of full rail carriers),
f=tn+n+1,
r=t+n+1=n+2s+4,
c=t=2s+3,  z=0,
b=2n-2t-4=2n-4s-10,
K=3n-3.                                            (16)
```

The two outer horizontal rails contribute boundary deficiency 2n on F;
all t rail endpoints contribute 2t; the four middle F vertices on the two
vertical boundaries contribute four. This proves the displayed b count,
with corner deficiencies counted in both directions. The forest argument
proves c independently of the ledger.

Every upper-bank rail and every lower-bank rail form a pair of separation

```text
(3s+7+3j)-3i = 3(s+j-i+2)+1,
```

and each pair has overlap width n. There are `(s+1)(s+2)` such pairs. Hence

```text
sum_all_these_pair_widths = n(s+1)(s+2)=Theta(n^3),
K=O(n),   r=O(n),   c=O(n),   Q_exc<=10K=O(n).      (17)
```

All these mismatches share one actual seven-step defect region and its
same middle singleton carriers. Even the carriers protected by (15) cannot
be charged anew to each enclosing pair. Dividing each pair's width by the
square side still leaves quadratic demand against a linear natural budget.

This specifically refutes summing arbitrary wider pairs. If "facing" is
defined to exclude an intervening full rail, only the closest pair in
this construction is eligible; (17) is NOT a counterexample to that more
carefully restricted proposal. Rather, choosing and proving a canonical
non-reusing exposure rule is essential, not supplied by the residue of the
separation alone. As with the earlier pinwheel, (16) has ample K and is
not offered as a low-K counterexample.

### Current Closure Status

At separation four the forced crossconnections leave at most one middle
center and put the width cost into actual isolates. At separation seven,
the displayed alternating pattern avoids repeated crossconnections by
keeping two rail-rooted trees separate. It replaces that isolate cost by
linearly many immutable singleton carriers. Thus the repeated-connection
argument alone does not identify one universal type of width witness.

For a copy of width W>=n-d, (15) gives K>=n-d-2, excluding K<n-d-2,
not every K<n. No argument has been shown to force such a copy,
a long distance-four overlap, or a jointly sufficient collection of either.
Nor has it been shown that each remaining intermediate cap exposes such
a window of width A/3. A cap's back-face FF edge is only a short local rail;
extending it into a second facing rail of the required separation and
width is an additional unproved geometric assertion.

No unconditional constant follows from this continuation. The new proofs
are the physical change of payment resource (14), its extension-stable
carrier charge (15), and the wider-pair nonreuse obstruction (16)--(17).
The missing global exposure argument remains open, including the
all-one-pair eligible class in the cap note. No fresh scalar identity is
being substituted for that argument.

Verification: bounded frontier tests used height eight and prefix widths
at most 15 to test strip proposals. A five-column repeating state exposed
the construction in (14); its arbitrary-width proof above does not rely
on pumping an unchecked abstract state. Separate direct union-find checks
verified (14) on widths 5, 9, and 13, and (16) on the 11-square, including
all global isolates, carriers, and boundary weights. All those direct
checks passed. No optimization above dimension 15, no Lean command, and
no edit outside this appended note was performed. These new deductions
have not been independently reviewed.

A further direct check attempted all 72 neighbor promotions at the protected
middle centers on those three rectangles. Every promotion created a forced
cycle, confirming the extension obstruction used in (15) on these inputs.
The uniform proof remains the explicit diagonal and existing-path argument.
