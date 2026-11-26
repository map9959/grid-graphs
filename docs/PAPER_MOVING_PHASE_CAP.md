# Moving-Phase Cap Research

Date: 2026-09-07. Paper research with bounded experiments at sides 11 and 14.

## Outcome

No `T(k)-O(1)` construction is established. The new result is a **two-row
cap obstruction for the concrete moving-phase interior**, not the previously
failed fixed-boundary stripe or an endpoint-window search.

After a single endpoint deletion, retain the moving-phase centers below row
two and allow **arbitrary center occupancy in both rows zero and one**. This
allows a linear number of boundary and next-ring additions and deletions,
with no prescribed cap component count. Every feasible result satisfies

```text
|F| <= T(k) + 3 - ceil(k/2).
```

Thus this entire two-row replacement class cannot close at bounded net cost.
The obstruction is that the retained lower support has already joined all
`k+2` upper terminals into one actual tree. It is not a ban on adding centers
in the next ring. A quantitative extension below allows arbitrary edits
below the cap and shows that at least a linear number are necessary. It does
**not** exclude the linear, count-balanced distributed changes permitted in
the question, nor simultaneous redesign of all four sides.

## Coordinates And Baseline

Use zero-based `(row,column)` coordinates on `[0,n-1]^2`, where

```text
n = 3k+2,  k >= 3,
T(k) = 3k^2+7k.
```

For a center set `F`, `H(F)` contains all ambient vertices and every grid
edge having a center endpoint. Feasible means forest; ambient isolates and
multiple components are allowed.

The input is the concrete construction in
[Paper Constant-Gap Lower](PAPER_CONSTANT_GAP_LOWER.md), sections
"Concrete Moving-Phase Strip" through "Failed Cap And Specific Remaining
Interface". Its packets and interior word are

```text
L = UU.   R = .UU   X = U.U   H = UUU
C_a = . L^a X R^(k-a-1) .
W_a = . L^a H R^(k-a-1) .
D_a = . L^a H H R^(k-a-2) .

row 3a+2: C_a,  0 <= a <= k-1
row 3a+3: W_a,  0 <= a <= k-2
row 3a+4: D_a,  0 <= a <= k-2.
```

Dots are centers, and packet `i` occupies columns `3i+1..3i+3`. The
nonboundary centers are

```text
A_i = [2,3i] x {3i+1},       1 <= i <= k-1,
B_i = [3i+5,3k-1] x {3i+3},  0 <= i <= k-2,
x_a = (3a+2,3a+2),          0 <= a <= k-1.
```

The original boundary center set `M_F` is the perimeter minus

```text
{(0,1), (0,2), (1,3k+1), (3k+1,1), (3k+1,3k)}.
```

Its support is one tree. The interior's exact partition against that tree is

```text
{l,t_1},
{b_(a-1),t_(a+1)}       for 1 <= a <= k-2,
{b_(k-2),q,z},

t_i = (1,3i+1), b_i = (3k,3i+3),
l = (2,1), q = (3k-1,3k), z = (3k,3k-1).
```

These `k` separate interior trees have `2k+1` distinct contacts. The original
full center count is `T+2`, but its cycle rank is `k+1`. A permutation of
these same contacts among `k` nonempty interior blocks cannot fix a single
cap tree: the incidence rank remains `(2k+1)-k`. With all contacts retained,
a forest needs at least `k+2` contact-bearing cap components. This does not
rule out a cell rewrite that changes the number of interior blocks or the
contact set, rather than merely permuting the old matching.

## A Different Cap Class

Delete `x_(k-1)` and remove **all** centers in rows zero and one. Let the
remaining set be `J`. Explicitly,

```text
K = (M_F intersect {r >= 2}),
J = K union (union A_i) union (union B_i)
      union {x_a : 0 <= a <= k-2}.
```

The proposed replacement is

```text
F = J union Q,
Q any subset of {0,1} x [0,n-1].
```

Neither row of `Q` is fixed. In particular, next-ring centers can be added
in every column, and top boundary centers can be removed in every column.
The one deletion of `x_(k-1)` removes the right-end three-port issue before
asking about this different cap. It is not charged once per cell.

The original rows zero and one contain `n-2` and one centers respectively.
Consequently

```text
|J| = (T+2)-1-(n-1) = T-n+2.
```

### Complete Lower Partition

Write `N[S]` for the closed ambient radius-one neighborhood of a center set.
The full component partition of `H(J)` is

```text
one nontrivial block: S = N[J],
one singleton block {v} for each v outside S.
```

In particular the nontrivial block is a tree, not a collection of components
identified by a root label. Here is the coordinate attachment proof.

The support of `K` is a tree: its boundary edges form the path down the left
side, across the bottom, and up the right side, with endpoints `(1,0)` and
`(1,n-1)`. The bottom corner holes ensure that all inward edges are pendant,
as are the two upper endpoint edges. Every `B_i` meets this tree only at
`b_i`. These attachments therefore give one tree. The `A_i` trees are still
separate. The star of `x_0` meets the first tree at `l` and `A_1` at `(2,3)`.
For `1 <= a <= k-2`, the star of `x_a` meets precisely

```text
B_(a-1) at (3a+2,3a+1),
A_(a+1) at (3a+2,3a+3).
```

Thus each insertion joins the already attached B side to a previously
separate A tree, using two distinct vertices and no shared edges. Different
stars are disjoint. The rod-support separations are the same coordinate
inequalities as in the input interior proof. All rods and stars have now
joined exactly once; no other nontrivial component remains.

The entire intersection of `S` with the two-row cap vertex set is

```text
P = {(1,0), (1,2), (1,n-1)}
      union {(1,3i+1) : 1 <= i <= k-1},
p = |P| = k+2.
```

Only row-two centers can reach row one: they are exactly the two side
centers, `x_0`, and the tops of the A rods. No fixed center reaches row zero,
and no edge of `H(J)` lies wholly inside the two-row cap. The terminal
partition is the **single block `P`**. All other cap vertices are separate
ambient isolates before `Q` is inserted.

## Two-Row Obstruction

The following elementary lemma accounts for additions and holes jointly.

**Lemma.** Suppose a fixed tree outside a two-row ladder of length `n` meets
the ladder in exactly `p` vertices, with no shared ladder edges. If arbitrary
centers in that ladder extend it to a forest, the number `f` of ladder
centers satisfies

```text
f <= n+2-ceil(p/2).
```

Extra edges from ladder centers to vertices outside the ladder may be
ignored for this necessary bound. They cannot destroy a cycle in the
subgraph being counted.

**Proof.** Let `m_0,m_1` be the center counts in the two rows; let `R_0,R_1`
be their numbers of nonempty consecutive center runs; let `E_0,E_1` count
occupied row endpoints. Let `d` count columns occupied in both rows. The
number of forced horizontal edges in row `j` is exactly

```text
h_j = m_j + R_j - E_j.
```

This includes empty rows and fully occupied rows. The vertical forced-edge
count is `f-d`, so the total ladder edge count is

```text
e = 2f + R_0+R_1 - E_0-E_1 - d.
```

If a column has both centers, every neighboring column must have neither:
any center in such a neighboring column completes a forced unit square.
Hence every doubly occupied column gives a distinct singleton run in each
row, including at the ends. Thus `R_0+R_1 >= 2d`, while `E_0+E_1 <= 4`, and

```text
e >= 2f-4.
```

Contract the fixed tree. The ladder's `p` terminals become one vertex, so
the resulting multigraph has `2n-p+1` vertices. Contraction of a forest
cannot create a cycle, including loops or parallel-edge cycles. Regardless
of how many other components or isolates remain,

```text
e <= 2n-p.
```

Combining the two inequalities and using integrality proves the lemma.
This bound is not claimed sharp.

Apply the lemma to the actual tree `H(J)` on `S`, with `p=k+2`:

```text
|J union Q|
  <= T-n+2 + n+2-ceil((k+2)/2)
   = T+3-ceil(k/2).
```

The proof does not require the new cap to be connected, or every cap
component to meet `S`. Rootless cap components are permitted. Linear
numbers of additions in row one are permitted. Nevertheless their total
compensation for top-row holes is bounded by the ladder edge budget.

## Distributed-Edit Requirement

There is a useful extension that does not silently forbid changes below the
cap. Let

```text
F = (J minus D) union A union Q,
D subset J, |D|=h,
A subset ({r >= 2} minus J), |A|=a,
Q subset {0,1} x [0,n-1].
```

If `F` is feasible, so is `(J minus D) union Q`. Deleting `h` centers removes
at most `4h` edges from the original lower tree, keeping its vertices. The
partition of the original terminal set `P` therefore has at most
`s <= 1+4h` blocks, counting any newly isolated terminals separately.

Contract each of these lower components separately. There are now
`2n-p+s` cap vertices after contraction, so

```text
2|Q|-4 <= e <= 2n-p+s-1 <= 2n-p+4h.
|Q| <= n+2-ceil(p/2)+2h.
|F| <= T+3-ceil(k/2)+h+a.
```

In particular, reaching `|F| >= T-C` requires

```text
h+a >= ceil(k/2)-C-3.
```

This is a lower bound on the **number of edits below the two-row cap**, not
on their net center cost `h-a`. It explicitly allows `h,a=Theta(k)` and
`h-a=O(1)`. Such a distributed exchange, or editing the other boundary
sides and next-ring strips on that scale, is outside the no-go conclusion.
Adding centers alone never splits the inherited terminal block; deletions
must change its connections, and additions must pay for those deletions
without introducing replacement cycles. The inequality does not establish
that this can or cannot be done at bounded net cost.

## Bounded Experiments

Only `k=3,n=11` and `k=4,n=14` were materialized. The read-only input patterns
were `_RESIDUE_TWO_EXPLICIT[11]` and `[14]` in
`analysis/patterns/diagonal_patterns.py`. Their dots were interpreted as
centers; their historical labels of optimality were not used as evidence.

The temporary script `/tmp/opencode/moving_phase_cap_probe.py` performs a
full forced-graph check and an exact two-row cap dynamic program for `J`.
Its state retains the occupancy of the preceding column and the partition
of the fixed lower tree, upper frontier vertex, and lower frontier vertex.
Each of the four column masks is tried. All forced horizontal and vertical
ladder edges and actual attachments to the lower tree are inserted; a union
within an existing block is rejected as a cycle. Closed components are
allowed to disappear from the frontier, not rejected for being rootless.
Equal states retain the greatest center count. Reconstructed outputs are
checked again on the full ambient forced graph.

```text
k  n   |J|  p   maximum |Q|  |J union Q|  T   cached |F|
3  11   39  5       8            47      48      49
4  14   64  6      10            74      76      77
```

The maximizing caps returned have these center columns:

```text
n=11:
  row 0: {0,3,4,5,6,9,10}
  row 1: {0}
n=14:
  row 0: {0,3,4,5,6,9,10,11,12}
  row 1: {0}.
```

Both full graphs have cycle rank zero and one nontrivial component, with
all unused ambient vertices still counted as individual isolates. Their
lower terminal partitions are, respectively,

```text
{{(1,0),(1,2),(1,4),(1,7),(1,10)}}
{{(1,0),(1,2),(1,4),(1,7),(1,10),(1,13)}}.
```

The cached inputs both check as forests with one nontrivial component and
center counts 49 and 77. More importantly, after removing their centers in
rows zero and one, their lower nontrivial components expose the partitions

```text
n=11: {{(1,0)}, {(1,3)}, {(1,10)}}
n=14: {{(1,0)}, {(1,5)}, {(1,8)}, {(1,11)}}.
```

There are no additional lower nontrivial blocks in these two checks;
remaining vertices are isolates. These inputs do not merely rearrange the
moving strip's matched contacts: they keep the exposed lower components
separate before adding the top cap. This is the relevant distinction to
preserve in a future six-row interface rewrite. The two finite examples
supply neither a repeatable cell nor a uniform lower proof.

## Scope And Verification

The proved result is the arbitrary two-row cap bound and its distributed
edit requirement, with the lower component partition given in coordinates.
It is strictly more permissive than keeping the top boundary fixed while
testing a stripe or a bounded endpoint window, but strictly less permissive
than the unrestricted task. A simultaneous all-side cap/interior trade with
linear edits and bounded net cost remains open. So does a six-row cell
rewrite that creates separately closable components at target charge.

Only `docs/PAPER_MOVING_PHASE_CAP.md` was added in the repository. The
experiment script was created with `apply_patch` under `/tmp/opencode` and
run with `python3 -B`; it writes no repository artifacts. No Lean build,
large search, or experiment above side 14 was run. The uniform inequalities
are proved above, not extrapolated from the finite maxima. The companion
upper-bound paper supplies no lower witness and is not invoked here.
