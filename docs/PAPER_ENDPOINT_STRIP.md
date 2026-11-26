# Endpoint Free-Column Strip

Date: 2026-09-07. Paper proof, not a Lean theorem.

## Result and Scope

Let `N >= 1`. On the rectangular grid with columns `0,...,4` and rows
`0,...,N-1`, label each vertex F or U. Assume column 3 is entirely U and
column 4 is entirely F. Let `H` contain all vertices and exactly those grid
edges with at least one F endpoint. Suppose `H` is a forest. Write

```text
s = number of F vertices in columns 0 and 1;
t = number of F vertices in column 2.
```

Then the sharp uniform bound is

```text
s + t <= N + 2.
```

The constant 2 is attained for every positive `N = 1 mod 3`. This theorem
also applies when the rectangle is part of a larger actual forced forest:
restrict that forest to the rectangle first. External edges can exclude
configurations, not invalidate this upper bound. The sharpness construction
below is for the rectangle itself; no extension through an ambient boundary
is claimed.

An independent read-only review checked all 176 transition outcomes and the
potential inequalities: 70 transitions are accepted and 106 rejected. It
also checked initialization, forgetting, root connectivity, and sharpness.
This is a paper-certificate review, not Lean kernel verification.

This resolves the concrete strip inequality in the **Endpoint Free Column**
section of [Paper Packing Stability](PAPER_PACKING_STABILITY.md). Combined
with that section's displayed reduction `e <= s+t-N+2`, it gives `e <= 4`
in that endpoint-free-column saturated subcase. The separate
[zero-loss proof](PAPER_ZERO_LOSS_UPPER.md) now handles mixed saturated
tilings and gives a stronger bound, without using this strip theorem as a
black box. Positive packing loss and the general constant-gap bound remain open.

## Exact Root Reduction

Contract the full vertical rail in column 4 to a single vertex `R`. Every
column-3 vertex is joined to `R`. If `(2,y)` is U, the column-3 vertex in
row y is a leaf; delete it. If `(2,y)` is F, that column-3 vertex has degree
two; suppress it, replacing its two-edge path by an edge `(2,y)--R`.
There are no vertical edges in column 3.

The resulting graph `K` has `R` and the three vertices `(0,y),(1,y),(2,y)`
in each row. Put `m_y = (a_y,b_y,c_y)` for their F indicators. Its edges are
exactly:

```text
(0,y)--(1,y)       if a_y or b_y;
(1,y)--(2,y)       if b_y or c_y;
(2,y)--R           if c_y;
(i,y-1)--(i,y)     if m_(y-1)[i] or m_y[i], for i=0,1,2.
```

Here and below `or` is Boolean disjunction, not addition. These operations
preserve the presence or absence of cycles. In particular, `H` is a forest
if and only if `K` is a forest. One can also recover `H` by subdividing
root edges, adding the deleted leaves, and expanding `R` into the rail tree.

All edges in this reduction come from the actual forced graph. In
particular, an F vertex in column 1 also forces an edge to a U vertex in
column 2. Those edges must not be omitted. The root simultaneously retains
all connections through the rail, so the distinct-tooth-component constraint
is enforced jointly with the local spacing constraints. Neither an
independent estimate `s <= N` nor virtual UU edges are used.

## Frontier States

Process `K` in increasing row order, keeping `R` from the start. After row
y, the frontier consists of `(0,y),(1,y),(2,y),R`, in that order. A state
records the three-bit word `m_y` and the connectivity partition of these
four vertices in the entire processed graph. Components that have lost all
frontier vertices can be forgotten: no future edge can meet them.

Encode a partition by its restricted-growth string: label the first block
0, the next previously unseen block 1, and so on. Thus `0010` means that
the column-0 vertex, column-1 vertex, and root are connected, and the
column-2 vertex is in another component. `0123` means all four are separate.

Here is a precise transition rule, also giving a direct way to check every
entry of the table below. Given old state `(m,p)` and new word `n`, take
symbols `o0,o1,o2,R,v0,v1,v2`. Initially the old symbols and `R` have the
equivalence relation specified by `p`; each new symbol is separate. Insert
the following edges, in the displayed order:

```text
oi--vi, i=0,1,2, if m[i] or n[i];
v0--v1           if n[0] or n[1];
v1--v2           if n[1] or n[2];
v2--R            if n[2].
```

For each inserted edge, reject the transition if its endpoints are already
equivalent; otherwise merge their classes. After all insertions, restrict
the equivalence relation to `v0,v1,v2,R` and canonically relabel it. This
is the new partition, and the new word is `n`.

The rule is exact: starting with a forest, an edge creates a cycle exactly
when its endpoints are already connected. Old equivalences encode existing
paths, not extra edges to be inserted. This also detects two distinct new
attachments to the same old tree. Forgetting the old vertices after the
test preserves precisely the information needed at the next step.

For the first row, use separate symbols `v0,v1,v2,R`, insert only the last
three kinds of edges, and form the partition. In word order
`000,001,010,011,100,101,110,111`, the initial state IDs are

```text
8, 10, 12, 13, 17, 18, 20, 21.
```

## Complete Certificate

The following 22 states contain every initial state and are closed under
every nonrejected transition. The eight successor columns are in the same
word order as above. A dash means rejection by the exact cycle test, not
an omitted or unexamined successor. `P` is the potential.

```text
ID  word  partition  P | 000 001 010 011 100 101 110 111
 0  000   0000       1 |   8   -  11   -  15   -   -   -
 1  000   0010       0 |   8  10  11   -  15   -   -   -
 2  000   0012       0 |   8  10  12  13  17  18   -   -
 3  000   0100       0 |   8   -  12   -  15   -  19   -
 4  000   0111       0 |   8   -  11   -  17   -  19   -
 5  000   0120       0 |   8  10  12  13  15   -  19   -
 6  000   0121       0 |   8  10  11   -  17  18  19   -
 7  000   0122       0 |   8   -  12   -  17   -  20   -
 8  000   0123       0 |   8  10  12  13  17  18  20  21
 9  001   0000       1 |   7   -   -   -  14   -   -   -
10  001   0111       0 |   7   -   -   -  16   -   -   -
11  010   0000       1 |   6   -  11   -   -   -   -   -
12  010   0001       0 |   8   -  12   -   -   -   -   -
13  011   0000       1 |   4   -   -   -   -   -   -   -
14  100   0000       1 |   5   -   -   -  15   -   -   -
15  100   0010       1 |   5   9   -   -  15   -   -   -
16  100   0011       0 |   8   -   -   -  17   -   -   -
17  100   0012       0 |   8  10   -   -  17  18   -   -
18  101   0000       1 |   3   -   -   -  14   -   -   -
19  110   0000       1 |   1   -   -   -   -   -   -   -
20  110   0001       1 |   2   -   -   -   -   -   -   -
21  111   0000       2 |   0   -   -   -   -   -   -   -
```

For illustration, state 15 has word `100` and partition `0010`. Appending
`001` first attaches `v0` to `o0` and `v2` to `o2`, then inserts `v1--v2`
and `v2--R`. This joins all four new frontier vertices without a cycle,
giving state 9. In contrast, appending `101` also inserts `v0--v1`;
the final root edge then closes a cycle and the transition is rejected.
This is a connectivity obstruction, not just a forbidden adjacent-word pair.

Let `|n|` be the number of ones in the new word and set `w(n)=|n|-1`.
The full certificate consists of the displayed states, transition rule,
initial IDs, and these two inequalities:

```text
w(m) <= P(initial(m));
P(i) + w(n) <= P(j) whenever the table has i --n--> j.
```

They are verified directly as follows. For the initial states, the weights
are `-1,0,0,1,0,1,1,2`, and their potentials are
`0,0,0,1,0,1,1,2`. For every table column labeled `000`, the target potential
is at least the source potential minus 1. For columns `001,010,100`, it
is at least the source potential. For columns `011,101,110`, it is at least
the source potential plus 1. The only `111` transition is `8 -> 21`, with
potentials 0 and 2. These checks cover every nonrejected entry.

Consequently the precise induction invariant, after any positive number h
of rows, is

```text
sum_(y=0)^(h-1) (|m_y|-1) <= P(current state).
```

The first inequality initializes it, and the second preserves it. Every
forest word sequence remains in the table by the exact transition rule and
closure. Finally every listed potential is at most 2, so at `h=N` the
invariant reads `s+t-N <= 2`, proving the theorem for all heights.

This is a finite local proof, not an extrapolation from small boards. The
table can be checked using only equivalence relations on seven symbols;
no unknown reachable states or asymptotic search claims enter the proof.
As an independent arithmetic check during preparation, a temporary script
outside the repository generated and checked all 176 state/word transition
attempts and the potential inequalities. It used a hard cap of 120 states
and 960 transition attempts, with at most 15 row levels for discovery;
closure was obtained at level 4 and potential stabilization took five
rounds. No board enumeration, large optimization, or Lean build was used.
The explicit certificate above, rather than that script or a finite-height
maximum, is the basis for the uniform conclusion.

The literal five-column sharpness examples were additionally checked at
heights 1, 4, 7, 10, and 13, with a hard height cap of 15 and vertex cap of
75. Each had exactly `5N-1` edges and no cycle. These are only sanity checks;
the following construction argument proves sharpness at arbitrary height
in the stated residue class.

## Sharpness

For `N=3q+1`, `q>=0`, prescribe the first three columns by

```text
m_y = 111  when y = 0 mod 3;
m_y = 000  otherwise.
```

Keep column 3 U and column 4 F as in the theorem. In `K`, each occupied row
is the path `(0,y)--(1,y)--(2,y)--R`. Each available adjacent empty row
contributes three leaves, one at each of that occupied row's three vertices.
Different occupied rows have disjoint adjacent-row sets: their row distance
is three. There are no horizontal edges on an empty row, and no vertical
edges between consecutive empty rows. Thus these branches meet only at
`R`, once per occupied row, and `K` is a tree. In this height residue every
vertex belongs to one of the branches or is `R`. Undoing the root reduction
shows that the full five-column `H` is also a tree.

There are `q+1` occupied rows, hence

```text
s = 2(q+1),  t = q+1,  s+t = 3q+3 = N+2.
```

The teeth are three-spaced, their neighboring column-1 positions are U,
and their ports lie in distinct actual two-column-strip components.
In the certificate the repeated pattern follows
`21 -> 0 -> 8 -> 21`, with potentials `2,1,0,2` and row increments
`-1,-1,2`. This displays exactly how the component/spacing cost and the
tooth reward balance, including the sharp endpoint allowance of 2.
