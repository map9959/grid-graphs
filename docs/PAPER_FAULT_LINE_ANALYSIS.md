# Fault-Line Analysis

Date: 2026-09-07. Independent paper analysis, not a Lean theorem or an
independently reviewed certificate. Only the bounded sanity checks described
below were run. No formal build was run.

## Results And Limits

There are two completed results here:

1. A physical five-column strip, with column 3 U and every other column
   arbitrary, satisfies `TOTAL_F <= 2H+2` at every positive height `H`.
   A complete 58-state certificate below proves this. In the specified
   square-board family it strengthens the initial interruption estimate
   `e <= 4+2Lambda` to `e<=4`, independently of the number of interruptions.
2. An actual forced-forest family with `Lambda=2` disproves fixed-phase
   stability by `O(Lambda)` row or vertex deletion. A separate loss-three
   family realizes a persistent residue-one horizontal fault line.

Neither family has unbounded positive excess. Neither disproves a uniform
upper bound on `e`. The strip result does not prove that bound for arbitrary
small positive loss, or for intermediate loss. In particular, the false
fixed-phase statement refuted below is a possible strengthening of stability,
not a theorem asserted in the existing stability note.

Notation is that of [zero loss](PAPER_ZERO_LOSS_UPPER.md): `Q=k-1`,
`N=3Q+1`, `n=3Q+5`, deep row `y` means physical row `Y=y+1`, and
`T=3Q^2+13Q+10`. All unspecified vertices in the explicit constructions are
holes. All graph claims concern every physical grid edge with an F endpoint.

## What Propagation Actually Localizes

Let

```text
D = union over valid omitted steps of (E_y minus E_sigma(y)).
```

The fourth-step inequality gives `|D|<=3Lambda`. Every column occurring on
a good residue-one row belongs to `D`: follow that column forward in its
residue-one chain until its first disappearance, at latest at the invalid
good row `N`. Thus

```text
|union_(y=1 mod 3) E_y| <= 3Lambda.
```

Outside `D`, residue-zero horizontal edge sets nest forward, residue-two
sets nest backward, and residue-one sets vanish. This is a statement about
edge-left columns, not vertex columns; taking endpoints can enlarge the
exceptional set to `D union (D+1)`.

The argument charges a disappearance once, not all previous occurrences of
its column. It neither bounds the number of affected rows nor proves that
vertical phases outside those columns stay fixed. The loss-two example
below has `D=empty` and still changes vertical phase.

## Interrupted Physical Strip

The following initial bound is retained for comparison. The stronger
variable-rail certificate below removes its interruption penalty.

Consider columns `0,...,4` and `H` rows. Column 3 is entirely U. Column 4
is F except at `h` rows. Let `b` be the number of nonempty maximal F runs
in column 4, and let `S` count F vertices in columns 0, 1, and 2. Assume
the actual forced graph on this rectangle is a forest. Then

```text
S <= H + 2h + 2b.                                  (1)
```

Proof: restrict to each of the `b` full-rail row intervals. Restriction is
a literal subforest, and the [22-state strip certificate](PAPER_ENDPOINT_STRIP.md)
applies, giving at most `length+2` F vertices in the first three columns.
The remaining `h` rows contribute at most `3h`. Summing gives
`(H-h)+2b+3h`, as claimed. For `b=0` this is just `S<=3H`.

Write `g` for the number of absent FF edges of column 4 relative to a full
rail, including its end effects. Counting edges within its actual F runs,

```text
g = (H-1) - ((H-h)-b) = h+b-1.
```

This identity also holds when the rail is empty: then `h=H,b=0,g=H-1`.
Consequently (1) is equivalently

```text
S <= H + 2g + 2.                                   (2)
```

In particular, an arbitrarily long surviving rail segment costs only its
endpoint potential allowance, not its length. The coefficient two here
comes from the range of the physical 22-state potential. No virtual mirror
edges or scalar carrier labels are introduced.

### Attachment To Actual Components

These bounds remain valid inside any larger forced forest, even if distinct
rail runs are connected outside the rectangle. One may simply discard all
external edges before applying (1); discarding constraints cannot increase
the mass of the given pattern.

If external connectivity is retained for a sharper certificate, retain the
actual external component partition on all exposed ports. Contract those
external trees, insert each physical strip edge, and reject an insertion
whose endpoints are already connected. This is the ordinary forest cycle
test, not permission to insert an edge for a merely nominal contact.
Two attachments to one external tree can therefore reject a pattern that
the restricted strip would accept, never the reverse.

This observation proves that (1) is safe under gluing; it does NOT say that
the original 22 states suffice for arbitrarily many external ports. Their
single permanent root describes one rail tree. Several simultaneous roots
or external ports require more connectivity information. Nor may separate
strip certificates count the same F vertex twice in a global mass sum.

## Variable-Rail Constant Bound

**Theorem.** For every `H>=1`, label the vertices of the rectangle with
columns `0,...,4` and rows `0,...,H-1` by F or U. Require column 3 to be
entirely U; all other labels are arbitrary. If the actual forced graph is
a forest, then

```text
TOTAL_F <= 2H+2.                                   (4)
```

There is no persistent-rail assumption, and no limit on how often column 4
changes label. The constant is sharp for every `H=1 mod 3`. This is a
finite-state paper certificate, computationally checked as described below,
not an independently reviewed or kernel-verified theorem.

### Exact Physical Reduction

Column 3 has no vertical forced edges. In each row its vertex has degree
two precisely when both columns 2 and 4 are F. Suppress it in that case,
giving a single edge from column 2 to column 4. With just one of those
endpoints F it is a leaf and can be deleted; with neither it is isolated
and can be deleted. These operations preserve the presence of cycles.

The reduced graph keeps all vertices in columns `0,1,2,4`, including U
vertices. Write their row word as `m=(a,b,c,d)` in that order. The within-row
edges are exactly

```text
0--1 if a or b;
1--2 if b or c;
2--4 if c and d.
```

Between successive rows, at each of the four retained columns an edge is
present if either endpoint is F. In particular U vertices in column 4
cannot be forgotten early: they may connect consecutive F rail pieces.
Column 4 is NOT contracted to a root. This reduction counts all preserved
vertices without change, since the removed column contains only holes.

### State And Transition Rule

A frontier state is `(m,p)`, where `m` is its four-bit row word and `p`
is the restricted-growth string encoding the connectivity partition of
the four current vertices in the entire processed reduced graph. For
example `0010` connects columns 0, 1, and 4, leaving column 2 separate.
All four U/F vertices remain in the frontier. Forgotten components have
no possible future incident edge and need not be retained.

To append word `n`, start with old symbols `o0,o1,o2,o4` partitioned by
`p` and four separate new symbols `v0,v1,v2,v4`. The old equivalences
describe paths, not edges to insert. Insert in order:

```text
oi--vi, i=0,1,2,4, if the old or new bit at i is 1;
v0--v1 if n[0] or n[1];
v1--v2 if n[1] or n[2];
v2--v4 if n[2] and n[3].
```

Reject when an inserted edge has already-connected endpoints; otherwise
merge its endpoint classes. After all insertions restrict to the four new
vertices and canonically relabel. This produces the next state. For the
first row, start with four separate vertices and insert only within-row
edges. This is exact forest recognition: every accepted insertion joins
two trees, while every rejected insertion closes a physical cycle after
undoing the column-3 suppression.

### Complete Certificate

The successor columns in the table are the 16 new words in binary order:

```text
0000 0001 0010 0011 0100 0101 0110 0111
1000 1001 1010 1011 1100 1101 1110 1111
```

The initial state IDs in this same order are

```text
11 23 28 30 32 34 36 37 42 47 49 50 52 54 56 57.
```

Every table entry follows the transition rule above; a dash is a cycle
rejection. The table includes every initial state and is closed under
every accepted transition. `P` is the potential.

```text
ID word part P | successors in binary word order
 0 0000 0000 0 | 11 23 28  - 32 33  -  - 42 45  -  -  -  -  -  -
 1 0000 0001 0 | 11 23 28 30 32 34  -  - 42 47  -  -  -  -  -  -
 2 0000 0010 0 | 11 23 28 30 32 33 36  - 42 45 49  -  -  -  -  -
 3 0000 0012 0 | 11 23 28 30 32 34 36 37 42 47 49 50  -  -  -  -
 4 0000 0100 0 | 11 23 28  - 32 34 36  - 42 45  -  - 52 53  -  -
 5 0000 0102 0 | 11 23 28 30 32 34 36 37 42 47  -  - 52 54  -  -
 6 0000 0111 0 | 11 23 28  - 32 33  -  - 42 47 49  - 52 53  -  -
 7 0000 0112 0 | 11 23 28 30 32 34  -  - 42 47 49 50 52 54  -  -
 8 0000 0120 0 | 11 23 28 30 32 34 36 37 42 45 49  - 52 53 56  -
 9 0000 0121 0 | 11 23 28 30 32 33 36  - 42 47 49 50 52 53 56  -
10 0000 0122 0 | 11 23 28  - 32 34 36  - 42 47 49  - 52 54 56  -
11 0000 0123 0 | 11 23 28 30 32 34 36 37 42 47 49 50 52 54 56 57
12 0001 0000 1 | 11 23 27  - 31 33  -  - 40 45  -  -  -  -  -  -
13 0001 0001 0 | 11 23 28 30 32 34  -  - 42 47  -  -  -  -  -  -
14 0001 0010 0 | 11 23 28 30 31 33 35  - 40 45 48  -  -  -  -  -
15 0001 0012 0 | 11 23 28 30 32 34 36 37 42 47 49 50  -  -  -  -
16 0001 0100 0 | 11 23 27  - 32 34 35  - 40 45  -  - 51 53  -  -
17 0001 0102 0 | 11 23 28 30 32 34 36 37 42 47  -  - 52 54  -  -
18 0001 0111 0 | 11 23 27  - 31 33  -  - 42 47 48  - 51 53  -  -
19 0001 0112 0 | 11 23 28 30 32 34  -  - 42 47 49 50 52 54  -  -
20 0001 0120 0 | 11 23 28 30 32 34 36 37 40 45 48  - 51 53 55  -
21 0001 0121 0 | 11 23 28 30 31 33 35  - 42 47 49 50 51 53 55  -
22 0001 0122 0 | 11 23 27  - 32 34 35  - 42 47 48  - 52 54 55  -
23 0001 0123 0 | 11 23 28 30 32 34 36 37 42 47 49 50 52 54 56 57
24 0010 0000 0 | 11 22 28  -  -  -  -  - 39 43  -  -  -  -  -  -
25 0010 0001 0 | 11 23 28 30  -  -  -  - 39 44  -  -  -  -  -  -
26 0010 0110 0 | 11 23 28 30  -  -  -  - 42 45 49  -  -  -  -  -
27 0010 0111 0 | 11 22 28  -  -  -  -  - 42 46 49  -  -  -  -  -
28 0010 0112 0 | 11 23 28 30  -  -  -  - 42 47 49 50  -  -  -  -
29 0011 0000 1 | 10 22 27  -  -  -  -  - 38 43  -  -  -  -  -  -
30 0011 0111 0 | 10 22 27  -  -  -  -  - 41 46 48  -  -  -  -  -
31 0100 0000 0 | 11 21  -  - 32 33  -  -  -  -  -  -  -  -  -  -
32 0100 0001 0 | 11 23  -  - 32 34  -  -  -  -  -  -  -  -  -  -
33 0101 0000 1 |  9 21  -  - 31 33  -  -  -  -  -  -  -  -  -  -
34 0101 0001 0 | 11 23  -  - 32 34  -  -  -  -  -  -  -  -  -  -
35 0110 0000 0 |  7 18  -  -  -  -  -  -  -  -  -  -  -  -  -  -
36 0110 0001 0 |  7 19  -  -  -  -  -  -  -  -  -  -  -  -  -  -
37 0111 0000 1 |  6 18  -  -  -  -  -  -  -  -  -  -  -  -  -  -
38 1000 0000 0 | 11 20 25  -  -  -  -  - 42 45  -  -  -  -  -  -
39 1000 0001 0 | 11 23 25 29  -  -  -  - 42 47  -  -  -  -  -  -
40 1000 0010 0 | 11 20 28 29  -  -  -  - 42 45 49  -  -  -  -  -
41 1000 0011 0 | 11 23 28  -  -  -  -  - 42 47 49  -  -  -  -  -
42 1000 0012 0 | 11 23 28 30  -  -  -  - 42 47 49 50  -  -  -  -
43 1001 0000 1 |  8 20 24  -  -  -  -  - 40 45  -  -  -  -  -  -
44 1001 0001 0 | 11 23 25 29  -  -  -  - 42 47  -  -  -  -  -  -
45 1001 0010 1 |  8 20 26 29  -  -  -  - 40 45 48  -  -  -  -  -
46 1001 0011 0 | 11 23 27  -  -  -  -  - 42 47 48  -  -  -  -  -
47 1001 0012 0 | 11 23 28 30  -  -  -  - 42 47 49 50  -  -  -  -
48 1010 0000 1 |  5 16 25  -  -  -  -  - 39 43  -  -  -  -  -  -
49 1010 0001 0 |  5 17 25 29  -  -  -  - 39 44  -  -  -  -  -  -
50 1011 0000 1 |  4 16 24  -  -  -  -  - 38 43  -  -  -  -  -  -
51 1100 0000 0 |  3 14  -  -  -  -  -  -  -  -  -  -  -  -  -  -
52 1100 0001 0 |  3 15  -  -  -  -  -  -  -  -  -  -  -  -  -  -
53 1101 0000 1 |  2 14  -  -  -  -  -  -  -  -  -  -  -  -  -  -
54 1101 0001 1 |  3 15  -  -  -  -  -  -  -  -  -  -  -  -  -  -
55 1110 0000 1 |  1 12  -  -  -  -  -  -  -  -  -  -  -  -  -  -
56 1110 0001 1 |  1 13  -  -  -  -  -  -  -  -  -  -  -  -  -  -
57 1111 0000 2 |  0 12  -  -  -  -  -  -  -  -  -  -  -  -  -  -
```

Let `w(n)=|n|-2`. The certificate inequalities are

```text
w(m) <= P(initial(m));
P(i)+w(n) <= P(j) for every accepted i --n--> j.     (5)
```

Here is a short exhaustive potential check, separated from checking the
connectivity transitions themselves:

- For zero-bit words, `w=-2`; (5) follows from `0<=P<=2`.
- For one-bit words, `w=-1`; only source 57 has potential two, and its
  only accepted one-bit successor is `57 --0001--> 12`, with potential one.
- For two-bit words, `w=0`. A source of potential zero needs no check.
  The complete list of accepted two-bit transitions from positive-potential
  sources is `12->33,45; 29->43; 33->33; 43->45; 45->29,45,48;
  48->43; 50->43`. Every target has potential one. Source 57 accepts none.
- For three-bit words, `w=1`. Every accepted source has potential zero,
  and every three-bit target has potential one, as the table records.
- The four-bit word is accepted only from states 11 and 23, both of
  potential zero, and goes to state 57 with potential two.

Initialization follows directly: words with at most two bits have
nonpositive weight, three-bit initial states have potential one, and the
four-bit initial state has potential two. Induction using (5) gives

```text
sum_(y=0)^(H-1) (|m_y|-2) <= P(state after H rows) <= 2.
```

The sum is `TOTAL_F-2H`. This proves (4) for every height, not merely the
heights used to discover the closed state set.

For sharpness keep column 4 F and use word `1111` on rows zero modulo
three, `0001` on the other rows. This is the actual full-rail sharpness
construction from the endpoint-strip proof: separate bar branches meet
the rail once each. For `H=3q+1` it has `H+3(q+1)=2H+2` F vertices.
The certificate follows `57->12->23->57`, with potentials `2,1,0,2`
and appended weights `-1,-1,2`.

### Constant Under Physical Gluing

External physical connections only restrict accepted strip patterns, so
(4) holds for every such rectangle inside a larger forced forest. It does
not require distinct rail runs to remain globally disconnected. If external
ports are tracked, the appropriate external connectivity partition must
still be retained; the 58 states alone describe the restricted strip.

In the earlier notation `TOTAL_F=S+(H-h)`. Thus the stronger bound is

```text
S <= H+h+2.                                        (6)
```

Every removed rail vertex pays for at most one additional F vertex in the
other columns, apart from the single endpoint allowance two. There is no
per-run potential reset in (6), even when `g` or `b` is large.

## Square-Board Consequence

Here is a precise positive-loss family to which the strip proof applies.
Within the deep square assume:

- Columns `7,10,...,3Q+1` are full vertical F rails.
- Column 4 is F except at `h` rows, with `b` nonempty F runs.
- Column 2 is arbitrary; let `t` count its F vertices.
- Every other deep vertex is U.

The annulus is arbitrary subject to the full forced graph being a forest.
Let `s` count its F vertices in physical columns 0 and 1 on the deep row
interval. The initial bound (2) gives `s+t<=N+2g+2`; the stronger
variable-rail bound (6) gives `s+t<=N+h+2`.

There are no horizontal deep FF edges. The only good vertical edges are
those on the specified rails. Edges on column 2, if present, are bad, not
good. Therefore, without deleting any such edges from the actual graph,

```text
GOOD = 3Q(Q-1) + (N-h-b),
Lambda = h+b-1 = g,
Z = QN-h+t.
```

Each other two-column annulus side strip has at most `N` preserved vertices,
and the four corner blocks together have at most eight, by the physical
side-strip bound used in the endpoint-free-column reduction. These regions
and the selected side strip are disjoint. Hence

```text
F_A <= s+3N+8,
e <= s+t-N+2-h
  <= 4+2Lambda-h
  <= 4+2Lambda.                                    (3)
```

The stronger certificate replaces the last two estimates by

```text
e <= s+t-N+2-h <= (N+h+2)-N+2-h = 4.               (7)
```

This includes the empty-rail case and all intermediate values of `Lambda`
permitted by this family. No subdivision into full-rail runs, and hence no
per-run allowance, is needed. Equation (7) makes no claim that every narrow
fault line admits this geometry: in particular column 3 must remain U and
all deep vertices outside columns 2, 4 and the other prescribed rails must
remain U. The loss-two phase-switch construction below uses column 3 F
on its upper segment and is not a member of this family.

## Loss Two Changes Phase

Take `Q>=2` and `2<=j<=N-3`. Preserve exactly

```text
(x,y+1), x in {7,10,...,3Q+1}, 1<=y<=N;
(3,y+1), 1<=y<=j;
(4,y+1), j+2<=y<=N.
```

These are `Q-1` full rails and two partial rails separated by an empty
row. Every pair of distinct preserved intervals has grid distance at least
three. In particular the two partial-rail endpoints have distance three,
not two. Each individual interval forces a path with pendant neighbors;
distinct intervals have disjoint closed distance-one neighborhoods. Thus
the full forced graph is a disjoint union of these trees and isolates.
There is no omitted cross-edge: a forced edge has a preserved endpoint and
so belongs to one of those neighborhoods.

All FF edges are good, and direct counting gives

```text
GOOD = 3Q(Q-1)+(j-1)+(N-j-2) = 3Q^2-2,
Lambda=2,
f=QN-1,
e=-12Q-11.
```

Above the empty row the saturated axis set is `P_1`; below it the set is
`P_0`, in the zero-loss notation. The two deficient steps each lose one
vertical edge. The transition location can be in the middle of a board of
arbitrary height.

Here is the exact stability statement this refutes:

> After deleting at most `C Lambda` deep rows (or preserved vertices), every
> vertically oriented pattern agrees with one fixed saturated axis phase
> on all remaining rows (or has all remaining F vertices on that phase).

Every saturated phase has either column 3 or column 4 as its first axis,
never both. A phase lacking 3 disagrees on all `j` upper rows; a phase
lacking 4 disagrees on all `N-j-1` lower rows. The deletion requirement is
at least `min(j,N-j-1)`, which is unbounded for central `j`, while loss is
two. This uses distinct actual physical patterns, not solutions of the
scalar packing equations.

Allowing a bounded number of interfaces rather than a single global phase
avoids this counterexample. So does measuring the interface cost rather
than the number of rows on which the new phase persists. A full stability
proof should allow exactly this distinction.

For comparison, deleting the first vertex of column 4 from the full phase
`P_0` gives a feasible loss-one pattern. Here `h=1,b=1`, and (7) applies.
It provides
no analogous macroscopic phase switch and no evidence for amplification.
No classification of all loss-one or loss-two patterns is claimed.

## A Persistent Residue-One Family

Take the same `Q-1` full rails at `7,10,...,3Q+1`, and preserve instead the
horizontal bars

```text
x=2,3,4,5 at deep rows y=4,7,...,3Q-2.
```

There are `Q-1` bars, each with three good horizontal edges. Hence

```text
GOOD=3Q(Q-1)+3(Q-1)=3Q^2-3,
Lambda=3,
f=(Q-1)(N+4)=3Q^2+2Q-5,
e=-11Q-15.
```

Each bar's closed neighborhood meets the column-7 rail neighborhood only
at the intervening hole `(6,y+1)`. Different bars are three rows apart and
have disjoint closed neighborhoods. Attaching each bar tree to that rail
tree at its single common vertex preserves acyclicity. All other rails
have disjoint neighborhoods; the remaining vertices are isolates. This
proves feasibility in the full square, including the annulus, which is U.

The three edge-left columns `{2,3,4}` persist on `Theta(Q)` residue-one
rows. There are only three forward termination events, at the last bar.
For fixed column 2, for example, the number of row occurrences is `Q-1`,
not `O(Lambda)` uniformly over this family. Charging every occurrence to
its final termination is invalid.

The bars have only one internal rail contact. Their outward contacts go
to distinct isolated vertices of the all-U annulus. This is why they are
feasible. If two of these bars instead had two disjoint physical contacts
to the same pair of persistent rails, their union with the rail segments
would contain a cycle. If their boundary contacts were connected in the
annulus, two bars and that annulus path would likewise close a cycle with
the persistent rail. Actual component identities, not contact counts alone,
decide these obstructions.

## Verification And Remaining Gap

A temporary script, `/tmp/opencode/fault_line_check.py`, constructed the
loss-two and loss-three patterns at `Q=2,3`, on sides 11 and 14. It inserted
every physical forced edge into union-find and rejected cycles, then
counted good and bad FF edges independently. All four cases were forests;
the respective good counts were `10,25` and `9,24`, with no bad edges.
The largest coordinate was 13. No board with side greater than 15 was
generated. The script was run with `python3`; `python` was unavailable.
These checks supplement, rather than replace, the symbolic proofs above.

A second temporary script, `/tmp/opencode/interrupted_strip_certificate.py`,
generated the variable-rail states using only the four-vertex connectivity
transition. It enforced a discovery-depth cap of 15, a state cap of 256,
and a cap of 4096 state/word transition attempts. Closure occurred at depth
four with 58 states and 928 attempts: 433 accepted and 495 rejected. The
max-weight potential relaxation stabilized after five rounds. Replacing
its negative potentials by zero and checking every inequality yielded
exactly the displayed `P` with range `0,...,2`.

For every state a representative word history of height at most four was
retained. All 928 one-row extensions were checked separately by constructing
the original five-column graph and inserting every physical forced edge.
The literal cycle verdict matched the reduced transition verdict in every
case; these rectangles had height at most five. This is a cross-check of
the reduction, not an additional assumption about unreachable histories.

Dynamic programming on the closed graph also found the maxima for heights
1 through 15. They were

```text
H:       1  2  3  4  5  6  7  8  9 10 11 12 13 14 15
TOTAL_F: 4  5  7 10 11 13 16 17 19 22 23 25 28 29 31.
```

One maximizing literal strip at each height was checked for forced
acyclicity and count. No literal height exceeded 15 and no coordinate
exceeded 14. These finite maxima are sanity checks only. The closed table,
exact transition rule, and potential induction prove the arbitrary-height
result, including heights never materialized by the script.

For general fault lines the missing step remains substantial: construct a
disjoint physical decomposition whose interfaces, external ports, bad
edges, and unassigned components are paid from the exact global ledger.
Within the five-column geometry, interruptions themselves no longer need
a loss-proportional charge. The `3Lambda` edge-column localization alone
does not provide a decomposition into such strips.
Even an `O(Lambda)` error in the zero-loss contact argument would not by
itself imply a uniform constant for intermediate loss without checking its
coefficient against the loss already present in that ledger.

Thus the strongest new upper results are the unrestricted variable-rail
strip theorem (4) and `e<=4` in (7) for the explicitly prescribed square
family. The counterexample is to single-phase deletion stability, not to
constant excess. Arbitrary positive-loss constant-gap stability remains
unresolved by this analysis.
