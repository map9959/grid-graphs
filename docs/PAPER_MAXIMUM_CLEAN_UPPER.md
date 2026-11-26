# Maximum Clean Upper Research

Date: 2026-09-08. Paper results and precise obstructions; no optimization
or Lean work. This note does not prove an unconditional constant-gap bound.

## Outcome

Current review status: independent read-only audits covered the full note
through Pendant Translation Continuation (original line 618), with no
mathematical findings. Historical unaudited labels refer to earlier
snapshots. The maximum-specific translation alternative is proved, but it
does not force boundary exposure or an unconditional constant upper bound.

For `n=3k+2`, `k>=3`, put `T=3k^2+7k`. The requested implication
`P(n)<=T+O(1)` remains unproved. In particular, no count-preserving,
cycle-safe replacement forcing a paid clean normal form has been obtained.
There is no counterexample to that implication here.

The new results below are an arbitrary-batch obstruction to inward boundary
promotion, an exact physical path-cut formulation of replacement safety,
and a redundancy in the proposed carrier-span tie-break. These specify
what a maximum-specific argument still has to prove; they do not replace
maximum cardinality by inclusion maximality.

Inputs read: [half-coefficient](PAPER_HALF_COEFFICIENT_UPPER.md), the complete
[global-cap note](PAPER_GLOBAL_CAP_PAYMENT.md) including its corrected
flat-packet hypothesis, the final refined certificate in
[isolate routing](PAPER_ISOLATE_ROUTING_UPPER.md), and the
[projection exchange criterion](PAPER_PROJECTION_UPPER_RESEARCH.md).
All statements below allow disconnected forced forests, globally isolated
holes, arbitrary pure-carrier counts, and mixed carrier orientations.

## Objective And Certificate

Let `H(F)` contain precisely the grid edges with at least one endpoint in
`F`. Feasibility means that this actual graph is a forest. Write `f=|F|`,
`r` for the number of induced preserved carriers, `c` for all components
of `H(F)`, and `b` for the boundary deficiency of the holes. Here

```text
K=r+b+c,
3f+K=n^2+4n,
3(f-T)=n+10-K.                                      (1)
```

This `K` is NOT the two-layer loss called K in the half-coefficient note.
Maximum f is minimum K. Every cardinality-neutral feasible replacement
leaves K exactly unchanged, regardless of its changes to r, b, or c.

For precision, the final isolate certificate uses `A=n-1`, `z` actual
isolates, and the following already allocated resources:

```text
B_C=3(c-z-1)+t_0+3delta/2+C_C,
D_port=sum_clean through (max(5-k_s,0)/2-e_s),
L_*=g_+-j_C-nu_D-nu_N,
X_2<=A L_*,
S>=3L_*+1+B_C+nu_N+sigma_D-D_port+3j_C,
K=S+4-3C_o/4>=S+1.                                 (2)
```

Here `e_s` is the protected endpoint-slot payment, `j_C` counts a valid
endpoint-disjoint system of ordered clean joins, and `nu_D,nu_N,sigma_D`
are the dirty matching, isolate-allocation joins, and retained dirty
matching surplus of that note. In particular arbitrary donated V/T
resources are not available again. Empty F needs no certificate.

One can explicitly retain the unused chain length. Set

```text
Delta_*=A L_*-X_2>=0,
D_met=max(0,D_port-B_C-nu_N-sigma_D-3j_C-3Delta_*/A).
```

Subtract `3Delta_*/A` in (2) and use `K>=S+1`. This proves

```text
3X_2/A<=K-2+D_met,
3(f-T)<19+D_met.                                   (3)
```

The last implication is the source's area conversion, using the unchanged
`A^2=3X_2+Q_exc` and `Q_exc<=10K`. It permits a real nonnegative debt.
Thus `D_met=0` gives `f<=T+6`, not the sharp bound `f<=T`.

A legitimate maximum-normalization theorem could show that some maximum
admits (2) with `D_met<=D_0` for an absolute constant. Equation (3) would
then give `P(n)<=T+ceil((19+D_0)/3)-1`. Neither this existence theorem nor
even its all-one-pair eligible specialization is proved here. Alternatively,
`K<n-d` could imply an actual cardinality-increasing feasible replacement.
Either route needs new geometry, not a rearrangement of (1).

## Span Tie-Break Redundancy

Every preserved carrier is a filled straight interval. If its edge-length
span is `ell-1`, summing over carriers gives exactly

```text
total carrier span=f-r.                             (4)
```

Consequently, among equal-cardinality sets, minimizing r already maximizes
total carrier span. A subsequent maximization of that span breaks no ties.
Using vertex-length spans gives the constant f instead. This observation
does not concern the spans of entire forced components, which include
holes and branches and are different quantities.

One can choose, for example, a lexicographically extremal maximum using
`(r,-sum_carriers ell^2)` and a final fixed vertex ordering. Such a choice
exists by finiteness. But its only new consequence is that no feasible
neutral replacement improves this tuple. To deduce a normal form one must
prove that every unpaid configuration has just such a replacement. Neither
finiteness nor the existence of a tie-break proves the replacement.

## A Batch Promotion Obstruction

**Theorem.** Let I be a pure preserved interval on the side `x=0`. Let J
be a nonempty finite set of levels j such that both `(0,j-1)` and
`(0,j+1)` belong to I. Suppose a replacement has insertion set exactly

```text
A_J={(1,j):j in J}
```

and arbitrary deletion set `D subset F`, anywhere on the board. If the
replacement is feasible, then

```text
|D| >= |J|+q(J) > |A_J|,                            (5)
```

where q(J) is the number of maximal runs in J with successive difference
two, counted separately in the two parity classes.

**Proof.** Two preserved vertices at diagonally opposite corners of a
unit square force all four edges of that square. Thus feasible preserved
sets have no diagonal pair. The proposed insertion `(1,j)` is diagonal
to each of `(0,j-1),(0,j+1)`. Both boundary vertices must therefore be
deleted. In particular all proposed insertions were holes originally.
The required boundary deletion levels include

```text
(J-1) union (J+1).
```

For a parity run `a,a+2,...,a+2(t-1)` of size t, this union contributes
`a-1,a+1,...,a+2t-1`, of size t+1. Different maximal runs of the same
parity give disjoint sets; the two original parity classes give opposite
parities of deletion levels. Hence the union has size `|J|+q(J)`.
These vertices belong to F and are distinct, proving (5). Additional
deletions cannot reduce this necessary count. QED.

This strengthens the single-center six-cycle obstruction in the cap note:
deleting the center `(0,j)` is not even one of the two compulsory flank
deletions. The obstruction is local and persists regardless of distant
connectivity or maximum status. It does not require the promoted hole to
be a contact; in particular it applies to every such contact promotion.

The theorem also sums over all four sides if every selected level in its
side coordinates is in `[2,n-3]`, and its flanks belong to a pure interval.
The required deletion vertices then lie on disjoint open sides. If J_s
are the nonempty level sets, any replacement inserting exactly those
inward holes satisfies

```text
|D|-|A| >= sum_s q(J_s)>0.                          (6)
```

It is therefore impossible to normalize repeated interior pure-interval
contacts by ANY neutral batch of these inward promotions alone, even with
arbitrary coordinated deletions elsewhere. If additional insertions B
are permitted, (6) instead requires `|B|>=sum_s q(J_s)` for neutrality.
Those extra insertions must have their own cycle-safety proof. Endpoints
without both preserved flanks, other insertion locations, and replacements
of whole regions are not excluded by this theorem.

More generally, for any insertion set A define its old-preserved diagonal
shadow to be the vertices of F diagonal to at least one member of A.
Every feasible replacement must delete that entire shadow, and A itself
must have no diagonal pair. These are necessary conditions only. They
do not detect the longer forced cycles addressed next.

## Exact Path-Cut Test

Here is a physical formulation that makes the nonlocal obligation explicit.
Take arbitrary `D subset F`, `A subset V minus F`, and put `F_0=F minus D`.
Define R_D to be the old forced edges whose preserved endpoints all lie
in D. Equivalently,

```text
R_D={xy in E(H(F)): {x,y} intersect F subset D}.
H_0=H(F_0)=H(F) minus R_D.                          (7)
```

The intersection in (7) is nonempty since xy was forced. This matters:
deleting one endpoint of an FF edge does not remove that edge if its
other endpoint remains preserved.

Let N be the set of new physical edges, listed without duplication:

```text
N={xy in E_grid: {x,y} intersect F_0 is empty,
                  {x,y} intersect A is nonempty}.
```

Contract the actual components of H_0 and retain N as a multigraph Q,
including loops and parallel edges. Then exactly

```text
(F minus D) union A is feasible iff Q is a forest.  (8)
```

Proof: contract each old tree, or insert the edges of N successively.
An edge is safe precisely when its endpoints are still disconnected.
Loops and parallel-edge cycles must be retained for this equivalence.
All components, including isolates, participate. No auxiliary UU edge
is being asserted to have been forced before the replacement.

For a single insertion `A={u}`, define

```text
W_D=N_grid(u) minus F_0,
T_D={u} union W_D.
```

The new edges are the star `uv`, `v in W_D`. Thus (8) specializes to:
all vertices of T_D must lie in pairwise distinct components of H_0.
Since H(F) is a forest, this has an exact path-cut version. For every
pair `a,b in T_D` connected in H(F), let P_ab be its unique old path.
The insertion after D is safe if and only if

```text
E(P_ab) intersect R_D is nonempty for every such pair.             (9)
```

Pairs in different original components need no cut. Deleting more
preserved neighbours of u changes T_D as well as R_D, so a proof must
not freeze the old terminal list during an exchange. For multiple
insertions, applying (9) separately is insufficient: their new edges
can form a cycle jointly in Q. Equation (8) is the full criterion.

This isolates the gap in an abstract contact rerouting: a split in a
carrier drawing is not necessarily a cut in H(F), and enough deleted
edges numerically do not guarantee that the specific paths in (9) are
cut. A bounded local replacement must either control the connectivity
partition of its outside terminals or prove safety for every realizable
such partition. Maximum cardinality alone supplies neither assertion.

## What Saturation Supplies

For a maximum F, (8) implies that every replacement with `|A|>|D|` has
a cycle in Q. For a tie-broken maximum, every neutral replacement that
improves the selected tuple also has a cycle in Q. These are genuine
necessary conditions, but not an allocation of distinct obstruction paths.
One physical tree path may obstruct many candidate replacements.

Even the weaker single-insertion saturation cannot supply a linear
reserve by distinct witnesses. The full rods at `x=0,3,...,3k` on this
board are inclusion-maximal: every hole has a vertical hole neighbour
in the same rod tree, taking the inward neighbour at either horizontal
boundary. The star test blocks every promotion. This is the symbolic
example proved in the projection note, not a claim that these sets are
maximum or counterexamples to the target. It explains why using only
single-promotion witnesses discards the additional hypothesis that matters.

The scalar linear-excess example in the cap note likewise is not known
to be realizable, much less maximum. It rules out closing its retained
scalar inequalities by elimination alone; it does not refute a
maximum-specific geometric theorem. The compatible monotone orders of
the two seam banks also cannot be replaced by a crossing contradiction
without new localization of actual forced paths.

## Remaining Obligation

A sufficient noncircular maximum-specific statement is now precise:
choose a fixed tie-break on maxima; whenever its chosen maximum has
`D_met>D_0` for every allowed allocation in (2), exhibit concrete D,A
such that Q in (8) is a forest and either `|A|>|D|`, or `|A|=|D|` and
the tie-break improves. All donor and join allocations must be recomputed
or explicitly retained without reuse. Proving this statement would close
the constant-gap route through (3). It is not proved by the present note.

The proved obstruction (5)--(6) rules out a natural distributed version
of the pure-boundary-center exchange even before the nonlocal test. A
successful replacement must introduce compensating insertions elsewhere
or avoid those interior promotions. For that enlarged replacement, the
unresolved task is to establish (8), not just count carrier deletions,
assume connectedness, remove isolates, impose four pure carriers, or
regard a metric join as a modification of F.

The unconditional bound supplied by the inputs remains
`P(3k+2)<=T+floor(k/2)+1`. Only this document was written. No finite-grid
search, optimization, lower construction, or Lean command was run. The
new claims have the paper proofs above and have not been independently
audited in this task.

## Pendant Translation Continuation

Date: 2026-09-09. Append-only continuation. The preceding text is unchanged.
Read the new small-bank, exposed-bank, full-height moving-seam, root-hull,
and interior-escape results in `PAPER_CLEAN_METRIC_CLOSURE.md`, as well as
the actual-port obstruction in `PAPER_TERMINAL_TRANSPORT.md`.

There is a new maximum-specific structural lemma below: at a suitably
tie-broken maximum, every unobstructed positive-coordinate translation of
a connected union of whole carriers must have a repeated attachment to
one actual remaining component. This is proved by an exact gluing test,
not by treating contact-tree topology as geometric clearance.

It does NOT prove that partial fronts can be eliminated. A concrete
pendant-subtree obstruction shows why: even a whole positive-height wide
bank, translated with its actual connecting spine, can lose its sole old
attachment and acquire arbitrarily many attachments to ONE retained tree.
The slide is then infeasible. An exact linear deletion cost for repairing
this particular slide is proved below. The obstruction is not claimed to
be maximum or low-K, and does not refute a low-K normalization theorem.

### What The New Geometry Reduces

The direct K allocation in the metric-closure note now pays ALL small
banks, with their actual unused refunds retained. Under K<n, at most
thirteen wide banks remain. Exposed positive-height wide banks, with the
literal common-root localization and near-boundary FF edges in that
note, have a simultaneous payment with error at most six per selected
bank. These are direct K resources, not additions to the earlier clean
isolate bank in (2).

The full-height two-actual-root moving seam on `n=3s+5` satisfies
`K>=4s-18`, including arbitrary feasible extensions in its terminal
regions. That theorem rebuilds its original-resource allocation; it
cannot be added to already spent small-bank or boundary-bank coupons.

Thus the maximum-specific task is no longer to classify arbitrary tiny
banks. It is to expose or otherwise pay the remaining partial wide-bank
fronts while retaining actual root locations. The root-hull continuation
also retains `2beta_I+H_price-3u_F` and the internal terminal escape terms;
none is erased by there being thirteen colors. The transport note shows
why even an actual connected carrier is not a metrically costless routing
vertex. The argument below does not assume any of these terms paid.

### Exact Connected-Support Gluing

For a preserved set S, let its support graph be H(S) restricted to S and
its grid neighbours, rather than the spanning graph with all its irrelevant
isolates. Suppose F is feasible, S is a nonempty subset of F, and this
support graph is connected. Put `R=F minus S` and `G=H(R)` on the whole
board. Let `S'=S+v` be a lattice translation contained in the board and
disjoint from R. Write T for the support graph of S'.

T is a tree. To justify the boundary issue, extend the support of S to the
infinite square grid before translating. Every new vertex outside the
original square has at most one neighbour inside the square, so this only
adds pendant vertices. Translation preserves that tree. Restricting back
to the square deletes only outside pendant vertices: all translated
preserved vertices lie inside. The support remaining around S' is still
connected and acyclic.

For each component G_i of G meeting T, form the actual graph intersection
`L_i=T intersect G_i`, including its vertices and its common edges. Let
`h_i` be its number of connected components. Then

```text
cycle_rank(H(R union S')) = sum_(i meeting T)(h_i-1).              (10)
```

In particular the translation is feasible if and only if EVERY L_i is
connected. A one-vertex attachment is sufficient, but connected overlaps
containing edges are also allowed. Two distinct contacts to the same
retained tree are unsafe unless their connecting overlap is itself present
in T and G. Contact labels alone do not check this condition.

Proof of (10): each L_i is a nonempty forest, so its vertex count minus
edge count is h_i. If q components of G meet T, the union has
`c(G)+1-q` components. Inclusion-exclusion for its vertices and edges,
using that G is a forest and T is a tree, gives
`|E|-|V|+c=sum_i h_i-q`. This is exactly (10). All other components of G,
including isolates, cancel. This is equivalent to the component-cut test
(8), now specialized to the union of a retained forest and one moved tree.

Notice that deleting S need not literally cut out a vertex subtree of
H(F). Edges from a deleted preserved vertex to a retained preserved
neighbour can remain. Using G=H(R), rather than a nominal contact-tree
cut, is essential. Formula (10) recomputes all such surviving edges.

### A Genuine Maximum-Specific Alternative

Choose F first to maximize f, then to minimize r, and then to maximize

```text
Phi(F)=sum_((x,y) in F)(x+y).
```

These finite tie-breaks are available without any normalization hypothesis.
Let S be a nonempty union of WHOLE carriers of F whose support is
connected, and let v be `(1,0)` or `(0,1)`. Then at least one of the
following holds:

1. S+v leaves the board.
2. S+v meets a retained preserved vertex in R.
3. For some actual component G_i of H(R), the intersection of G_i with
   the support of S+v is disconnected.

Proof: otherwise (10) makes `F'=R union (S+v)` feasible, with `|F'|=f`.
Deletion of whole carriers does not split any retained carrier. Translation
preserves the internal carrier components of S. New adjacencies between
R and S+v can only merge these components, so `r(F')<=r(F)`. A strict
decrease contradicts the second tie-break. In the equality case,
`Phi(F')-Phi(F)=|S|>0`, contradicting the third. QED.

This includes pendant connected carrier subtrees, but needs no pendant
hypothesis. It is an actual structural consequence of maximum cardinality
and the stated tie-break. Its third alternative is a repeated-root
obstruction, not a bound on the number of unpaid fronts.

There is also a positive translation lemma implicit in the proof: if
S+v fits, avoids R, and has connected intersection with every remaining
component, the displayed replacement is genuinely count-neutral and
cycle-safe. One may iterate such verified moves, with Phi strictly
increasing and bounded by `2(n-1)f`. This proves termination at a blocked
configuration, NOT termination at a boundary-exposed configuration.
There is no proved monotonic decrease of partial fronts under these moves.

### A Whole Wide Bank With A Pendant Root Hull

Here is a symbolic obstruction for every `k>=4`, `n=3k+2`, `A=n-1`.
Put `m=k-1` and use the marked rows

```text
y_j=4+3j, 0<=j<m;       y_(m-1)=A-3.
```

Let the movable preserved set S be

```text
movable spine: {(3,y):3<=y<=A-3},
teeth:         {(x,y_j):5<=x<=A-3, 0<=j<m}.
```

Let the retained preserved set R be

```text
short root:    {(3,0),(3,1)},
top bridge:    {(x,0):5<=x<=A-2},
right spine:   {(A,y):0<=y<=A-3}.
```

Preserve exactly `F=R union S`, with all other vertices holes. The m teeth
are ONE entire horizontal bank: successive rows differ by three and their
FF intervals coincide. There is no other horizontal carrier on their
row residue. Its width is `A-8>A/3` for A>=13, and its positive height is
`3(m-1)`. Thus it is a wide bank, not a single-carrier degenerate example.

Each rod has tree support. The tooth supports are mutually disjoint and
each meets the movable spine support only at `(4,y_j)`. Hence S has tree
support. R also has tree support: its two contacts are `(4,0)` and
`(A-1,0)`, joining its three carriers in a path. The two support trees
meet exactly at `(3,2)`, the contact from the short root to the movable
spine. There are no other intersections, by the displayed row and column
separations. Thus F is feasible, with one nontrivial forced tree and
arbitrary actual isolates outside it.

The contact subtree on the m teeth and their movable spine is genuinely
pendant in the actual carrier contact forest. It contains the WHOLE wide
bank and its actual root hull, and has exactly one contact to R. This
does not use a virtual contraction of a bank.

Translate all of S one cell east. Its spine is now at x=4 and its teeth
occupy `[6,A-2]` on the same marked rows. The translated preserved set
S' fits in the board and avoids R. Both separate support graphs are still
trees. Their intersection is now exactly

```text
{(A-1,y_j):0<=j<m},                                (11)
```

with no common edges. The old attachment at `(3,2)` has disappeared.
Every vertex in (11) lies in the SAME nontrivial component of H(R), joined
there along the right spine. Formula (10) gives

```text
cycle_rank(H(R union S'))=m-1.                      (12)
```

These are genuine cycles through moved teeth, the moved spine, and the
retained right spine. They do not arise from a diagonal preserved pair;
there is no such pair after the slide. In particular this is not a failure
to cut the one old pendant attachment: that attachment was actually cut.
It is a failure of simultaneous reattachment at the new front.

### Exact Cost Of Deletion-Only Repair

Keep this rigid translated S' fixed. If `D subset R` and
`S' union (R minus D)` is feasible, then

```text
|D|>=m-1.                                         (13)
```

Moreover equality is attainable by deletions, so (13) is exact for this
specified repair operation. It is not a lower bound for all possible
distributed replacements.

Proof: let t be the number of marked right-spine vertices `(A,y_j)`
deleted. Each of the other `m-t` vertices still attaches to the connected
moved support through its own contact in (11). No two of these surviving
marked vertices can remain connected in `H(R minus D)`, by (10).

Between each two consecutive surviving marks, the old right-spine path
must therefore lose an edge. Every edge on that path was FF. It is
removed only when BOTH its consecutive right-spine vertices are deleted.
Marks are spaced by three, so such a deleted adjacent pair contains at
least one unmarked deleted vertex. The open intervals between consecutive
surviving marks are disjoint; choose one such unmarked deletion from each.
When `m-t>=2`, this requires at least `m-t-1` unmarked deletions in addition
to the t marked ones. The cases `m-t<=1` already have `t>=m-1`. Deletions
in the short root or top bridge cannot cut these right-spine paths.
This proves (13).

Conversely delete any m-1 of the marked right-spine vertices. They are
three-spaced, so all the vertical spine edges remain forced. Their
horizontal edges to the contacts in (11) disappear, leaving exactly one
intersection between the two support trees. The union is a forest by
(10). Thus m-1 deletions suffice. QED.

The translated bank had no loss of preserved cardinality before repair,
but its deletion-only repair now loses exactly m-1 vertices. To make this
particular repair neutral requires at least m-1 further insertions with
their own simultaneous safety proof. A constant number of bank colors
does not provide those insertions or make this correction cost constant.

### Empty Gap Does Not Mean Safe Extension

The original feasible F also obstructs the local-gap-fill premise directly.
At any marked row, try to extend its tooth by preserving

```text
u=(A-2,y_j).
```

This vertex was a hole, no old preserved vertex is diagonal to it, and
its promotion is internally consistent with the straight tooth. However,
u was already a leaf of that tooth's forced support, and `(A-1,y_j)` was
already a leaf of the right spine's forced support. Both belong to the
SAME original tree, connected through the old pendant root and top
bridge. Promotion forces the previously UU edge
`(A-2,y_j)--(A-1,y_j)`, which closes that unique old path.

The upper and lower new neighbours of u are isolates in this example.
The newly forced edge to the right is therefore the sole cycle-producing
edge, and the resulting graph has cycle rank one. This is a physical
long-root obstruction to filling an apparently empty endpoint gap, not
an assertion that an auxiliary UU edge was forced beforehand.

### Scope And Dependency Failure

The example has the exact original counts

```text
f=3k^2-2, r=k+3, b=6k+12, c=17k+3,
K=24k+18.                                         (14)
```

The carrier and boundary counts follow directly from the displayed
rods, including m teeth; c follows from the forest ledger. These examples
are well outside K<n and are not claimed maximum. They refute the
unqualified rule that translating a pendant actual contact subtree is
automatically legal until it encounters a preserved vertex or the board
boundary. They do not refute a NEW theorem deriving extra clearance,
alternative repairs, or sufficient payment from maximum status and K<n.

The proposed acyclic dependency conclusion still has two separate gaps.

First, a bank is not generally a connected contact subtree. The metric
note proves that its induced contact forest has at least `a_B+1` pieces.
Connecting these pieces requires actual external root paths; their hull
can include other banks and need not be pendant. In the example we granted
the stronger pendant-hull hypothesis, and the slide still failed.

Second, a blocked slide's prospective contacts are not edges of the OLD
forest. In (11) they are m prospective links to one retained tree, while
that tree and the movable hull previously had just one contact. Acyclicity
of the old contact forest says nothing that makes the prospective links
acyclic. Recording one directed bank dependency forgets their multiplicity
and their attachment positions. Likewise, identifying disconnected pieces
of one bank is not a forest-minor operation. Thirteen bank vertices do
not bound these missing data.

Nor does the increasing Phi cure this issue. Phi increases only along
LEGAL replacements. It does not orient prospective contact paths into a
physical acyclic graph, and it does not certify that a blocked terminal
can move into the next bank. Declaring the iteration finished at its first
collision proves only the repeated-attachment alternative, not boundary
exposure or payment of that collision.

### Remaining Maximum Obligation

The new maximum lemma reduces a proposed legal positive-coordinate hull
slide to three explicitly testable failures. To complete the global route
one still needs, under K<n, a non-reusing argument which either pays the
remaining unexposed packet demands or supplies a better replacement when
the third failure occurs. Such a replacement must break the repeated
attachment paths in G, supply any compensating insertions, and pass the
full simultaneous component-cut test. The gap-fill test alone cannot do
this. Neither can the deletion-only repair of (13).

No theorem here makes every unexposed wide bank a freely movable pendant
hull, bounds its repeated attachments by an absolute constant, forces
dependency acyclicity, or turns internal escape components into original
component coupons. Consequently the strong boundary and full-height
theorems still lack the maximum-specific root-localization lemma needed
for an unconditional `K>=n-O(1)`.

Verification: an in-memory Python 3 check on n=14 only verified the actual
support intersections, forced-edge cycle ranks, and absence of diagonal
pairs. The tuples `(f,r,b,c,cycle_rank)` were `(46,7,36,71,0)` originally,
`(46,7,36,73,2)` after translation, and `(47,7,36,69,1)` after the specified
single gap fill. Every one of the 20 single retained-vertex deletions
still left a cycle after translation. The forest ledger is used only
for the original feasible set, not for the two cyclic sets. The first
attempt to run the check found no `python` executable; `python3` ran all
assertions successfully. The arbitrary-size claims have the proofs above;
no board above side 14 was instantiated, no optimization or Lean ran, and
only this note was appended. These new paper results are not independently
audited in this task.
