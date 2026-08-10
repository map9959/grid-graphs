# Four-crop local alternative: exact obstruction

## 1. Outcome

The current exact signatures and candidate-owned primal disks do not imply the
proposed `E1`--`E4` local alternative.  The obstruction occurs before global
laminarization is relevant: one indivisible repair bundle can create several
pairwise disjoint inclusion-minimal obstruction disks.  Planar Euler accounting
counts all of those cycles, but does not turn them into distinct repair
vertices, free slots, or component credits.

There is also an exact gap in an adjacent-crop transfer.  The present overlap
lemmas preserve a path already known to lie in the common overlap, and they are
stated for the induced graph on `F`.  The repair signature instead contracts
components of the forced graph

```text
H = G - E(G[U]),
```

after every repair prefix.  An ambient ancestor equality, or even equality of
the physical bundle labels, does not reflect connectivity in either crop.

Thus no proof of the four-crop bundle-preserving charging theorem is claimed.
Section 4 states the exact missing local sublemma.  It must control all
independent cycles of a complete bundle and must reflect prefix connectivity
across an adjacent-crop overlap.

## 2. Sequential admissibility adds no selectable-edge freedom

Fix a crop `Q`, its initial forced forest `H_Q`, and a set `R` of repair
vertices.  Let `E_Q(R)` be the physical repair-edge set retained by the exact
signature.  If `S` is a subset of `R`, then

```text
E_Q(S) subseteq E_Q(R).                                (1)
```

Indeed, the condition that an edge has an endpoint in the repair set is
monotone, while the condition that neither endpoint was initially forced is
independent of the repair set.

**Lemma 2.1 (prefix criterion).** Let `u_1,...,u_t` be an ordering without
repetition and put `R_k={u_1,...,u_k}`.  Then the following are equivalent.

1. The complete repair `R_t` is admissible.
2. Every prefix `R_k`, `0<=k<=t`, is admissible.

**Proof.** By the exact signature theorem, admissibility is acyclicity of the
physical-edge-labelled component quotient, equivalently acyclicity of
`H_Q union E_Q(R_k)`.  If the final graph is acyclic, every prefix graph is a
subgraph by (1), and is therefore acyclic.  The converse includes the prefix
`k=t`.  QED

Consequently an ordered argument may expose a first blocked bundle, but it may
not select only a favorable edge or only one favorable obstruction disk from
that bundle.

## 3. Two minimal disks owned by one complete bundle

Consider the `3 x 3` grid with coordinates `(row,column)`.  Put

```text
F = {(0,2),(2,0)},             u=(1,1),
N=(0,1), E=(1,2), S=(2,1), W=(1,0).
```

All vertices other than the two displayed members of `F` are in `U`.  The
forced graph `H=G-E(G[U])` has exactly the four nonisolated edges

```text
N--(0,2)--E,                   W--(2,0)--S.             (2)
```

Hence `H` is a forest.  Inserting `u` forces its complete four-edge bundle

```text
B(u)={uN,uE,uS,uW}.                                    (3)
```

Contract the components of `H`.  Write `A` for the top path in (2), `B` for
the bottom path, and `C` for the isolated component containing `u`.  The exact
labelled quotient of (3) consists of

```text
two parallel C--A labels and two parallel C--B labels.  (4)
```

It therefore has cycle rank

```text
4 - 3 + 1 = 2.                                         (5)
```

In the primal grid the two corresponding simple cycles are

```text
u,N,(0,2),E,u,          u,W,(2,0),S,u.                  (6)
```

Their obstruction disks are respectively the top-right and bottom-left unit
faces.  They are nonempty, disjoint, and inclusion-minimal among nonempty face
sets.  Every fresh edge of either cycle belongs to the same complete bundle
`B(u)`, so both disks are owned by the same candidate.

This is a rigorous local counterexample to the step needed by a minimal-disk
induction:

```text
minimal owned disk  ->  one locally resolvable blocked bundle.          (7)
```

Resolving or charging either disk alone does not make `B(u)` admissible; the
other parallel pair remains a cycle.  The candidate cannot be split into two
repairs.  Both disks already have minimum area, so moving from one to the other
does not decrease an area potential.  Euler accounting gives the correct value
two in (5), but both Euler units have the same owner.  This is precisely an
owner-congestion failure, not a crossing or laminarity failure.

The pattern can be embedded in the common interior of neighboring sufficiently
large corner crops.  If the surrounding vertices are left in `U`, both crops
see the same four physical labels and the same two path components.  A transfer
then reproduces (4) and cannot strictly decrease any potential determined only
by the local exact quotient and the two disk areas.  Extra global frame data
could break the tie, but that requires a new theorem; it is not a consequence
of the owned-disk arrangement.

## 4. Exact missing sublemma

For a repair prefix `R`, let

```text
H_Q(R) = H_Q union E_Q(R)
```

and assume it is a forest.  For a next candidate `u`, put

```text
D_Q(R,u) = E_Q(R union {u}) setminus E_Q(R).             (8)
```

Thus `D_Q(R,u)` contains every physical label newly forced by repairing `u`;
an edge from `u` to an earlier repair is already present and is not counted a
second time.  Let `K_Q(R,u)` be the physical-edge-labelled quotient obtained
by contracting `H_Q(R)` and retaining all labels in `D_Q(R,u)`.  Define its
bundle obstruction rank by

```text
beta_Q(R,u)
  = |E(K_Q(R,u))| - |V(K_Q(R,u))| + c(K_Q(R,u)).         (9)
```

Isolated quotient vertices may be omitted from (9).  Since the contracted old
graph is a forest,

```text
beta_Q(R,u)=0  iff  R union {u} is admissible.          (10)
```

The example in Section 3 has `beta_Q(empty,u)=2`.  A sound local alternative
must use `beta`, or an equivalent basis of all bundle cycles, rather than one
canonical obstruction disk.

The missing geometric statement can now be isolated as follows.

> **Complete-bundle private resource or reflected-transfer lemma (`BRT`).**
> Let `Q` be an active corner crop, let `R` be an admissible ordered prefix,
> and let `u` be the candidate selected for the next unresolved frame charge.
> If `beta_Q(R,u)>0`, then either:
>
> 1. all `beta_Q(R,u)` independent obstruction units admit distinct currently
>    unused free-frame or component resources, with every resource assignment
>    made to the complete bundle `u`; or
> 2. there is an adjacent crop `Q'`, a corresponding prefix `R'`, and a
>    corresponding complete candidate bundle `u'` such that:
>    * every physical edge label of `E_Q(R union {u})` used in the transfer
>      lies in the common overlap and has the identical ambient label in `Q'`;
>    * for every pair of endpoints of those labels, reachability in `H_Q(R)`
>      is equivalent to reachability by a path in the common overlap, and is
>      equivalent to reachability in `H_Q'(R')`;
>    * these equivalences induce a label-fixing isomorphism between the two
>      restricted component quotients, including loops and parallel fibers;
>    * the prescribed global potential strictly decreases after transferring
>      the whole unresolved charge together with the whole bundle-obstruction
>      basis.

The first conclusion is the exact noncongestion assertion needed for a unique
free-frame discharge or a unique component cancellation.  It explicitly
forbids counting the two disks in Section 3 against one unit-capacity owner.
The second conclusion is the exact content needed for an adjacent-crop
transfer.  Its reachability equivalence is essential: equality of ambient
component ancestors supplies only one implication and can hide a connecting
path that leaves one crop.

`BRT` is the first missing sublemma, not a consequence of the current planar
facts.  The existing results supply only:

```text
* exact physical labels and complete overlapping bundles;
* exact labelled-quotient admissibility;
* one nonempty disk from one chosen blocked-insertion cycle;
* connected intersection of the old forest parts of two chosen cycles;
* persistence of a path already contained in the common overlap.
```

They do not supply a basis of all cycles created by one bundle, an injective
resource assignment for that basis, reflection of forced-graph connectivity
through an overlap, or a potential drop.  Planar arrangement and Euler
accounting alone cannot supply the first two, as Section 3 demonstrates.

## 5. Consequence for `E1`--`E4`

Under the natural bundle-preserving reading, `E1` is exactly `beta=0`.
Alternatives `E2` and `E3` require the private-resource branch of `BRT`, and
`E4` requires its reflected-transfer branch plus an independently defined
well-founded potential.  Without `BRT`, the four cases are not exhaustive.

The smallest repair to the proposed proof is therefore not a global
laminarization theorem.  It is a complete-bundle anti-congestion theorem that
handles `beta_Q(R,u)>1`, followed by component-reflecting overlap transport.
Any formulation using only one canonical disk per blocked candidate is false
by (2)--(6).

## 6. Exact multiplicity bound for one complete bundle

There is an unconditional per-vertex bound which uses the complete bundle,
not a selected obstruction cycle.  It is independent of planarity beyond the
maximum grid degree.

Let `C` be the component of `H_Q(R)` containing `u`, let

```text
k = |D_Q(R,u)|,
q = the number of components other than C met by the other endpoints
    of labels in D_Q(R,u).                              (11)
```

Repeated endpoints in one old component count once in `q`; a label whose other
endpoint is already in `C` counts zero.  This retains exactly the loop and
parallel-edge multiplicities suppressed by an unlabelled component signature.

**Lemma 6.1 (exact star-multiplicity formula).** For every admissible prefix,

```text
beta_Q(R,u) = k-q.                                      (12)
```

**Proof.** Every fresh label is incident with `u`, so after contraction every
edge of `K_Q(R,u)` is incident with `C`.  Its nonisolated quotient therefore
has the vertex `C`, the `q` distinct other component vertices, and all `k`
physical edges, including loops at `C` and parallel fibers.  If `k>0` this
multigraph is connected, and hence its cycle rank is

```text
k-(q+1)+1=k-q.
```

If `k=0`, then `q=0` and both sides vanish.  QED

**Corollary 6.2 (distinct-label defect basis).** Choose one label from `C` to
each of the `q` other components met by the fresh bundle.  Adjoin those chosen
labels to `H_Q(R)`.  The result is a forest, and each of the other `k-q` fresh
labels closes one fundamental cycle.  These cycles form a basis of the cycle
space of `H_Q(R) union D_Q(R,u)`.

**Proof.** After contraction, the chosen labels form a simple star on `C` and
the `q` other component vertices, so adjoining them preserves acyclicity.
Every omitted fresh label has both endpoints in one component of that enlarged
forest: it is either a loop at `C` or a repeated edge from `C` to one of the
`q` other vertices.  It therefore closes a unique fundamental cycle.  The
standard fundamental cycles of distinct nonforest edges are independent and
span, and their number is `k-q=beta_Q(R,u)` by Lemma 6.1.  QED

This assigns every defect unit to a distinct physical label of the one complete
bundle.  It does not assign the labels to distinct frame or component
resources: several basis labels may still be repeated incidences with the same
old component.

**Theorem 6.3 (sharp three-defect bound).** A complete next bundle in a square
grid crop satisfies

```text
0 <= beta_Q(R,u) <= 3.                                  (13)
```

**Proof.** Let `a` be the number of crop edges incident with `u` already in
`H_Q(R)`.  Because `u` is initially unforced and has not yet been repaired,
every crop edge at `u` is in exactly one of the old set or the fresh set:

```text
a+k=deg_Q(u)<=4.                                        (14)
```

If `a>0`, then `k<=3`, so (12) gives `beta<=k<=3`.  If
`a=0`, the component `C` is the singleton `{u}`.  When `k>0`, every other
endpoint is therefore in a component different from `C`, so `q>=1` and
`beta=k-q<=4-1=3`.  The case `k=0` is immediate.  Nonnegativity is the usual
cycle-rank inequality, or follows directly because `q<=k`.  QED

Thus the requested phrase “at most three unresolved units per vertex” has an
exact unconditional meaning: it is the nullity of the full fresh labelled
bundle.  The theorem does not assign those units to three distinct frame or
component resources.  Formula (12) only says that repeated incidence with old
components creates the units; it supplies no private capacity at those
components.

## 7. Sharpness and failure of adjacent-crop reflection

The bound (13) is attained in the exact four-crop geometry, and the same
example disproves connectivity reflection even when the whole candidate
bundle lies in the common overlap.

Take the `10 x 10` grid and the two top corner crops

```text
Q_NW = rows 0..6, columns 0..6,
Q_NE = rows 0..6, columns 3..9.                         (15)
```

Their common overlap is `rows 0..6, columns 3..6`.  Put `R=empty`, put every
vertex in `U` except the following nine vertices of `F`, listed in path order:

```text
(2,4),(2,2),(2,0),(4,0),(6,0),(6,2),(6,4),(6,6),(4,6). (16)
```

Consecutive displayed vertices are at axial distance two and have one common
`U` neighbor.  No nonconsecutive pair has intersecting incident-edge stars.
Consequently the nonisolated part of the forced graph `H=G-E(G[U])` is obtained
by pasting the nine stars successively at one vertex each and is a tree.  All
other components are isolated `U` vertices, so this is a valid forced forest
without any repair prefix.

Choose

```text
u=(3,5),
N=(2,5), S=(4,5), W=(3,4), E=(3,6).                    (17)
```

The complete four-label bundle

```text
{uN,uS,uW,uE}                                          (18)
```

lies in the common overlap.  The vertex `u` is isolated in both cropped forced
graphs.  In `Q_NW`, all four of `N,S,W,E` lie in one forced component: `N,W`
meet the star at `(2,4)`, `S,E` meet the star at `(4,6)`, and the whole chain
(16) joins those stars through columns `0` and `2`.  Therefore (12) has

```text
k=4, q=1, beta_Q_NW(empty,u)=3.                         (19)
```

In `Q_NE`, the vertices of (16) that remain are

```text
(2,4),(6,4),(6,6),(4,6).                               (20)
```

The first is in a different forced component from the last three.  Hence
`N,W` lie in one component and `S,E` in another, with no path between them in
`Q_NE`.  Thus

```text
k=4, q=2, beta_Q_NE(empty,u)=2.                         (21)
```

In particular,

```text
N connected to S in H_Q_NW(empty),
N not connected to S in H_Q_NE(empty),                 (22)
```

although `N,S` and every label of the complete bundle (18) lie in the common
overlap.  The connecting path in the northwest crop leaves the overlap and
returns.  The two restricted labelled component quotients have respectively
one four-edge parallel fiber and two two-edge parallel fibers, so they are not
label-fixing isomorphic.

This is a theoretical counterexample to either of the following proposed
reflection principles:

```text
complete bundle contained in an adjacent overlap
  -> prefix connectivity of its endpoints is reflected;

equality of the complete physical bundle labels
  -> equality of the bundle obstruction basis.         (23)
```

It also proves sharpness of Theorem 6.3.  It does not refute a `BRT` whose
transfer branch explicitly assumes the reachability equivalences in Section 4;
rather, it proves that those equivalences are an additional hypothesis and
cannot be derived from four-crop geometry or complete-label agreement.

## 8. Exact status of the proposed charging theorem

The following are now complete unconditional conclusions.

```text
1. Every blocked complete bundle has exactly k-q independent defect units.
2. There are at most three such units per candidate vertex, sharply.
3. A complete bundle wholly in an adjacent overlap need not reflect the old
   component relation, even for an empty prefix and a globally valid forced
   forest.
```

No unconditional private-resource-or-transfer theorem follows.  “Free-frame
resource,” “component resource,” its capacity, and the strict global potential
would first have to be defined.  Under any unit-capacity interpretation, a
proof must separately establish an injection for all `k-q` units; Theorem 6.3
only bounds the size of its domain.  Under any reflected-transfer
interpretation, it must verify overlap-contained paths for all endpoint pairs,
not merely overlap-contained labels.  Example (15)--(22) shows that the latter
verification can fail at the sharp three-defect bundle.

## 9. Canonical disks and seam witnesses do not remove congestion

The sharp example in Section 7 loses one defect unit when it is reflected to
the northeast crop.  It is therefore not a sink for a memoryless scalar
potential on those crop states.  A four-state sink for that restricted transfer
model is obtained by putting the same forced tree strictly inside the common
core of all four crops.

Fix `n=17`; larger squares contain the same example by translation.  The common
core is `rows 3..13, columns 3..13`.  Put every vertex in `U` except the nine
members of `F`

```text
(7,9),(7,7),(7,5),(9,5),(11,5),(11,7),(11,9),(11,11),(9,11),
                                                               (24)
```

listed in path order, and put

```text
u=(8,10),  N=(7,10),  S=(9,10),  W=(8,9),  E=(8,11).    (25)
```

Thus every displayed forced star lies in `rows 6..12, columns 4..12`, with a
one-cell margin inside the common core.  Abstractly, the configuration has the
following properties:

```text
* the nonisolated forced graph is a tree A;
* A and all its incident edges lie strictly inside the common core;
* N,W are leaves at one end of the A backbone, while S,E are leaves at
  the other end;
* the paths N--A--W and S--A--E have length two and bound the two unit
  cells incident with u;
* u is an isolated U vertex and its four grid neighbors are N,S,W,E.
```

The star-pasting construction (24) realizes these properties as
`H=G-E(G[U])`: consecutive `F` centers have axial distance two and their stars
meet once, while nonconsecutive stars are disjoint.  Their union is therefore
a tree.  Every other vertex remains in `U`.

**Proposition 9.1 (fourfold congestion in the unit-capacity witness model).**
For (24)--(25), in every corner crop `Q`,

```text
k_Q=4,              q_Q=1,              beta_Q(empty,u)=3.     (26)
```

The complete bundle and its old endpoint-connectivity relation are identical
in all four crops.  Relative to the fixed owner `u`, its planar cycle space has
a canonical basis of three facial cycles.  In the unit-capacity witness model
defined below, those three basis units have no frame witness, have the same
old-component witness, and induce no seam-split witness.  This owner-relative
facial basis does not assert that its disks are inclusion-minimal among
obstruction disks available globally from all candidates.

**Proof.** The vertex `u` is an isolated component and all four other bundle
endpoints lie in `A`, proving (26) by Lemma 6.1.  The graph

```text
A union {uN,uS,uW,uE}
```

is connected and has cycle rank three.  Euler's formula therefore gives three
bounded faces.  After irrelevant pendant subtrees of `A` are deleted, their
boundary cycles are simple; each contains a fresh edge at `u`.  Their closed
face disks are pairwise interior-disjoint.  Ordering the disks by the least
physical edge on their boundaries gives a canonical independent facial-cycle
basis for the cycle space created by the fixed owner `u`.  This proves
owner-relative faciality and independence, not global inclusion-minimality
against obstruction disks owned by other candidates.

Use the exact local witnesses naturally supplied by the proposed argument.  A
frame witness is an intersection of an owned disk or its supporting old path
with the crop frame.  A component witness is the old component containing the
non-`u` endpoints on that cycle.  A seam-split witness is one of the independent
split tokens obtained by restricting that old component to an adjacent overlap,
as in Section 5 of `FOUR_CROP_SIMULTANEOUS_REPAIR_RANK.md`.  The configuration
is strictly inside the common core, so there is no frame intersection.  Every
component witness is `A`.  Moreover `A` restricts to the same connected tree in
every adjacent overlap, so its seam-split rank is zero.  Thus

```text
frame:       empty,
component:   (A,A,A),
seam split:  empty.                                      (27)
```

Consequently the three basis units cannot be injected into distinct resources
when each of these explicitly defined frame, component, and seam witnesses has
unit capacity.  QED

Changing the deterministic facial or fundamental basis does not remove this
failure of the unit-capacity witness model.  It changes three representatives
of a three-dimensional cycle space, but it does not change the single
supporting old component, create a frame intersection, or create overlap split
rank.  Owner-relative facial separation does not create additional witnesses.

**Proposition 9.2 (memoryless scalar-potential sink).** No transfer rule on the
four fixed corner-crop states of (24)--(25) can resolve the witness-model
congestion solely by transferring the complete unresolved bundle and requiring
a strict decrease of a memoryless scalar potential whose value is determined
by the current crop state.

**Proof.** Reflection to any adjacent crop fixes every physical bundle label,
the complete old tree `A`, its endpoint partition, and the three-dimensional
owned cycle space.  In particular, the candidate-restricted quotients
`K_Q(empty,u)` are label-fixing isomorphic, and every reflected state has the
witness data (26)--(27).  This is an equality only of the candidate-restricted
quotients, not of the complete crop quotients.  Pick a crop where the proposed
memoryless scalar potential has minimum value among the four fixed states.
Neither adjacent transfer has smaller value.  At that crop the unit-capacity
witness assignment fails by (27), while the strict-transfer branch is
unavailable.  Starting elsewhere only gives a finite strictly descending chain
ending at such a sink without changing the witness data.  This does not exclude
a history-dependent potential, an enlarged state space, or another `BRT`
resource model.  QED

Sequential admissibility supplies no escape.  The empty prefix is admissible
in every crop, and transfer keeps that prefix and all old connectivity.  The
complete insertion of `u` is inadmissible because `beta=3`.  Lemma 2.1 forbids
discharging the three cycles by inserting selected bundle edges or by treating
their disks as three sequential repairs: the only repair object is the complete
bundle.

Thus the proposed ingredients prove `beta<=3` and produce three distinct
canonical owner-relative facial obstruction units, but do not by themselves
prove `BRT`.  In the explicitly defined unit-capacity witness model, the exact
unresolved congestion configuration is

```text
(k,q,beta)=(4,1,3),
three owner-relative facial basis disks,
one repeated old-component witness,
zero frame witnesses,
zero seam-split witnesses,
the same candidate-restricted labelled quotient K_Q(empty,u)
  in all four crops.                                     (28)
```

This witness model can support `BRT` only if it introduces a resource absent
from (28), or gives the repeated component capacity greater than one together
with a separate global accounting theorem.  The owner-relative canonical
basis and seam components alone do not provide unit-capacity injections.  The
example does not rule out other `BRT` resource definitions or accounting
schemes.
