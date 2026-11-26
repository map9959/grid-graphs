# What a failed crop can pay at an end cut

**Result.** The useful quantity is the cycle rank lost when donor
edges are removed *after contracting the candidate end ports*. It is
not the number of marks left behind by the crop. One donor can pay for
an otherwise losing end repair. But there is no unconditional dichotomy
between the six-layer crop and the two end-row refills, even allowing
arbitrary paid exterior deletions for the refill. Both can fail on a
physical tree within a **constant** of the comb.

## Exact price for remote donors, at any width

Use the [end-band replacement](END_BAND_RANK.md), holding its initial
compulsory cycle deletions fixed. Let `U` be any unrecovered marked
sites strictly more than two rows from both end lines. These sites
cannot change a port's eligibility or whether a backing edge is
compulsory. In the exterior erase them temporarily. Contract the
remaining forest and the compulsory edges. Write `E` for the edges
lost by the erasure, retaining **all owners** of each edge. `E` is
independent before any optional port is inserted. Let `T` be the set
of all eligible optional normal edges, not only those used by one
optimal repair. Form `Q` by contracting the components of `T` as
well. Keep loops and parallel edges of `E` in `Q`.

For `S⊆U`, let `E'` be the edges still having at least one owner
outside `S`. With `ν` the graphic nullity in `Q`, the exact extra
gain from deleting `S` and refilling is

```
ν(E) - ν(E') - |S|.
```

Indeed rank of `E∪T` is `|E| + rank(T after E)` in the first order,
and `rank(T) + rank_Q(E)` in the reverse order. Subtract the same
identity for `E'`. This prices the actual paths from the donors to
the end, even if multiple donors support a single return. It works
for arbitrary selections; the replay's greedy search only supplies a
lower bound on the best selection.

In a replayed side-163 tree the crop cost **1275** against a comb
budget of **1269**. The end cuts at rows 9 and 153 initially lost one
mark. The depth-five donor `(5,90)` had an **occupied crop shadow**.
Its deletion split two independent returns in the port quotient:
the end rank rose by two at cost one. The resulting zero-loss aligned
repair gives the comb upper on this input. An independent small
check recomputes the full physical optimum for all 32 subsets of a
donor set including shared-edge owners.

### Near and blocking donors: upper certificate

For a full-width refill we can also bound *every choice* of leftover
deletions. Temporarily erase all permitted exterior donors `V`:
the leftovers and any backing owner on an original compulsory cycle.
Splitting components cannot put a previously acyclic compulsory
edge on a cycle. An originally unblocked normal, if selected, forces
its port edge, including when the backing is marked. Thus take every
such in-board edge as optional for an **upper** bound. Outside-board
ports are free. A newly unblocked normal needs at least one deleted
off-center backing mark; the blocker sets for different ports are
disjoint. Give one designated blocker a one-mark deletion credit if
the entire blocker set is deletable.

Apply the same quotient to all remaining donor edges. For each `u`,
let `I_u` be its incident donor edges, even shared edges. The rank
increase from removed edges `L` is `ν(E)-ν(E\\L)`, the rank function
of the dual graphic matroid. By monotonicity and subadditivity it is
at most the sum of the singleton-*donor* prices for the deleted
marks, and at most `ν(E)`. For an optimistic net bound sum the
positive parts of these prices minus each donor's fee (zero for a
designated blocker, one otherwise), capped by `ν(E)`. This applies
without enumerating deletion subsets; it is not an attainability claim.

## A certificate even against arbitrary paid exterior deletions

Consider consecutive pitch centers on one end line `y` for which both
normals were originally unblocked and the entire tangential stretches
on **both** backing rails `y±3` were marked. On an interval of `t`
such teeth, the number of new normal marks, **net of exterior deletions
on its two rails**, is at most `t+1`. To see this, call a tooth double
if both its normals are selected. Each double has a path between its
two rail feet unless a foot mark was deleted. Charge these lost feet
once. Between every two successive remaining doubles one of the two
tangential paths must be broken, or the two doubles close a physical
cycle. Breaking a path takes a missing edge and thus two consecutive
deleted rail marks. At least one is off pitch and cannot have paid
for a lost foot. The intervals have disjoint interiors. Consequently
each double beyond the first pays for one distinct exterior deletion.

Start with all originally eligible normal slots, plus one center per
tooth. Subtract one for each consecutive pair certified this way,
then subtract the old band count. Any extra normal on an originally
blocked face costs its own deletion at `y±2`, separate from the rail
charges. This gives an upper on the total gain for **arbitrary paid
exterior deletions**, not just the unrecovered set. The opposite
three-row bands use disjoint charges when the cuts are more than six
rows apart. Exterior insertions are a different operation.

## Why the disjunction fails

Start with the [five wrapped paths](END_BAND_RANK.md) around the comb
of side `n-30`, `n=3k+1≥103`. On each side choose a central coordinate
`a=3 floor(n/6)+1`; use offsets `X={-9,-6,-3}` and `Y={-9,-6,…,9}`
from `a`. At depth two add teeth at `X`; at depth five add teeth at
`Y`. For each such tooth at `(h,x)`, empty `(h+1,x+j)` for
`j=-1,1,2,4` and mark `(h+2,x),(h+2,x+3)`. At depth nine remove
the marks directly below the depth-seven additions. Rotate this
prescription onto each side.

The occupied shadows remain marked. On the next path the consecutive
holes just after each attachment split it into arcs, each receiving
at most one link from the outer paths. The auxiliary marks at depth
four are in the same columns as depth-five teeth and give no second
link; the depth-seven marks have no depth-nine contact. The side
edges of these added stars lead to leaves. This leaves a
forest. Relative to the five paths the score change per side by depth
is `+3,-8,+4,+7,-16,+8,-8`, i.e. minus ten. The resulting marking
has `comb-58` marks and admits a physical completion.

For a three- or six-layer cut all introduced rim vacancies on the
smaller square have a **marked interior diagonal**. Even optimizing
the entire smaller perimeter with the interior fixed can add at most
five net marks (the five original path omissions). The peeled counts
are `4n+3` and `8n-18`. Even after recovering five, these exceed the
respective comb increments `4n-6+e'` and `8n-36+e`, with `e'≤1`,
`e≤2`. Extra full-degree sites of a completion do not weaken this
obstruction.

Merely occupying the shadow does not have this effect. In a separate
side-103 replay, all 16 occupied depth-five shadows had a flanking
vacancy that could be promoted on the smaller square. Checking the
incident crop components before each promotion recovered 16 against
a raw crop loss of 790. The marked interior diagonals distinguish the
locked family from this recoverable case.

In either orientation all but a bounded number of triples at each
candidate depth still see the original parallel rails. For a depth
divisible by three the interval argument above limits these triples
to two marks apiece plus a constant. At other depths one normal
faces a full blocking row; its inclusion costs an exterior deletion.
The original three-row band had three marks per triple. Hence the
loss grows linearly for any choice of depths 1 through 9, even
allowing paid deletions. On the long undisturbed stretches a blank
neighbor of a rail cannot become a new full site in a completion
because of its marked diagonal.

At **103** the replay gave **3588 actual full-degree sites**. The
three- and six-layer removals cost 415 and 806, against budgets
406 and 789. For the six-layer crop, 44 marks remained on layers
four and five. Among all 81 cut pairs in each orientation the best
donor-rank upper on gain was **−34**; the best arbitrary-deletion
rail upper was **−27**. Neither test reaches the comb. The separated
side-hole theorem also cannot simply be applied here: the side bars
have consecutive holes between every allowed pair of end cuts.

This is an obstruction to the **reductions**, not to the conjecture.
It says nothing against a dichotomy for *maximizers* or a deeper
variable-depth crop. A proof for unrestricted trees needs, for example,
to charge the locked vacancies to a deficit farther inside the crop,
instead of requiring the smaller square to recover them on its perimeter.

```
python3 -B -m analysis.research_program.crop_end_coupling
(cd lean && lake env lean GridGraphs/Geometry/CropEndCoupling.lean)
```
