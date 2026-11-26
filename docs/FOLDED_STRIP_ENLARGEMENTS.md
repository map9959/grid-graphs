# Which side-623 exclusions survive arbitrary enlargement?

**Two gaps: all of them.** No square of side `623+42t`, `t≥0`,
attains the exceptional upper bound with two gaps. **One gap: only
part of the exclusion transfers.** In the north-isolate chart, axis 2
is reduced to the twelve isolate distances `5,11,...,71`; on axis 1
the even isolate indices `2,4,...,56` are excluded. These are necessary
conditions from the independent-length test. The subsequent
[synchronized-front proof](SYNCHRONIZED_FRONT.md) eliminates all twelve
distances on both axes for `k≥207`.

## What is allowed in an insertion

Use the physical plaquette tables, common masks and strip forest
partitions of [the fixed-size proof](UNCAPPED_ONE_GAP_623.md). Bond
`g` denotes the transition between tile columns `g` and `g+1` (or
between the corresponding tile rows). Replacing this one bond by
`1+m` bonds inserts `m` tiles, **not** `m` copies of the old tile
mask. Each occurrence is allowed the entire local plaquette domain.

* Along a strip, close its actual transition graph: a node contains
  the transverse tile masks and the complete labeled partition of the
  frontier, including the root and open-side flags. Every additional
  tile uses the physical edge insertion and cycle/retirement checks.
  The outgoing node need not equal the incoming node. In the exclusion
  tests the extra length is *any nonnegative integer*. Multiple
  insertion sites and different strips may choose lengths independently.
* Project supports for an expandable bond from **all positions** in
  all accepting runs there. Counting just the first or last transition
  would incorrectly delete masks in the interior of an insertion.
  Rust marks forward-reachable and suffix-co-reachable arcs. Python
  instead closes the two half-forests independently on opposite sides
  of a proposed transition, then tests their physical join. For a
  single expandable bond the two half-lengths may be added freely.
* Transversely, a width-two strip over an expandable bond can be
  applied to every occurrence of that bond. A width-three strip on
  consecutive base bonds still exists at their physical interface.
  At an insertion boundary its restrictions on the nonrepeated bond
  are necessary, but its restriction on the *particular neighboring
  occurrence* of a repeated bond need not hold for the other copies.
  Do not intersect the repeated domain with that restriction. Thus
  failure of an entire such strip is conclusive, but local support is
  not evidence of a globally consistent forest.

The alternative phase test gives each of fourteen successive bond
positions its own domain and permits any number of further **blocks**
of fourteen. Only the position within a block repeats. No two visits
are required to choose the same mask or component partition. The
single-bond, arbitrary-length test already suffices for the exclusions
below.

**Positive control.** In a synthetic north strip the left and right
lips are `A`, and the gap permits `A→B→0→A` only on the top tile row
(`A=2`, `B=128`; teeth are physically separated). Ordinary adjacency
alone cannot connect the lips. A gap of length `1+14s` can, but a gap
of length `1+3s` cannot. The replay accepts the former and rejects the
latter. This checks both the length phase and retention of nonconstant
interior transitions in the projected supports.

## The two-gap cover

Use the [ordinary bridge and end-range reductions](CORE_413_UNIFORM.md).
Write `k=207+14t`, `d=2+3q`. The two distances `d` and `n-1-d` must
both be at least 308. Set

```
q₀ = min(q,104)           (102, 103 or 104)
a  = q-q₀                 b = 14t-a .
```

Both `a` and `b` are nonnegative. Starting from base exit `q₀`,
insert `a` columns at bond 8, `b` at bond 198 and `a+b` rows at
bond 8. This gives precisely the actual size and exit, including cases
where one or both horizontal insertions vanish. The exit's root
attachment is omitted only at its designated physical site; it is
never copied into an insertion.

Why the local tables transfer: cuts 8 and 198 are in the homogeneous
coordinate range and separated from every base exit and both corner
halos. Inside an inserted band, local stencil types depend only on
coordinates modulo three in the enlarged direction. A tile displacement
is three physical sites. Outside the band the clipped coordinates
relative to a nearby end stay unchanged. In a boundary box, inserting
on a straight perimeter stretch subdivides the same clean path: the
frame bits and directions towards NW or the exit are unchanged. In a
box meeting the exit, the exit and its halo translate together. These
facts apply independently in both coordinates, including at band
intersections. Thus each physical occurrence uses the table for its
folded plaquette. As a check the audit also compares the actual box
keys (including reflected charge types, perimeter parents, defect
guards and axis filters) at **every** position for insertions
`(a,b)=(0,0),(0,14),(14,0),(5,9)` on every base exit.

| base exit `d₀` | base tile `q₀` | empty width-three vertical strip starts at |
|---:|---:|---:|
| 308 | 102 | 101 |
| 311 | 103 | 102 |
| 314 | 104 | 103 |

Both implementations obtained the same empty strips, *with the
insertion closures active*. A true enlarged witness would survive
every support deletion, so none exists. The 35 distinct local
two-gap catalogue covers were freshly checked by `drat-trim`; the
strip contradiction itself is finite-state exhaustion, not a SAT
timeout. In conjunction with the already solved smaller sides this
removes two gaps as a route to equality on the exceptional progression.

## One gap: a partial transfer and a failed full transfer

The following tests use a smaller homogeneous base, `k₀=81`. Keep
the vertical insertion at bond 8 and write `q` for the isolate index
on the enlarged board (`d=2+3q`).

* On axis 2, the singleton base `q₀=24` was empty with freely many
  extra columns at **both** 8 and 72. This covers `q≥24` and
  `k-q≥57`: insert `q-24` west and `k-q-57` east.
* For the remaining `q≥24` put `q₀=81-(k-q)`. It belongs to
  `25..79`. Allow the **union** of these base isolates and insert
  `k-81` columns at bond 8. This is also empty. In both tests the
  first empty strip was horizontal, width two, starting at row 3.
* For each even `q` through 22 on axis 2, and through 56 on axis 1,
  keep the isolate fixed and insert at bond 72 to its east. Every
  one of these unrestricted-length tests is empty. The gaps are far
  enough from the isolate and axis fringes for the clipped catalogue
  types to transfer. This establishes the announced restrictions for
  the exceptional family at `k≥81`.

In contrast, rebase at 623, keep `q=1` (distance 5), and put
fourteen-phase insertions starting at horizontal bond 180 and vertical
bond 8. On **both** axes the width-two and width-three passes reach
a **nonempty joint fixed point**. The two independent programs agree.
This is not `UNKNOWN` treated as an exclusion, and it is not an
equality witness. Different strips may still require different
extension lengths or incompatible interiors. For example, even if
there are exactly `t` additional blocks in each direction, the local
per-plaquette minimum charges at this fixed point sum to only
`1292+84t` in units of `4D`, versus the equality budget `4248+288t`.
No matching lower and upper formula for this one-gap tail follows.

```
PYTHONPATH=target/pb-python python3 -B -u -m analysis.research_program.folded_strip_audit --drat
(cd lean && lake env lean GridGraphs/Geometry/FoldedStripCover.lean)
```

Lean checks reachability preservation, clipped bond tags and the
exit/isolate cover arithmetic. It does not certify the enumerated DP
transitions. No growing square-board proof files are needed.
