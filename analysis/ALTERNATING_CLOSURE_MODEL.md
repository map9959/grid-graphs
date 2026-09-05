# One-Copy Grouped Alternating-Closure Model

`alternating_closure_grid_trees.py` exhaustively checks every `3 x 3` and
`4 x 4` spanning tree, both shore axes, every admissible contour-occurrence to
spatial-gap bijection, and every subset of the resulting grouped Hall source.

## Correct Source Ledger

The old checker used each later contact with a raw component as a Hall source.
Those collision leaves are provenance, not independent physical obligations.
The corrected checker constructs one global occurrence-split cotree-dual core,
takes the minimal ancestor hull of the inward collision leaves, and uses:

1. One source for each used split-boundary root.
2. One source for each branch-excess slot of the shared hull.
3. One separately routed source for each outer collision.

Thus the executable identity is `inward leaves = roots + branch excess`.
Continuation edges and bounded faces occur once globally; they are never copied
per raw component.

## Gap Choices

For each raw component, the script computes the spatially consecutive contact
gaps. Ordinary gaps execute Lean's selected unit segment and opposite cell side.
The southwest row-axis and northeast column-axis duplicated-corner transitions
also follow the exact top-else-right and bottom-else-left rules.

Lean reindexes contour collisions to spatial gaps with noncomputable
`Fintype.equivOfCardEq`. There is no canonical executable value to imitate.
The census therefore enumerates every componentwise occurrence-to-gap bijection
and reports both:

- `axis_audits_holding_for_all_gap_choices`
- `axis_audits_holding_for_some_gap_choices`

`gap_choice_count` is the total number of audited bijections across both axes.

## Physical Neighborhoods

Roots first expose their actual split-boundary port. Outer sources start at
their selected gap occurrence. Branch slots start in a distinct physical child
sector and follow the shared parent chain. At a bounded face, the computational
candidate set contains its incident raw physical resources. Reserved exits,
internal tokens, and component representatives trigger alternating owner
displacement; only residual split ports, support-support tree edges, and raw
components enter Hall neighborhoods.

`OUT` is not used as one candidate face. The checker interleaves split vertex
sectors and primal boundary edges in clockwise perimeter order, including both
sectors at each corner. Displacing a reserved root/exit port continues in the
same direction; it does not restart or expose every outer resource. Each of the
clockwise and counterclockwise walks ends at its first free port or first local
cotree, component, or support-support internal-edge occurrence. A boundary
cotree contact enters its bounded face. If an internal/component continuation
later reaches a boundary cotree occurrence, it resumes from the two sectors
adjacent to that occurrence. Thus reservation chains are ordered and every
transition remains labelled by its initiating grouped source.

A used shared-hull root retains its single grouped source occurrence and also
walks inward, opposite the parent orientation, along the unique active chain of
each selected collision leaf below that root. Shared prefixes are visited once
for that occurrence. Every bounded face on those descendant chains offers its
incident raw resources through the same internal-edge, component, owner, and
outer-boundary rules; reverse traversal neither creates a source per leaf nor
changes branch-slot or separately routed outer-source launches.

### Experimental component, internal-edge, and tree-basis continuation

The analysis checker now closes two additional, purely experimental transitions.
When a walk reaches a raw free-component resource, that component is still
counted once when residual or displaces its representative when reserved. The
same source occurrence may then traverse the occupied component and resume at
both adjacent dual faces of every distinct tree-edge contact between the
component and cotree support. Contacts are continuation states, never resources,
and queue deduplication retains the initiating grouped-source occurrence.

When a walk offers an internal tree-edge resource `e`, it still processes `e`
under exactly the existing rule: a residual `e` enters the Hall neighborhood,
while a reserved `e` displaces only its existing matched owner. The initiating
source occurrence may then pass through `e` from the incident dual face where
it arrived to the other incident face. A bounded opposite face applies the
existing cotree/component/resource rules. If the opposite face is `OUT`, the
walk resumes clockwise and counterclockwise at that exact boundary-edge
occurrence under the existing ordered-outer rule. The resource neighborhood is
a set, so returning to `e` through the other face never awards a second copy.

Independently, after reaching either an internal tree edge `e` or a tree-edge
contact `e` of an already reached raw component, the same walk may use every
cotree edge `f` for which the unique tree path between the endpoints of `f`
contains `e`. Equivalently, `e` lies on the fundamental cycle of `T + f`, so
`T - e + f` is a legitimate tree-basis exchange. The contact edge remains a
continuation state rather than an additional resource.

The continuation resumes at the existing one-copy cotree occurrence for `f`
and follows its existing parent direction. The omitted edge `f` is not a new
Hall resource, owner, or copied hull node. Seen-node suppression prevents an
exchange loop from manufacturing repeated resources. Setting `displace=False`
also disables these exchange continuations, preserving the direct-neighborhood
control audit. No Lean theorem currently justifies this experimental closure.

The candidate collection is still an analysis-layer neighborhood, not an
extraction of Lean `FirstOwned` witnesses. The core shortest-parent tie is made
deterministic by the node order. These conventions affect the claimed
neighborhood, but not the corrected one-copy Euler source count.

## Explicit `n = 4` Audit

The former first counterexample has two collision leaves on component `12`, but
its grouped ledger has a reserved root and one separately routed outer source.
Both possible occurrence-to-gap bijections select coordinate edge `(8,9)`.
The tree-basis continuation from internal edge `(5,9)` uses the eligible
omitted edges `(4,8)`, `(6,10)`, and `(7,11)`. Singleton neighborhoods are:

```text
outer selected-gap source -> internal edge (5,9), free port (11,E)
reserved root source      -> internal edge (5,9), free port (11,E)
```

Consequently Hall holds for this audit. This is the regression that prevents a
return to collision-leaf accounting.

A separate two-root columns regression uses the tree encoded in
`test_two_root_reverse_continuation_exposes_internal_edge`. The grouped root at
reserved port `(13,S)` retains one source occurrence while its reverse walk
follows the selected descendant chains and exposes residual internal edge
`(5,9)`. The old outward-only root launch did not contain that edge.

Zero-based spanning-tree census item `T780` is the second former remaining
columns failure. Every grouped source reaches boundary internal edge `(7,11)`
from its bounded incident face. Opposite-face pass-through reaches `OUT`, resumes
the contact-local exterior walk, and exposes free port `(11,E)`. The edge remains
one neighborhood resource. Hall now holds for all six occurrence-to-gap choices
and all source subsets of this audit.

## Exhaustive Results

The checked census is:

| n | trees | axis audits | gap choices | Hall for all choices | Hall for some choices | one axis fails | both axes fail |
|---|---:|---:|---:|---:|---:|---:|---:|
| 3 | 192 | 384 | 393 | 384 | 384 | 0 | 0 |
| 4 | 100,352 | 200,704 | 204,179 | 200,704 | 200,704 | 0 | 0 |

Here an axis fails only when every occurrence-to-gap bijection fails. Both axes
now succeed independently, robustly with respect to the noncomputable gap
reindexing, for all `100,352` trees at `n = 4`. This is finite evidence, not a
proof for arbitrary `n`.

## Random And Targeted Results

For `n = 5..8`, exhaustive tree enumeration is replaced by deterministic
structured combs, tree-basis exchange hill climbs that maximize row- or
column-collision pressure, and uniform Wilson spanning trees. Small grouped
source ledgers enumerate every source subset. Above a configurable threshold,
the checker instead computes an exact bipartite maximum matching. If matching
fails, alternating reachability from unmatched sources recovers and records an
explicit deficient Hall subset.

Gap bijections are treated independently from Hall subsets. Their exact
factorial product is computed without expansion. Every bijection is checked
when that product is at most `--all-gap-limit`; otherwise the checker uses
distinct uniform samples from the componentwise product, reproducibly seeded.

The checked `20260816` campaign used 12 targeted and 32 Wilson trees per size,
both axes, an all-gap limit of 120, 64 sampled choices, and a source-subset
limit of 4:

| n | trees | axes | maximum sources | gap space | tested | all/sample axes | subset/matching axes | failures | seconds |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 5 | 44 | 88 | 4 | 129 | 129 | 88 / 0 | 88 / 0 | 0 | 1.917 |
| 6 | 44 | 88 | 5 | 236 | 236 | 88 / 0 | 87 / 1 | 0 | 2.932 |
| 7 | 44 | 88 | 4 | 132 | 132 | 88 / 0 | 88 / 0 | 0 | 3.744 |
| 8 | 44 | 88 | 6 | 822 | 166 | 87 / 1 | 87 / 1 | 0 | 4.649 |

Thus 351 of 352 axis audits covered every gap bijection. The remaining `n=8`
audit checked 64 reproducible samples from its 720-choice space. No individual
axis failure, and therefore no adaptive-axis counterexample, was found. Full
machine-readable results are in
`alternating_closure_grid_trees_n5_n8.json`. The campaign took 13.24 seconds;
runtime includes targeted tree-basis hill climbing as well as Hall audits.

Reverse-root continuation removed 3 of the preceding 5 failures, internal-edge
opposite-face pass-through removed `T780`, and contact-edge basis exchange
removed the final `T779` failure. In `T779`, reaching the reserved component `11`
also reaches its tree contact `(10,11)`. The legitimate exchanges through omitted
edges `(6,10)`, `(9,10)`, and `(10,14)` continue to face `7`, where the same
source occurrence reaches residual component `12`. The neighborhood therefore
contains component `12` and free ports `(8,W)` and `(14,S)`, exactly three
physical resources for the three-source deficient subset. All six gap choices
now pass, as do all `n = 4` tree/axis audits and source subsets in the declared
model.

The row-axis ledger for the same tree has only one source: the separately
routed outer collision from row demand `3` on component `12`. There is one gap
choice, and alternating continuation routes that source to residual free
component `11`. Hence the row audit has a one-by-one matching and no deficient
subset. The columns obstruction is genuinely directional: changing axes changes
the grouped source ledger from two branch slots plus one root to one outer
source, rather than merely finding a third resource for the same three sources.

## Adaptive-Axis Theorem Target

For every square-grid spanning tree, at least one of the row and column
one-copy grouped-hull models satisfies Hall for every componentwise
occurrence-to-gap bijection. Equivalently, if

```text
defect_axis(T) = max_S (|S| - |N_axis(S)|),
```

then the target is

```text
min(defect_rows(T), defect_columns(T)) = 0.
```

A plausible proving invariant is an **orthogonal escape invariant**. A positive
axis defect should localize, by planar interval uncrossing, to grouped branches
trapped between too few boundary exits. The transverse grid direction crosses
that trapping interval in order. Those crossings should either merge the
transverse source ledger before branching, as in `T779`, or expose distinct
transverse free-component/internal-edge/port resources. Proving an injection
from the trapped branch excess to these ordered transverse crossings would show
that defects in the two axes cannot coexist. The needed statement is geometric
and source-sensitive; the scalar residual ledger cannot prove it because its
component terms cancel independently of axis.

## Historical Approximation

The previous census launched every collision leaf through every omitted edge
incident with its carrier. It passed all `n = 3` audits and reported the explicit
tree above as the first `n = 4` failure with two collision leaves sharing only
`(11,E)`. The functions `historical_collision_hall_balance` and
`historical_closed_region_balance` remain available for reproducing that
comparison, but they are not used by the corrected census.

Run the complete audit with:

```bash
cd analysis
python3 -m unittest test_alternating_closure_grid_trees.py
python3 alternating_closure_grid_trees.py --n 3 --n 4 \
  --output alternating_closure_grid_trees.json
python3 alternating_closure_grid_trees.py --n 5 --n 6 --n 7 --n 8 \
  --random-count 32 --targeted-count 12 --all-gap-limit 120 \
  --sampled-gap-count 64 --subset-limit 4 --seed 20260816 \
  --output alternating_closure_grid_trees_n5_n8.json
```
