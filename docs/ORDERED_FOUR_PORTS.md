# Four ordered connections per cut: the budget can survive

This is the same north-isolate, one-gap relaxation as the
[three-port test](ORDERED_TWO_PORTS.md#extension-to-three-ordered-hops),
with the cutoff increased to **four on each cut**. It tracks the order,
row phase, hop type and rooted partition of up to four connections,
plus the two rim masks at each end of the seam. Changing the cutoff
changes the graph. Gluing a column to a prefix must not close a cycle,
join two teeth or leave an unrooted component behind a closed cut.

The exact terminal bitset now contains the equality price on both axes.
Some checks from the direct forward computation (`t=0..12` all pass):

| side | target | minimum | number of distinct deficits | maximum | target bit set? |
|---:|---:|---:|---:|---:|:---:|
| 119 | 198 | 144 | 160 | 327 | yes |
| 161 | 270 | 186 | 249 | 456 | yes |
| 203 | 342 | 228 | 334 | 585 | yes |
| 623 | 1,062 | 648 | 1,168 | 1,839 | yes |

The bitset need not be an interval. A bit at `D` means some path starts
and ends on an empty cut and accumulates **exactly** `D` from allowed
column costs. A second evaluation factors out the east fringe: for each
possible bulk exit it first computes the exact suffix costs, then adds
them to that state's prefix costs. The two evaluations agree on the
table. Of 5,959 (axis 1) and 5,294 (axis 2) reachable bulk interfaces,
144 on each axis can reach the east end. No generated board CNFs are
used.

### Why this is not just a finite run of passing budgets

`four_port_pump.py` looks for a path containing **two insertion sites**.
It enumerates small closed walks in the live bulk graph and records
the precise interfaces at which each walk can start and finish. A
second exact-price transfer carries two flags; its equality paths
must visit both required kinds of interface on the *same* path. The
east suffix must still close at exactly the requested deficit.

The certificate uses a three-column walk costing 18 and a one-column
walk costing 3. For each of `t=0,1,2` an equality path visits both
kinds of site. Insert ten copies of the first walk at its site and
twelve copies of the second at its own site. This adds **42 bulk
columns and 216 deficit**, precisely the increments for `t → t+3`.
Both sites are still available after the insertion; iteration proves
membership for all `t`, without requiring the original path to be
periodic. The induction arithmetic is checked in `pump_budget` in
[`OrderedCutBound.lean`](../lean/GridGraphs/Geometry/OrderedCutBound.lean).

The fourth contact can neither be dropped nor identified with another
contact. As a check, `four_port_glue_audit` constructs an undirected
multigraph with a node per local tree and prefix class. It counts
teeth and edges in each connected component and traces outgoing class
identities by graph traversal. For the charts at offsets `0,-4,+5` on
both axes it agrees with the transfer on all 11,649 distinct gluing
inputs involving a fourth port (7,136 illegal and 4,513 legal).

Together with the three-port exclusion, this identifies four as the
smallest per-cut cap permitting the exact budget **in this relaxation**.
An accepting path is **not a spanning-tree witness**. Different column
witnesses may put corresponding hops at different absolute heights
with the same row phase, and need not use the same transverse length.
The two-axis calculations are separate, not a joint realization. In
particular, even at sizes where equality is independently known to be
impossible this relaxation can pay the equality budget. The result
does not change any unrestricted bound on `P(n,n)`.

The [fixed-height side-623 test](ABSOLUTE_PORTS_623.md) pairs the true
absolute rows, and replays the resulting forest and the extra edges
that arise when physically superimposing the center marks.

```
export PYTHONPATH=target/pb-python
python3 -B -m analysis.research_program.four_port_glue_audit
python3 -B -m analysis.research_program.three_port_square 1 4
python3 -B -m analysis.research_program.three_port_square 2 4
```
