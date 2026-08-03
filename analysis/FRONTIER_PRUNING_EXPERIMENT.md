# Frontier Pruning Experiment

`src/bin/search_n17_frontier_pruned.rs` is an isolated copy of the exact
frontier solver with selectable experimental pruning at completed row
boundaries:

- `mirror`: identify a state with its left-right reflection.
- `geometry`: bound future rank gain by the maximum possible number of future
  U-U edges, `2b-ceil(b/n)`, for a remaining budget of `b` U vertices.
- `closure`: add every dual edge that could possibly occur in the unprocessed
  rows, ignoring the U budget, and reject states that still cannot connect.
- `all`: apply mirror, geometry, and closure in that order.

All modes retain complete frontier partitions and exact minimum U costs. They
agree with exhaustive search for every target through `n=3`, and they return
the known exact minima at `n=8` and `n=12`.

## n=12 Benchmark

Release-mode command shape:

```text
target/release/search_n17_frontier_pruned --n 12 --u-count 86 --pruning MODE
```

Results on the same machine:

| mode | minimum U | peak states | transitions | elapsed | peak RSS | row-boundary removals |
|---|---:|---:|---:|---:|---:|---:|
| none | 86 | 309,484 | 48,653,376 | 20.818s | 71.2 MiB | 0 |
| mirror | 86 | 169,605 | 27,420,644 | 7.471s | 46.5 MiB | 304,251 merges |
| geometry | 86 | 309,457 | 48,427,470 | 21.875s | 70.9 MiB | 55,714 prunes |
| closure | 86 | 309,484 | 48,653,376 | 20.433s | 70.1 MiB | 0 prunes |
| all | 86 | 169,605 | 27,284,312 | 7.945s | 39.7 MiB | 304,251 merges, 27,963 geometry prunes |

The mirror quotient reduces peak states by 45.2%, transitions by 43.6%, wall
time by 64.1%, and peak RSS by 34.8%. Geometry alone removes only 0.46% of
transitions and is slower than the baseline. Adding it to mirror removes a
further 0.50% of transitions but is slower than mirror alone. The optimistic
closure test removes no states; the existing retired-component rule already
detects all such failures by the next row boundary in these controls.

The useful result is therefore the row-boundary mirror quotient. The other two
pruners should remain experimental unless a sharper formulation changes their
cost-benefit ratio.

## n=17 Global Result

The exact mirror mode was run globally at the former 178-U target:

```text
target/release/search_n17_frontier_pruned --n 17 --u-count 178 --pruning mirror --progress
```

It returned `UNSAT` after 6,824.946 seconds with 45,898,352 peak states,
16,359,946,462 generated transitions, 126,288,370 cumulative mirror merges, and
8,784,308 KiB peak RSS. The state set became empty at step 288 of 289.

Because dual connectivity is monotone under adding U vertices, retaining only
the minimum U cost for each structural state decides existence at or below the
target. The result therefore rules out every 178-U pattern globally. Together
with the independently validated connected 179-U construction, the exact
minimum is 179 and `P(17,17)=110`. Machine-readable run metadata and source
hashes are in `frontier_n17_mirror_result.json`.
