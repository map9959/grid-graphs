# n=17 history recovery from committed frontier artifacts

## Conclusion

The committed material is sufficient for a bounded, rigorous backward
over-approximation, but not for recovering actual predecessor summaries for all
20 old-baseline survivors.

Exact reverse transition enumeration proves that persistent unpayable debt was
already positive before the dumped terminal cut for:

| completed step | next cell | survivors forced positive | exceptions by dumped `row_u` |
|---:|---|---:|---|
| 286 | `(16, 14)` | 18/20 | `40960, 40962` |
| 285 | `(16, 13)` | 18/20 | `40960, 40962` |
| 284 | `(16, 12)` | 18/20 | `40960, 40962` |
| 283 | `(16, 11)` | 16/20 | `33792, 33794, 40960, 40962` |

Here "forced" means every transition-valid reverse chain from that dumped
survivor has positive current debt minus exact remaining-final-row active-edge
capacity. This is stronger than choosing one guessed predecessor and does not
assume reverse candidates are forward reachable.

For the two step-286 exceptions, reverse enumeration contains both zero-deficit
and positive-deficit candidates mapping to the same dumped state and minimum
cost (their per-survivor minimum is zero and maximum is two). More generally,
the dump has no field that selects the forward-reachable candidate wherever a
zero-deficit reverse branch occurs. Therefore the available artifact cannot
establish whether those survivors' persistent debt became positive at these
earlier cuts. Resolving that requires an earlier forward layer/checkpoint,
predecessor flags recorded during the original run, or a new forward
reachability computation.

## Committed inputs

At `HEAD` (`2751e1d8c24719a97002cdfc8dc5f61c6d790e09`), the relevant committed
files are:

- `analysis/frontier_n17_u178_step287.json`, SHA-256
  `917cc5605f4fa7e2d2172d1bd90200ad158a6b811d50c0cfc29a1d19c9936018`.
- `analysis/frontier_n17_unmirrored_result.json`, SHA-256
  `48d50c669480b5ae21c7c9e18556cdf32651492aa66e0e10a95d4117de4c1795`.
- `analysis/frontier_n17_u179_replay.json`, SHA-256
  `d33f6ca716c81dc2ecdf50c5773ca2fdb475c47348b2f5874a203bbc7882620d`.
- `analysis/frontier_n17_mirror_result.json` and
  `analysis/test_frontier_n17_result.py`.
- `src/bin/search_n17_frontier_pruned.rs`, SHA-256
  `111c509818d072df1a9da1e954bedc24dd3dee06451fe680db9f3982cc735ca2`.

The 179-U replay is a useful positive control because its explicit witness is
known. It does not identify a prefix for any 178-U survivor.

The unmirrored result names a step-34 checkpoint in `/tmp/opencode`, but does
not commit that checkpoint. Its committed final checkpoint has zero states and
52 bytes, so it carries no earlier layer to replay.

## What the dump preserves

For each of 20 states after 287 cells (through `(16, 14)`), the dump preserves:

- the canonical frontier partition, always `[0, 1, 2]`;
- the mixed current/previous row U mask;
- minimum prefix U cost, always 177;
- diagnostics for the next cell only.

This is enough to reproduce the two-cell terminal rejection and to invert the
local transition relation.

It does not preserve a predecessor state, a predecessor-set hash, a row mask
history, a backpointer, or an aggregate such as "some/all minimum-cost paths
have previously had positive unpayable debt."

## Why source-level replay cannot recover the missing choice

The committed search map has type `FastMap<State, u16>`. On collision,
`extend_chunk` retains only `min(existing_cost, next_cost)`. `dump_states`
serializes only that state and cost. The binary checkpoint format likewise uses
18-byte records: 16 bytes of packed state and 2 bytes of cost. It has no spare
predecessor or flag payload.

Canonical frontier connectivity is intentionally Markovian for deciding future
connectivity. A historical maximum such as persistent unpayable debt is not
Markovian in this key. Once two prefixes merge into the same `State` at the same
minimum cost, neither the dump nor a later reverse transition can distinguish
them.

The source does contain `reverse_predecessors`, but that function enumerates
all states that satisfy one local transition. It does not test whether a state
was in the original forward layer. The bidirectional search regenerates a
forward layer for exactly this reason; doing so near the n=17 peak would repeat
the expensive computation the present investigation is meant to avoid.

## Bounded reverse experiment

`analysis/n17_history_reverse_probe.py` independently applies the exact cell
transition used by the Rust program. For each reverse candidate it forwards the
candidate again and retains it only if the dumped post-state, row mask, and cost
are reproduced exactly. Candidate origins are tracked as a 20-bit set, so the
per-survivor universal claims above remain valid when reverse branches merge.

Command:

```bash
python3 -B analysis/n17_history_reverse_probe.py --depth 4
```

Exact layer sizes and distributions:

| predecessor completed step | candidates | costs | attachment debt | predecessor multiplicity |
|---:|---:|---|---|---|
| 286 | 120 | `177:120` | `2:120` | `6:20` post-states |
| 285 | 720 | `176:72, 177:648` | `2:696, 3:24` | `6:120` |
| 284 | 4,368 | `176:480, 177:3888` | `2:4176, 3:192` | `6:696, 8:24` |
| 283 | 26,592 | `176:3264, 177:23328` | `2:25056, 3:1536` | `6:4176, 8:192` |

The exact unpayable-debt histograms over all candidates are:

| completed step | deficit 0 | deficit 1 | deficit 2 |
|---:|---:|---:|---:|
| 286 | 6 | 108 | 6 |
| 285 | 60 | 642 | 18 |
| 284 | 432 | 3,882 | 54 |
| 283 | 4,176 | 22,254 | 162 |

The capacity calculation is an exact two-state dynamic program over the
unprocessed suffix of the final row. It maximizes active left/up edges under
the remaining U budget and then caps by current attachment debt. Every
independent component merge consumes an active edge, so
`debt - min(debt, maximum_active_edges)` is a safe lower bound on unpayable
debt without inspecting suffix acceptance.

The depth-4 run took 87.09 seconds and 30,968 KiB maximum RSS on this workspace.
Depth 2 took 0.15 seconds and 19,612 KiB. No forward frontier search was run.

## Interpretation

Backward DP can prove universal properties over its transition-valid
over-approximation. That is why the 18/20 and 16/20 earlier-cut statements are
rigorous despite missing reachability data.

Backward DP cannot recover existential history facts for candidates that mix
zero and positive deficit: unreachable reverse branches are indistinguishable
from the actual predecessor. Compact predecessor flags would have solved this
if propagated in the original forward run. At minimum, each state needed an
`ever_positive` may/must pair (or the minimum and maximum historical deficit)
for minimum-cost prefixes. Those bits cannot be reconstructed after projection.

Thus the committed artifact supports partial earlier propagation, but lacks the
necessary data for complete predecessor summaries of all 20 survivors.
