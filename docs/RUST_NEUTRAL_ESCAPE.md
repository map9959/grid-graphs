# Verified neutral escape from the 14-square trap

## Result

The follow-up [simplification and held-out study](RUST_NEUTRAL_GENERALIZATION.md)
found no shorter route using a subset/reordering of these recorded moves and
the same final gain. On eight fresh inputs, the unpruned neutral beam won once
and the random baseline four times, with disjoint wins. The original escape
also reproduces without its certified-radius shortcut. These results support
keeping neutral search as an optional capability, not replacing the baseline.

The saved score-76 witness has a replayed route to score **77**:

**eleven one-for-one neutral exchanges, followed by one two-for-three gain.**

Every completed intermediate state has score 76 and a primal forced forest.
The final state has `f=77, r=14, b=5, c=2, z=1`, and 194 forced edges.
This recovers a previously known attainable score from the nonoptimal input;
it is not a new grid optimum or a shortest-path theorem.

Permanent artifacts:

- [`data/neutral_escape_14.json`](../data/neutral_escape_14.json): complete
  configuration, counters, layer coverage, original board, all move snapshots,
  and final observation.
- [`data/neutral_escape_14.txt`](../data/neutral_escape_14.txt): final witness.
- [`data/neutral_escape_14.audit.json`](../data/neutral_escape_14.audit.json):
  separate forced-edge trace replay.

## The actual sequence

Vertex IDs are zero-based row-major, `v=14*y+x`. All rows and intermediate
scores are saved in the trace artifact.

| Step | Delete current F | Add current U | Resulting score |
|---:|---|---|---:|
| 1 | 86 | 101 | 76 |
| 2 | 75 | 73 | 76 |
| 3 | 103 | 90 | 76 |
| 4 | 120 | 118 | 76 |
| 5 | 108 | 121 | 76 |
| 6 | 38 | 80 | 76 |
| 7 | 78 | 50 | 76 |
| 8 | 104 | 91 | 76 |
| 9 | 10 | 38 | 76 |
| 10 | 44 | 89 | 76 |
| 11 | 87 | 72 | 76 |
| 12 | 73, 101 | 10, 88, 114 | **77** |

The final gain removes `(3,5)` and `(3,7)` and inserts `(10,0)`, `(4,6)`,
and `(2,8)`, in `(x,y)` coordinates. Those additions are not all local to one
small window. Earlier neutral changes make their simultaneous insertion safe.

The final witness omits **nine** of the input's original F vertices and adds
ten original holes. Thus there is no conflict with the completed exclusion
of every direct improvement removing at most four original F vertices.
The minimum number of original F vertices that must be removed to reach a
better final board is therefore bounded between five and nine; this search
does not determine that minimum.
The total number of move operations is not the number of distinct original
vertices changed: the path restores some original vertices and later removes
some newly inserted ones.

## Search and reproduction

```bash
cargo build --release --bin neutral_plateau
target/release/neutral_plateau data/corpus_trap_14.txt one 20260908 60000 200000000 100000 128 12
target/release/neutral_plateau verify data/neutral_escape_14.json
target/release/neutral_plateau reproduce data/neutral_escape_14.json
```

The explicit limits are 60,000 ms, 200,000,000 work nodes, 100,000 stored
states, beam width 128, and neutral depth 12. Search rejects sides above 15.
`reproduce` uses the complete stored configuration, including per-probe
budgets, instead of relying on current CLI defaults. Wall-time fields vary;
time cutoffs can change coverage on slower or busy machines.

For a future successful report, `archive` validates it before saving all
three artifacts and refuses to overwrite existing files:

```bash
target/release/neutral_plateau archive /tmp/new-escape.json data/new_escape
```

The search stores full board bitsets and uses full-key equality for duplicate
detection. It retains parent IDs and exact exchanges. Every newly stored
neutral board is checked by the independent traversal-based `observe` routine,
including its score and ledger. Only completed exchanges are search states;
the intermediate deletion operation inside an exchange need not preserve score.

### Neutral generation and beam selection

Phase A enumerates all feasible one-for-one neighbors of each expanded state,
subject to the global limits. It does not use the first repair returned for
one insertion as a substitute for all neighbors.

Phase B also samples 64 deletion-pair draws per expanded state, deduplicates
those pairs, and enumerates all feasible two-hole insertions for each sampled
pair. It is not an exhaustive two-for-two neighbor generator. Both phases
start from the original witness with fresh state tables and phase budgets.

When a layer exceeds the beam width, roughly one third of slots favor distance
from the original F set, one third cycle through `(c,z,r,b)` shape groups, and
the rest use a deterministic seeded layout ordering. These are heuristics.
In particular `r+b+c` is constant on a fixed-score plateau and is not used as
a progress objective.

The visited table includes beam-discarded states; rediscovering such a state
does not reintroduce it. Reports retain beam-discard counts, partial expansion
counts, depth limits, state limits, probe cutoffs, and time/work limits.
`frontier_empty` alone is not a proof that no escape exists. No negative
outcome from this bounded beam implementation is a global plateau theorem.

### Improvement probes and certified distance pruning

The search checks single additions and one-for-two probes where eligible.
Two-for-three probes are attempted on a deterministic one-in-eight subset
of retained state IDs. Each probe has its own work cap and 250 ms time cap,
both clipped to the remaining global phase allowance. All probe work counts
toward the global node budget.

For the EXACT saved trap, the completed zero-through-four-deletion results
justify skipping a probe with j further deletions whenever `missing+j<=4`.
Here `missing` is measured from the original board, not from move depth.
The configuration must match the saved fixture's actual preserved set; this
pruning is disabled on all other inputs, including merely similar patterns.
The report records this premise and its source artifact.

The successful run used a 500,000-node cap per selected probe. Cutoff probes
are never converted to negative conclusions. The last gain was found by a
two-for-three probe, so the path terminates at neutral depth 11 with twelve
total exchanges.

## Measured runs and the useful correction

The initial pilot used only 20,000 nodes per local probe. Its selected larger
probes all hit that cap, despite substantial unused global budget. That was
a reason to increase the local allocation, not evidence against an escape.
The revised run kept every agreed overall phase limit unchanged.

| Run | Per-probe cap | States stored | Work nodes | Probe cutoffs | Seconds | Outcome |
|---|---:|---:|---:|---:|---:|---|
| A, one-for-one pilot | 20,000 | 5,960 | 19,718,488 | 122 | 0.845 | Depth 12; no escape found |
| B, mixed pilot | 20,000 | 6,937 | 29,890,049 | 137 | 1.241 | Depth 12; no escape found |
| A, completed-probe allocation | 500,000 | 5,644 | 50,041,310 | **0** | **1.858** | **Escape to 77** |

The successful run expanded 847 states and discarded 3,898 generated states
at earlier beam selections. It made 779 single-addition probes, 808 one-for-two
probes, and 101 two-for-three probes. No phase time, state, work, or depth
limit was hit before success. Because A found an escape, a revised B run was
unnecessary and was not performed.

This result does not show that the beam path is shortest, that mixed moves
are worse, or that a larger corpus has been exhausted. It does show that
completing selected improvement probes mattered more here than increasing
the number or depth of sampled states.

## Independent trace checks

The library replays the complete trace from scratch, checks move membership
and distinctness, validates every forced graph with `observe`, and compares
every stored snapshot and original-distance count.

The binary verifier separately enumerates literal primal edges and checks
acyclicity by endpoint union. It does not use the search's whole-star insertion
routine, its neighbor-generation logic, or its BFS feasibility implementation.
It confirms eleven neutral steps followed by the one gain. The original input
and each intermediate graph have score 76; the endpoint has score 77.

The archived witness also passes the existing `certificate_corpus verify`
command. The fixed trace is a regression fixture for both replay methods.
A `reproduce` run regenerated identical moves, states, layers, and work
counters. Elapsed time varies. Older archives default the later explicit
`use_certified_radius` configuration field to true, preserving their original
pruning semantics.

```bash
cargo test --lib neutral_search
cargo test --bin neutral_plateau
target/release/certificate_corpus verify data/neutral_escape_14.txt
```

Tests include complete one-for-one neighbor comparisons on all feasible
3-square boards, a complete sampled-pair small-board control, duplicate
handling, beam/state/depth/time/work limits, identity-bound pruning, corrupt
trace rejection, and the actual archived escape. The separate edge checker
was compared with the primal validator on all 65,536 four-square subsets.

## Artifact hashes

```text
input data/corpus_trap_14.txt
08d0408b293ec53fceabe69f4d4dd27b59c1348dd902e47786ea89f9c5429e91
trace data/neutral_escape_14.json
63b9999b34b53a4d89a53c901b61b4f89b740f481ba6704a6b958f07e5feb17e
witness data/neutral_escape_14.txt
9ee0294d62aa8fb9c23ac1263ebecd329dccefb4d55639b5f3da523eef5776db
audit data/neutral_escape_14.audit.json
a3e253402839c367d5ceeb246bbe802ce108165183b6757a80d75a427810a4d6
```

The pilot reports remain at `/tmp/opencode/neutral-n14-one.json` and
`/tmp/opencode/neutral-n14-mixed.json`. Their configurations can be rerun with
`reproduce` while those temporary files are present. The successful full report
is archived byte-for-byte from `/tmp/opencode/neutral-n14-one-full-probes.json`.

All exploration was on the 14-square. No 17-square optimization, change to the
historical unmirrored source, new universal upper bound, or Lean theorem is
claimed by this experiment.
