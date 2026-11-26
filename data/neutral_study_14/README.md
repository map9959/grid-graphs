# Predeclared neutral-search held-out experiment

Completed results are summarized in `summary.json` and
[`docs/RUST_NEUTRAL_GENERALIZATION.md`](../../docs/RUST_NEUTRAL_GENERALIZATION.md).
Files prefixed `posthoc_` are separately labelled follow-ups and are not
included in the frozen eight-case success rates.

Freeze `selection.json` before running any case. Generate 24 fresh source
runs (12 unseeded, 12 from the explicit parallel-rod seed), 10,000 mutations
per run, source seeds 20261001 through 20261024. Select eight score-76 inputs,
four from each family, with distinct source runs and square-symmetry classes.
Exclude the original training witness and all archived trace states under
rotation/reflection. Prefer new component signatures, then large minimum
symmetry distance, breaking ties by source seed. Selection never consults
benchmark results.

For every selected input, give the random sampler and one-for-one neutral
beam method at most ten seconds each, stopping at the first score of at least
77. Run methods serially, alternating their order by case parity. Benchmark
seeds are `900000000 + 1000*case_id`, separate from source-generation seeds.
Disable the certified-radius special case on all held-out neutral arms.

The neutral method keeps beam width 128, depth 12, 100,000 states, and a
200-million-work-node safety limit per beam attempt. It restarts with fresh
tie seeds within the SAME ten-second arm budget when a depth/state/work limit
ends an attempt. At most 64 attempts are allowed. It stops restarting a
seed-independent, empty, unpruned frontier. These are bounded heuristic
failures, not nonexistence certificates. Local probes get at most 500,000
nodes and 250 ms, clipped to remaining time. The random control uses its
existing delete/regrow, downhill, and periodic-restart policy until target
or deadline. No sampler policy is tuned after observing held-out outcomes.

Separately rerun the original input with and without its certified-radius
pruning, using seed 20260908 and ten seconds per arm. This control is excluded
from held-out success rates.

Commands:

```bash
cargo build --release --bin neutral_study --bin neutral_plateau
target/release/neutral_study select data/neutral_study_14
target/release/neutral_study case data/neutral_study_14/selection.json 0 data/neutral_study_14
# Repeat case indices 1 through 7, without concurrent benchmark processes.
target/release/neutral_study control data/neutral_study_14
```

Generated files use create-new semantics and are not overwritten on reruns.
Case outputs include witnesses, full neutral-attempt traces, counters, timing,
and compact summaries. Independently replay all winning neutral traces and
all final board files using `neutral_plateau verify` and `check-witness`.

This is one run per method per selected input, not an IID sample or a
statistical significance claim. Times are measured on the current machine;
deadlines are checked between finite operations and may overrun slightly for
final validation. All searches are on side 14, and the search APIs reject
sides above 15.
