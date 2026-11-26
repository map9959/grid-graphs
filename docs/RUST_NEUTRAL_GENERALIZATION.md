# Neutral escape simplification and held-out comparison

## Conclusions

The proposed finishing-pattern probe has now been implemented and tried
inside the random sampler. See [RUST_SHUFFLE_OPERATOR.md](RUST_SHUFFLE_OPERATOR.md):
it is cheap and recovers the two development gains, but a fresh paired batch
finished 5/8 for both arms with no operator-attributed gain. That follow-up
does not change the frozen results in this note.

1. **The recorded escape has no shorter subsequence in its move vocabulary.**
   All eleven recorded neutral moves are required before the unchanged final
   gain, even when they may be reordered. This is not a globally shortest
   escape-path theorem.
2. **The random baseline did better on the frozen held-outs:** four successes
   versus one for the unpruned one-for-one neutral beam, with ten seconds
   allowed per method per input. Their successes were disjoint.
3. **The original success does not depend on its certified-radius shortcut.**
   Disabling the shortcut recovered the same escape. The shortcut saved only
   about 2.7% of the unpruned work count.
4. **Neutral exploration is a complementary capability, not a replacement
   supported by this batch.** A separate hard-case follow-up identified a
   small closed one-for-one component; sampled two-for-two moves expanded
   beyond it but did not find a gain before their work cap.

The default sampler has not been replaced or retuned to fit these outcomes.
All optimization in this study was on 14x14. No 17-square claim or universal
upper bound changes.

## Exact trace simplification

`src/trace_simplify.rs` searches subsets of the archived eleven neutral moves,
each usable at most once, holding the final two-for-three move fixed. There
are two modes: order-preserving omission, and arbitrary valid reordering.

For a fixed subset of recorded moves, every valid ordering produces the same
board: each coordinate equals its initial occupancy plus the sum of that
subset's additions minus deletions. Move membership must be valid at every
step. Thus a subset mask is a complete state key for this restricted search.
Breadth-first traversal proves the minimum number of retained moves when it
finds a gain; it does not enumerate or assume all permutations feasible.

Both modes examined 16 reachable subset states and required all eleven
neutral moves. A reordered route of the same length might exist; the result
does not assert a unique ordering. A route using other neutral moves, repeated
moves, or a different finishing exchange is outside this minimization.

Artifacts:

- [`neutral_escape_14_simplified_ordered.json`](../data/neutral_escape_14_simplified_ordered.json)
- [`neutral_escape_14_simplified_reordered.json`](../data/neutral_escape_14_simplified_reordered.json)

Both paths passed the separate forced-edge verifier. State/time limits return
the known original route with `minimum_proved=false`, never an unsupported
minimum claim. Tests compare the subset BFS with an unmemoized permutation
search on a small nontrivial example, along with omission and cutoff cases.

```bash
target/release/neutral_study simplify data/neutral_escape_14.json ordered /tmp/ordered.json
target/release/neutral_study simplify data/neutral_escape_14.json reorder /tmp/reordered.json
target/release/neutral_plateau verify data/neutral_escape_14_simplified_reordered.json
```

## Frozen held-out protocol

The protocol was written in [`data/neutral_study_14/README.md`](../data/neutral_study_14/README.md)
and the selection manifest was saved before any paired benchmark ran.

- Generate 24 fresh source runs: 12 unseeded and 12 from explicit score-70
  parallel rods, with seeds 20261001 through 20261024 and 10,000 mutations
  each. All 24 produced best score 76.
- Select eight inputs, four per starting family, with distinct source runs
  and square-symmetry classes. Exclude the original training board and every
  archived trace state under rotation/reflection.
- Prefer previously unrepresented `(c,z,r,b)` signatures, then large minimum
  symmetry distance to the original and previously chosen inputs; break ties
  by source seed. This is a diverse selection, not an IID sample.
- Give each method up to ten seconds per input, stopping at its first score
  of at least 77. Run methods serially and alternate their order by case
  parity. Benchmark seeds are `900000000+1000*case_id`, separate from source
  generation seeds.
- Disable `use_certified_radius` on every held-out neutral attempt, rather
  than relying only on the fixture-identity check.

The neutral arm restarts one-for-one beams with fresh tie seeds within its
single ten-second allowance when depth/state/work limits end an attempt.
It retains beam width 128, depth 12, 100,000 states and a 200-million-node
safety limit **per attempt**. Consequently summed work across attempts may
exceed 200 million while total wall time remains bounded. Local probes retain
500,000 nodes and 250 ms, clipped to remaining time. A seed-independent empty
unpruned frontier terminates early rather than rerunning the same search.
At most 64 attempts are allowed.

The random control retains its delete/regrow, occasional downhill, and
periodic-restart policy. Its new timed wrapper stops on target or deadline;
the untimed sampler's random move sequence is unchanged. The methods' work
counters have different meanings; outcomes and wall budgets are the direct
comparison, not ratios of their raw node/iteration counts.

## Paired results

The entries below are time to first 77. A dash means no 77 was found within
the arm's configured procedure and budget; it is not an infinite runtime or
a nonexistence proof.

| Case | Fresh source seed | Starting family | Random | Neutral, no certified pruning |
|---:|---:|---|---:|---:|
| 0 | 20261012 | Unseeded | **1.13 s** | — |
| 1 | 20261023 | Parallel rods | — | — |
| 2 | 20261001 | Unseeded | — | — |
| 3 | 20261022 | Parallel rods | **6.97 s** | — |
| 4 | 20261008 | Unseeded | **1.51 s** | — |
| 5 | 20261016 | Parallel rods | — | — |
| 6 | 20261006 | Unseeded | — | **2.35 s** |
| 7 | 20261014 | Parallel rods | **7.94 s** | — |

- Random: **4/8**.
- Neutral: **1/8**.
- Both: **0/8**; neither: **3/8**.
- Neutral's case-6 win was on an input where random search timed out.

The held-out neutral escape again uses eleven one-for-one steps followed by
a two-for-three gain. It has twelve missing original F vertices at the final
board. Its full path and independent audit are saved as
[`case_06.escape.json`](../data/neutral_study_14/case_06.escape.json) and
[`case_06.escape.audit.json`](../data/neutral_study_14/case_06.escape.audit.json).

All sixteen final board files passed independent primal-edge cycle checks.
All stored neutral-attempt representative/winning paths passed library
replay; the held-out winning trace and both control escapes also passed the
separate forced-edge verifier. The summary builder checks result scores
against saved witnesses and rejects unexpected input or certified pruning
inside any held-out attempt.

This is one run per method per selected input. It does not establish
population-level superiority, statistical significance, or an optimal hybrid
budget split. Combining their disjoint wins would require more total time;
it is not evidence that a hybrid would achieve 5/8 in the same ten seconds.
All eight selected starts happened to have `c-z=1`: one nontrivial forced
component plus isolates. Their layouts and boundary/component counts differ,
but this batch does not test near-optimal starts with several nontrivial
forced components.
Method order is balanced overall, but because starting families alternate
with case parity, it is confounded with starting family. This protocol does
not isolate family effects or execution-order effects.

## Original-input pruning control

This training-input control is separate from the held-outs. Both arms used
seed 20260908 and a ten-second allowance.

| Certified-radius shortcut | Result | Counted work | Time to target |
|---|---:|---:|---:|
| Disabled | 77, same twelve moves | 51,452,291 | 1.839 s |
| Enabled | 77, same twelve moves | 50,041,310 | 1.739 s |

The shortcut saved 1,410,981 work units, approximately 2.7% of the unpruned
count, and skipped 130 otherwise eligible probe calls. The timing difference
is one paired measurement, not a general speedup estimate. The important
observation is that the original escape survives without the special-case
knowledge. Both complete traces are saved and independently replayed.

## Post-hoc diagnostic: case 1

These follow-ups were chosen after examining the benchmark and are **not
included in its success rates**. No original case output was overwritten.

The original neutral arm stopped after about 0.42 seconds. It had stored and
expanded all 168 states in its one-for-one component, with no beam discards,
but had not selected 147 two-for-three probe locations. Further tie-seed
restarts would reproduce that same frontier and selection.

The first diagnostic set `larger_probe_stride=1`, keeping the original move
class. It completed **all 168 probes of each deletion size 0, 1 and 2**, with
no cutoff, in about 2.32 seconds and 61,047,500 work units. It still found no
gain. The run recorded `frontier_empty`, all 168 states expanded, no beam
discard, and no certified-radius pruning. Thus the limitation was not solely
the original sparse probe schedule. This is a finite component/probe result,
not an exclusion of different neutral move types or larger finishing moves.

A second diagnostic enabled sampled two-for-two neutral moves, retaining
full probes on retained states. It reached 761 stored states, but exhausted
its 200-million-node cap after about 7.22 seconds without a gain. It discarded
107 states at beam selection and had one interrupted probe; it is incomplete.
It does not prove that mixed-move escape is impossible.

The files `posthoc_case_01_full_probes.json` and
`posthoc_case_01_mixed_full_probes.json` retain those distinct outcomes and
their replayed neutral representatives. The default benchmark policy was not
changed to fit these outcomes.

## Practical decision

There is a concrete finishing mechanism shared by the training escape and
the held-out neutral win. Split each final two-for-three gain into its two
interior insertions and its boundary insertion:

| Route | Delete | Interior insertions | Boundary insertion |
|---|---|---|---|
| Training escape | (3,5), (3,7) | (4,6), (2,8) | (10,0) |
| Held-out case 6 | (3,9), (3,11) | (2,8), (4,10) | (13,0) |

Coordinates are `(x,y)`. The interior shuffles are reflected/translated
versions of the same local pattern; the boundary insertions are remote and
different. In each case, omitting that boundary insertion from the verified
final forest gives a feasible score-76 state by heredity. Thus a two-for-two
interior shuffle unlocks a single boundary promotion. This is an exact
description of these two recorded gains, not a claim that the shuffle is
always legal or that every escape has this form.

It suggests a cheaper *candidate* probe: test such shuffles around existing
two-F-neighbor contacts, then test newly available promotions, with full
feasibility checks. That could avoid many arbitrary deletion-pair queries.
It was identified after viewing the study, so it has not been installed as a
default or credited with any of the frozen successes. It needs a new held-out
experiment before claiming a performance improvement.

Keep the random sampler as the default. Neutral exploration has a demonstrated
additional success and produces useful replayable mechanisms, but this batch
does not support replacing random search with the current one-for-one beam.
A future integration should test an actual time-budget split on another
fresh selection, rather than adding the success counts from these two arms.

The remaining neutral failures are not uniformly explained by probe cutoffs:
most cutoff-free beam attempts reached depth limits, and one case had a small
closed one-for-one component. More candidate types, wider/deeper beams, and
larger finishing probes have different costs. This study does not select a
universal fix for them or infer one from a single post-hoc case.

## Code, artifacts, and checks

- `src/trace_simplify.rs`: bounded exact move-subset simplification.
- `src/holdout_study.rs`: symmetry-aware selection, validation, timed neutral
  restart wrapper, and explicit no-certificate controls.
- `src/certificate_corpus.rs`: timed baseline wrapper and stop/target counters.
- `src/bin/neutral_study.rs`: freeze, case, control, summary and labelled
  post-hoc drivers. Outputs use create-new semantics.
- [`data/neutral_study_14/selection.json`](../data/neutral_study_14/selection.json):
  full generation pool, exclusions and chosen inputs.
- [`data/neutral_study_14/summary.json`](../data/neutral_study_14/summary.json):
  paired results, with full per-case records nearby.
- [`data/neutral_study_14/control.summary.json`](../data/neutral_study_14/control.summary.json):
  original-input control, excluded from held-out scores.

```bash
cargo test --lib trace_simplify
cargo test --lib holdout_study
cargo test --lib certificate_corpus
cargo test --lib neutral_search
cargo test --bin neutral_plateau
```

Tests cover nontrivial simplification versus permutation enumeration, valid
cutoff fallbacks, symmetry invariance, training leakage and duplicate-run
rejection, disabled pruning, timed sampler target/deadline semantics, and
independent replay. The saved successful paths remain verification fixtures.

Frozen hashes:

```text
selection.json
406a05ebe36eaa9c74b408b64ee93846a67bfc506021e46747f499a088e0643d
summary.json
d64aaad3cfa30ccc2252931e6674042f5f560a51bde7ed3a831f3e5ae1693b56
case_06.escape.json
197dfc712cff5d08919d624ac5094390e49b7799d9869cb88b66671c49396833
control.summary.json
434767684fb55aaa23777e5befcefab1230361d6ab3bfcba6414b07e785d4756
```

The source-generation manifest is deterministic for the recorded algorithm;
timed-run endpoints and counters can vary with machine speed. Do not overwrite
the frozen artifacts when reproducing: use a new output directory. No Lean
build, new universal theorem, or optimization above side 15 is part of this
study. The historical unmirrored 17-square source retains its original hash.
