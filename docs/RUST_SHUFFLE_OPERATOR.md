# Boundary-shuffle operator inside the random sampler

## Result

The operator is implemented, tested, and available as an **opt-in** sampler
variant. It is fast and recovers both recorded development gains, but the
frozen fresh-input benchmark found **no additional success**:

- Baseline: **5/8** reached score 77.
- Baseline plus operator: **5/8**, on exactly the same inputs.
- All ten successful arms reached their targets through ordinary random
  moves, not the operator.
- The paired successful arms reached the same witnesses at exactly the same
  mutation iteration counts.

The default sampler remains unchanged. These findings do not support enabling
this particular best-board stagnation trigger by default.

## Candidate geometry and exact checks

`src/boundary_shuffle.rs` searches the following specified class. Let m be
an interior U vertex with opposite preserved neighbors `m-axis` and `m+axis`.
Delete those two F vertices. For both perpendicular signs and both axial
ends, try inserting

```text
m + side*perp,
m - side*perp + 2*end*axis,
side,end in {-1,+1}.
```

Both axes are used, covering rotations and reflections. All four removed or
inserted core vertices must be interior; the two insertions must be original
holes. For each feasible two-for-two core, try original boundary holes as
single promotions. A success gains exactly one preserved vertex.

The pattern is only a proposal. The reduced forced forest is rebuilt, both
core insertions are checked with actual component connectivity, and the
boundary insertion is checked against the resulting components. A successful
core and endpoint both pass the separate traversal validator. There is no
assumption of root connectivity or sufficiency of local four-cycle exclusions.

The report distinguishes `found`, `exhausted_candidates`, `test_limit`, and
`time_limit`. Exhaustion concerns only this operator class, not arbitrary
two-for-three exchanges or global optimality. Cutoffs are never cached as
negative results.

Optional diagnostics rebuild each rejected graph and record the length of
one detected cycle. This is not necessarily the shortest cycle or a unique
cause of rejection. Production timing disables this additional work.

## Correctness and development gate

The operator finds a score-77 gain from both recorded pre-gain boards in all
eight square symmetries, without hardcoded gain coordinates. An independent
brute pair enumerator checks its geometry using relative-coordinate dot
products and tests whole final graphs. It agrees on every feasible subset of
a specified twelve-position patch in a 6-square, including positive and
negative cases. Tests also cover empty classes, limits, and the side-15 guard.

Development measurements used 31 previously examined score-76 states:
the two recorded escape paths before their final gains, plus the previous
held-out starts, with exact duplicates removed.

| Probe | Gains found | Median measured call time |
|---|---:|---:|
| Specialized shuffle | 2 | **28.3 microseconds** |
| General two-for-three query | 2 | **12.75 milliseconds** |

The specialized median was about 450 times smaller in this development batch.
These are single-call measurements on development data, not evidence of a
lossless replacement for the general query or a universal speedup. Both
recorded gains passed independent forced-edge trace replay. Diagnostic
rejections included cycles of length 52, confirming that the connectivity
checks cannot be replaced with adjacency checks alone.

Data: [`data/shuffle_development_14/development.json`](../data/shuffle_development_14/development.json),
with per-state probe and general-query records in the same directory.

## Fixed sampler integration

The opt-in variant changes only one aspect of the random sampler:

1. At multiples of 128 mutation iterations, after at least 128 iterations
   without a strict best-score improvement, probe the **best-so-far board**.
2. Allow at most 5,000 tests and five milliseconds per call, clipped to the
   remaining run time.
3. Cache the last completely exhausted board using full board equality.
   Repeated checks of that unchanged best board are skipped.
4. Accept only a complete gain. A feasible neutral core without a boundary
   gain is discarded, leaving the sampler unchanged.

The delete/regrow mutation, downhill acceptance, restart schedule and random
stream are otherwise retained. Failed probes do not consume randomness or
change current/best boards. The cache is not a cache of scores or component
counts: different layouts with the same features remain different keys.

An integration test confirms a real gain can be emitted directly from a
prepared pre-gain board. A separate fixed-iteration test confirms identical
baseline trajectories when probes fail. Cutoff tests confirm that interrupted
queries are not stored as exhausted.

```bash
cargo build --release --bin shuffle_study --bin neutral_plateau
target/release/shuffle_study sample data/corpus_trap_14.txt 123 10000 77 operator
target/release/shuffle_study sample data/corpus_trap_14.txt 123 10000 77 baseline
target/release/shuffle_study probe data/corpus_trap_14.txt 100000 1000 diagnostics
```

The sample arguments are witness, seed, milliseconds, target, and method.
The operator is not automatically enabled by the existing `sample` or
`sample_timed` APIs; the new API is `sample_timed_with_shuffle`.

## Fresh frozen held-outs

The protocol in [`data/shuffle_study_14/README.md`](../data/shuffle_study_14/README.md)
and the selection manifest were saved before any paired trials.

- 24 fresh baseline source runs, seeds 20261201--20261224, 10,000 mutations
  each: twelve unseeded and twelve from explicit parallel rods. All reached
  best score 76 during generation.
- Eight selected score-76 starts, four from each family, with distinct source
  runs and symmetry classes.
- Exclude 300 canonical symmetry classes from recorded prior study states,
  including both development escape paths. This does not establish that the
  new starts differ from every unrecorded state ever visited previously.
- Prefer new component signatures and large minimum symmetry distance to
  prior recorded score-76 boards and previously selected new inputs. This
  is a deliberate diverse selection, not an IID sample.
- Ten seconds per method per input, stopping at the first score at least 77.
  Single-worker methods run serially, with order balanced **within** each
  starting family. Both arms use seed `910000000+1000*case_id`.

No trigger, geometry rule, or sampler policy was retuned after observing these
outcomes. These are different inputs from the earlier neutral-beam study;
the new baseline rate must not be compared with that study's 4/8 as evidence
of an algorithm change.

## Paired results

A dash denotes no target found within the configured ten-second procedure.
Times are seconds to first 77, excluding subsequent artifact writing.

| Case | Source seed | Family | Baseline | With operator | Target mechanism |
|---:|---:|---|---:|---:|---|
| 0 | 20261211 | Unseeded | — | — | None |
| 1 | 20261215 | Parallel | — | — | None |
| 2 | 20261208 | Unseeded | 1.862 | 2.009 | Random, both |
| 3 | 20261222 | Parallel | — | — | None |
| 4 | 20261209 | Unseeded | 3.472 | 3.396 | Random, both |
| 5 | 20261223 | Parallel | 4.125 | 4.321 | Random, both |
| 6 | 20261206 | Unseeded | 3.800 | 3.938 | Random, both |
| 7 | 20261216 | Parallel | 8.241 | 7.984 | Random, both |

The operator arms made **41 calls**, totaling **10,560 tests** and about
**1.32 milliseconds inside the probes**. There were **zero cutoffs**, zero
feasible neutral cores on those checked boards, and zero boundary-promotion
tests. The calls therefore never changed the random trajectory. Successful
paired runs had exactly matching iteration counts and final witnesses.

Probe time excludes bookkeeping and cache checks, so it is not a complete
measurement of wrapper overhead. Wall times varied in both directions; these
single paired runs do not resolve small overhead or population performance.
The substantive result is no observed additional gain, not a demonstrated
speed advantage or disadvantage.

All sixteen final witnesses passed the independent primal-edge checker.
The summary also verifies stored observations and checks trajectory identity
for paired random successes. There were no new operator gain traces in the
held-out runs; development gains remain separately labelled controls.

## Post-hoc snapshot coverage

After freezing the results, the same operator was applied with diagnostics
to all 67 unique score-76 boards in the saved per-score archives and best
snapshots. This is a diagnostic, not a revision of the benchmark outcomes.

It examined 289 contacts and 1,156 geometric shuffle candidates. Only **one**
core was feasible, and none of its five boundary-hole promotions was legal.
No gain was found. Core rejection diagnostics included unit and six-cycles
as well as larger cycles, up to 56 edges.

The archives retain a small number of boards per score, not every visited
state. This does not show that the operator could never help on an unrecorded
state. It does show that the inspected ordinary-sampler snapshots were rarely
prepared for this finishing maneuver, in contrast to the two deliberately
rearranged development states. Repeatedly probing an unchanged exhausted
board cannot fix that lack of preparation.

Data: `posthoc_archive_coverage.json` in the fresh study directory. It is
excluded from paired success counts. No post-hoc trigger change was made.

## Decision and scope

Keep the implementation available as an opt-in proposal, and keep the plain
random sampler as the default. The tested trigger was cheap but did not meet
the adoption criterion of providing additional useful gains.

A future test could apply the probe after intentional neutral rearrangements
or on different candidate states. That is a new integration hypothesis and
needs new evidence; the present data do not justify claiming it works.
Neither failed probes nor this eight-input trial establish an upper bound.
No 17-square optimization or Lean theorem is part of this work.

## Reproduction and files

```bash
target/release/shuffle_study select data/neutral_study_14 NEW_OUTPUT_DIRECTORY
target/release/shuffle_study case NEW_OUTPUT_DIRECTORY/selection.json 0 NEW_OUTPUT_DIRECTORY
# Repeat indices 1--7, with no concurrent timed runs.
target/release/shuffle_study summarize NEW_OUTPUT_DIRECTORY
target/release/shuffle_study archive-coverage NEW_OUTPUT_DIRECTORY
```

The output directory must already exist. Create-new semantics preserve frozen
artifacts. Validation checks source IDs, families, policy parameters, previous
recorded exclusions, scores, symmetry uniqueness and selection distances.

- `src/boundary_shuffle.rs`: geometric proposals, exact checks and diagnostics.
- `src/shuffle_study_data.rs`: fresh selection and validation.
- `src/bin/shuffle_study.rs`: prototype, development and paired-trial commands.
- [`data/shuffle_study_14/selection.json`](../data/shuffle_study_14/selection.json):
  frozen selection, policy and exclusions.
- [`data/shuffle_study_14/summary.json`](../data/shuffle_study_14/summary.json):
  complete paired outcomes and attribution.
- `data/shuffle_study_14/final_boards.audit.json`: independent witness checks.

Frozen artifact hashes:

```text
data/shuffle_study_14/selection.json
7675f916755caac499a4ebcaaa82be1411d0a3d9a2ba7bb5da4f662d12144cc0
data/shuffle_study_14/summary.json
511ca8dba00cae748f1d7e8f3b8a43d24134a69bed8356867aff9dba30c0eb41
data/shuffle_study_14/posthoc_archive_coverage.json
a963dcb59ef7289bcbfca92fba4738c196c2894c5ecfe078788b7db75865f6f3
data/shuffle_development_14/development.json
a9a0f193c4b814fecfa11119a2fd0fab396356a43d96e3837d143bc9d047e9a0
```

```bash
cargo test --lib boundary_shuffle
cargo test --lib shuffle_study_data
cargo test --lib certificate_corpus
cargo test --bin neutral_plateau
```

The pattern tests include all square symmetries of both controls and every
feasible subset of the declared 6-square patch, compared with brute pair
enumeration and full-graph checks. Sampler tests cover replayed gains,
unchanged random streams on failed probes, cutoff-cache behavior, and invalid
intervals. The independent verifier checks both shuffle metadata/geometry
and the actual neutral/gaining graph sequence.
