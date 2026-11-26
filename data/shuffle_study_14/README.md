# Predeclared random-sampler/operator comparison

Completed results are in `summary.json` and
[`docs/RUST_SHUFFLE_OPERATOR.md`](../../docs/RUST_SHUFFLE_OPERATOR.md).
The file `posthoc_archive_coverage.json` is separately labelled and does not
change the paired outcomes or the predeclared policy below.

Freeze `selection.json` before running any paired trial. Generate 24 fresh
baseline source runs (12 unseeded, 12 from the explicit parallel rods), with
10,000 mutations each and seeds 20261201 through 20261224. Choose eight
score-76 inputs, four per family, with distinct source runs and square-symmetry
classes. Exclude all recorded row states in the previous neutral study and
the original training trace, including all development inputs for this probe.
This does not promise disjointness from every unrecorded state visited in
earlier searches.

Selection prefers new `(r,b,c,z)` signatures within the selected set, then
large minimum symmetry distance to prior score-76 records and previously
selected inputs, with source-seed tie breaking. It does not consult paired
trial outcomes. The selection is diverse and deliberate, not an IID sample.

Give each method ten seconds per input and stop at the first score of at
least 77. Run single-worker methods serially. Seeds are `910000000+1000*id`
for both methods. Baseline runs first on cases 0,1,4,5; the variant runs first
on 2,3,6,7. Thus order is balanced within both source families.

The only sampler change is an optional probe of its best-so-far board:

- Check at multiples of 128 mutation iterations, after at least 128 iterations
  without a strict best-score improvement.
- Try the contact-centered interior shuffle in every rotation/reflection,
  then test original boundary holes for a single promotion.
- Cap a call at 5,000 tests and 5 ms, clipped to the remaining arm time.
- Cache the last fully exhausted board by full equality, not hash alone.
  Cutoff results are not cached as negatives.
- Accept only a complete gain, not an unsuccessful neutral shuffle. Failed
  probes leave the state and random-number stream unchanged.
- Preserve delete/regrow, downhill acceptance, and restart rules otherwise.

All probe time is charged to the variant's ten-second budget. No certified
radius pruning is used by either sampler. The baseline remains the default;
no trigger or pattern change is made after seeing held-out outcomes.

```bash
cargo build --release --bin shuffle_study --bin neutral_plateau
target/release/shuffle_study select data/neutral_study_14 data/shuffle_study_14
target/release/shuffle_study case data/shuffle_study_14/selection.json 0 data/shuffle_study_14
# Repeat indices 1 through 7, without concurrent timed trials.
```

Record time to target, iteration count, probe calls/cost/cutoffs, and whether
the target came directly from the operator or a random candidate. Preserve
each winning board and every operator exchange. Independently replay all
final boards and operator gain traces after timing finishes.

One paired run per selected input provides descriptive engineering evidence,
not a universal performance or optimality theorem. All optimization stays
on side 14; search APIs reject sides above 15.
