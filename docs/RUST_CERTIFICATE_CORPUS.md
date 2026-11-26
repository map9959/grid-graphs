# Rust corpus experiment and 17-square audit

The subsequent [neutral-plateau experiment](RUST_NEUTRAL_ESCAPE.md) recovered
77 from the saved score-76 trap through a fully replayed score-preserving
path and one final gain. The trace and final witness are archived in `data/`.

For the component-aware continuation, see
[RUST_EXCHANGE_EXPERIMENT.md](RUST_EXCHANGE_EXPERIMENT.md). It adds blocking
paths, bounded exact repair, neighborhood scans, and seeded/unseeded sampler
comparisons. The documented score-76 trap on side 14 resists every improving
exchange with at most four original-F deletions, despite a known score-77
witness. This is local-optimality evidence, not a global optimum claim.

## What the historical 17-square result actually says

The repository contains a computational exactness claim, separately from the
current Lean interval `110 <= P(17) <= 113`:

- `analysis/frontier_n17_mirror_result.json` reports no feasible pattern with
  at most 178 holes using a row-reflection quotient.
- `analysis/frontier_n17_unmirrored_result.json` reports the same rejection
  without that quotient: 30,053,510,406 generated transitions, 85,066,722 peak
  states, empty state set after vertex 288.
- `analysis/residue_two_affine_17_witness.txt` has 179 holes and 110 preserved
  vertices. The independent primal checker added here validates its forest.

Thus 110 was not merely the best score returned by a beam search. If the
recorded exhaustive computation and its starting checkpoint are correct,
111, 112, and every larger score are excluded. The two searches share their
basic frontier method; they are not independent mathematical algorithms.

The unmirrored source remains byte-for-byte unchanged:

```text
src/bin/search_n17_frontier.rs
4991e07b6ef965a68e8d695e151fdcbf1eab643305444bf66e57eadde0aa3adc
```

This matches the historical result's source SHA-256. No source hash or old
result artifact was rewritten to accommodate the new tests.

### Audit and limits

The reviewed unmirrored algorithm stores the processed dual connectivity
partition and mixed previous/current row mask, retaining minimum hole cost
per equivalent state. Forgotten components must remain represented by a
frontier vertex, with OUT retained throughout. Its rank pruning is safe:
one future selected hole can activate at most its two newly exposed edges,
so at least `ceil(remaining_rank/2)` further holes are necessary. Smaller
cost dominates at the same state because the query is an upper hole budget;
extra holes can only add dual edges.

At side 17 the face identifiers include 256 (OUT). They are `usize`, not
8-bit values. The five-bit labels identify at most 17 *frontier components*,
not global faces. The label region uses 85 bits and the row uses 17 more,
within `u128`. Fixed replays check all 17 columns and every prefix rank bound.

The checkpoint reader checks dimensions, target, record count and length,
canonical labels, row bits, cost, duplicates, and a checksum. This checks
integrity, not completeness of the earlier generated state set. The historic
step-34 checkpoint and executable are not present in this session's
`/tmp/opencode`; a source hash and an empty final frontier cannot reconstruct
the entire search. No new exhaustive 17-square run was performed.

The old small-board brute-force comparison uses the same dual-edge schedule
as its frontier implementation. The new checker instead traverses the
literal primal grid, with an edge iff either endpoint is preserved. Each
connected component must have exactly one fewer edge than vertices. It also
counts F-components, all forced components including isolates, and boundary
deficiency, and checks `3f+r+b+c=n*n+4n`.

New checks compare all 65,536 four-square subsets against both the incremental
primal search kernel and frontier transitions. Every four-square budget is
also checked against that enumeration. The 17-square witness, its eight
symmetries, and three deterministic F-deletion variants per symmetry survive
the frontier transition and rank tests. These are fixed replays, not searches.
The persistent frontier tests are in `src/frontier_primal_tests.rs`, attached
to the maintained pruned executable; the historical unmirrored file stays
unchanged. No solver correctness bug was found in this audit. These checks
do not independently certify the historical negative result.

Literal 17-square replay:

```text
f=110, r=20, b=5, c=2, z=1, forced_edges=287, r+b+c=27.
```

## New bounded experiment

Build:

```bash
cargo build --release --bin certificate_corpus
```

Commands (stdout is JSON; diagnostics/errors go to stderr):

```bash
target/release/certificate_corpus verify analysis/residue_two_affine_17_witness.txt
target/release/certificate_corpus enumerate 4
target/release/certificate_corpus sample 14 10000 8 20260908 data/diagonal_u_14.txt > /tmp/corpus-n14.json
target/release/certificate_corpus check-claim /tmp/corpus-n14.json docs/CORPUS_BUDGET_CLAIM.json
target/release/certificate_corpus check-claim /tmp/corpus-n14.json docs/CORPUS_LEDGER_CLAIM.json
```

- Witness alphabet is `U` for a hole and `.` for a preserved vertex. Blank
  lines and whole-line `#` provenance comments are accepted. Other symbols
  are rejected. `verify` supports fixed witnesses through side 128.
- `sample N ITERATIONS RUNS SEED [WITNESS]` is restricted to side 15 or below.
  It uses two workers, deterministic per-run SplitMix64 seeds, union-by-size
  primal components, exact whole-star insertion tests, delete/regrow moves,
  occasional downhill moves, and periodic restarts. A plateau reservoir
  selects among equally good visited witnesses rather than always returning
  the initial seed. Each run's output is independently checked by traversal.
- This is a heuristic corpus generator: it never reports UNSAT or optimality.
  Seeded runs do not demonstrate recovery of the optimum from scratch.
- `enumerate N` checks every subset, only for sides 1 through 4. Its full
  histogram and optimum apply to that size alone; at most 128 optimal
  witnesses are exported. A claim checked on those exported witnesses does
  not automatically cover the other enumerated subsets.
- Observations contain `n, vertices, f, r, b, c, z, budget, forced_edges`,
  and `target, excess` for residue two, plus all 512 interior 3x3 F-mask
  frequencies. Local masks are row-major, with top-left bit zero; they are
  not symmetry-quotiented or boundary-padded. The target expression in these
  features is `3k*k+7k`, including early sizes where the optimum can be T+1.
- Claims use `constant + sum(coefficient * feature) >= 0`. Coefficients are
  signed integers; evaluation uses checked 128-bit accumulation. Pattern
  features are named `local3:MASK`. Every corpus witness and every stored
  feature is recomputed before checking. Unknown features and inconsistent
  artifacts are errors. A violation returns its witness; a pass is only a
  finite-corpus result. The command reports falsification in JSON, not via
  a nonzero exit status (which is reserved for errors).

`CORPUS_BUDGET_CLAIM.json` tests the candidate `r+b+c>=n`.
`CORPUS_LEDGER_CLAIM.json` checks the known ledger at zero slack.
This implements feature collection and counterexample testing, not automatic
coefficient synthesis or a universally checked discharging certificate.

## Measured smoke experiment

The displayed seeded 14-square command performed 80,000 mutation/regrowth
iterations in about 0.28 seconds wall time (two workers, optimized build,
including JSON output). Its eight runs retained score 77 and exported five
distinct best witnesses. This is a single measured run, not a performance
guarantee or evidence excluding a better configuration.

In-session outputs are `/tmp/opencode/corpus-n14.json`,
`/tmp/opencode/corpus-n4.json`, and `/tmp/opencode/n17-primal-replay.json`.
They are temporary and can be regenerated by the commands above.

Validation commands:

```bash
cargo test --lib certificate_corpus
cargo test --bin certificate_corpus
cargo test --bin search_n17_frontier
cargo test --bin search_n17_frontier_pruned independent_primal_tests
python3 -m unittest analysis.tests.searches.test_frontier_n17_result
```

No optimization above side 15 or Lean build is part of this experiment.
