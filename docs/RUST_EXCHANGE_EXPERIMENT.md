# Component-aware Rust exchange experiment

## Main finding

**The trap now has a verified neutral escape.** See
[RUST_NEUTRAL_ESCAPE.md](RUST_NEUTRAL_ESCAPE.md): eleven one-for-one neutral
steps followed by a two-for-three gain reach score 77. The final board omits
nine original F vertices, so the completed radius-four exclusion below is
unaffected. This supplies an actual escape path rather than a larger direct
exchange search.

**Four-for-five continuation completed:** the deletion-first search has
now exhausted all 1,282,975 four-deletion sets, with no improvement. A
separate literal-graph traversal audit agreed. The current conclusion is
that every better board must omit at least FIVE original F vertices of the
saved score-76 witness. Details are in the continuations below; earlier
results remain recorded as their original checkpoints.

The sampler's score-76 output on the 14-square is a genuine small-exchange
trap, despite the existing feasible score-77 witness. For the explicit
`data/corpus_trap_14.txt`, the new scans found no improving exchange involving
at most two deletions of original preserved vertices. A separate deletion-first
enumerator confirmed the result. This is a computational local-optimality
statement for one witness, not an optimum claim for the board.

The cycle-guided sampler did not outperform the baseline in the measured
batch. It performed many valid repairs but cost about nine times as much
wall time at equal iteration counts. The baseline remains the default.

## Commands

```bash
cargo build --release --bin certificate_corpus

# Fixed-witness analysis, allowed for the existing 17-square witness.
target/release/certificate_corpus diagnose analysis/residue_two_affine_17_witness.txt > /tmp/n17-diagnostics.json

# Fixed additions are row-major vertex IDs: v=y*n+x, zero based.
target/release/certificate_corpus repair data/corpus_trap_14.txt 3 10000 14 15

# Complete small-exchange scans for the fixed 14-square trap.
target/release/certificate_corpus scan data/corpus_trap_14.txt 1 1 120
target/release/certificate_corpus scan data/corpus_trap_14.txt 2 128 7140
target/release/certificate_corpus scan data/corpus_trap_14.txt 3 512 280840

# Every comparison includes unseeded starts, plus each supplied seed file.
target/release/certificate_corpus compare 14 10000 8 20260910 256 data/diagonal_u_14.txt data/corpus_seed_parallel_14.txt > /tmp/n14-comparison.json
target/release/certificate_corpus summarize /tmp/n14-comparison.json
target/release/certificate_corpus check-claim /tmp/n14-comparison.json docs/CORPUS_LEDGER_CLAIM.json
```

`diagnose` supports fixed witnesses through side 32. `repair`, `scan`, and
`compare` reject sides above 15. No new 17-square repair or optimization was
run. The historical unmirrored frontier source is unchanged and retains its
recorded SHA-256; the results below do not invalidate or independently
reproduce its historical UNSAT computation.

## Exact physical diagnostics

`src/exchange_analysis.rs` constructs the actual primal forced forest,
including isolates. For a proposed promotion v, its new edges lead exactly
to its original U neighbors. If those edges number m and the center plus
their endpoints occupy t original components, the introduced cycle rank is
`m+1-t`.

The output lists those component groups and the original tree paths between
their terminals. For each old path edge it reports every preserved endpoint
that must be deleted to remove the edge:

- An FU edge requires deleting its F endpoint.
- An FF edge requires deleting BOTH F endpoints.
- An edge incident to the promoted vertex cannot be removed this way: the
  promoted vertex keeps it forced.

`single_deletion_path_hits` counts shared coverage of these displayed basis
paths. It is a diagnostic, **not a sufficient repair certificate**. For example,
on `.UU / UUU / .U.`, deleting the top-left preserved vertex cuts all three
displayed paths for a center promotion, but the resulting graph still has
cycles. Exact repair needs all three original F vertices deleted. This is a
regression test against using a cycle-basis hitting set as a feasibility test.

The 17-square replay reproduces the previous result:

```text
component sizes: [288, 1]
isolated vertex: 36 = (2,2)
single-promotion cycle ranks: {1:3, 2:22, 3:154}
legal single promotions: 0
```

## Bounded exact repair

`repair FILE MAX_DELETE MAX_NODES ADD_VERTEX...` searches only deletions of
original F vertices, holding the specified original-hole additions fixed.
Iterative deepening establishes the minimum number of deletions when it
finishes successfully.

At each node the implementation finds a cycle in the **current final forced
graph**. Any successful deletion completion must remove an edge of that cycle.
It branches over every removable edge, deleting all of that edge's current F
endpoints. Edges incident to locked additions are not removable. It then
rebuilds the graph and checks another actual cycle. This is complete for the
stated fixed-addition/deletion problem; it does not just hit the initial basis.

Equivalent deletion states are memoized within each depth. The key need not
contain remaining depth because the same state at that depth has the same
number of original deletions; the memo is reset for each new depth. Final
witnesses also pass the independent traversal-based `observe` checker.

Results distinguish:

- `minimum_found`: all smaller deletion budgets were exhausted.
- `no_repair_within_budget`: all stated deletion depths finished.
- `cutoff`: the node limit interrupted the query. Smaller fully exhausted
  depths are reported separately; this status is not a negative certificate.

`scan FILE ADD_COUNT MAX_NODES_PER_QUERY MAX_QUERIES` enumerates combinations
of exactly ADD_COUNT original holes, allowing up to ADD_COUNT-1 original-F
deletions. ADD_COUNT is restricted to 1, 2, or 3. It stops at the first
improvement or the combination limit. `exhausted_neighborhood` is emitted only
when every combination finished and there were no query cutoffs. An empty
combination domain is explicitly a vacuous completed neighborhood.

## Comparative sampling

The guided policy uses the same random moves and restart schedule as the
baseline, replacing every other non-restart proposal with:

1. Select a hole with low cycle rank among four shuffled candidates.
2. Sometimes select a nearby second hole, avoiding an intrinsically cyclic
   diagonal pair of additions.
3. Search for a minimum repair with at most three deletions and the specified
   per-proposal node budget.
4. Randomly regrow the feasible result. Failed or cutoff queries fall back
   to the baseline mutation, and are reported distinctly in the counters.

It remains heuristic: proposals are sampled, and the exact repair queries
solve only their fixed-addition subproblems. The candidate pool is not a
claim to cover all larger improving exchanges.

Comparison output preserves per-run seeds, initial witnesses, best witnesses,
repair counters, and up to eight distinct visited boards at each score within
two of the **run's observed best**. Those scores are not known distances from
the true optimum. Boards are deduplicated into a replayable feature corpus;
all retained boards are checked independently. The bounded archives are not
uniform samples of the state space. The best witness is always retained
separately, even when its archive band is full.

The new `summarize` command replays every exported corpus witness and produces
compact comparisons. Timing and search counters are summarized, not rerun.

## Measured 14-square experiment

Eight runs per variant, 10,000 iterations per run, two workers, initial seed
20260910, 256 repair nodes per guided proposal. These are equal-iteration,
**not equal-time** comparisons.

| Initial state | Baseline best, all 8 runs | Guided best, all 8 runs | Baseline seconds | Guided seconds |
|---|---:|---:|---:|---:|
| Unseeded | 76 | 76 | 0.316 | 2.882 |
| Known score-77 witness | 77 | 77 | 0.309 | 2.805 |
| Explicit score-70 parallel rods | 76 | 76 | 0.304 | 2.731 |

The comparison exported 1,051 distinct independently replayed observations.
Across the three guided variants there were 119,064 repair attempts:
82,711 successful minimum repairs, 34,671 exhausted queries, and 1,682
cutoffs, using 2,846,017 repair nodes. Successful repairs are not synonymous
with score improvements. No variant found a score above 77.

The 77 seed is present before searching; retaining it does not count as
rediscovering it from scratch. Both other initializations missing 77 is a
concrete limitation of these samplers, not a result against the historical
exhaustive DP. Eight runs do not establish general relative performance.

## Independently checked score-76 trap

`data/corpus_trap_14.txt` is variant 0, run 0's best witness. Its counts are
`f=76, r=15, b=5, c=4, z=3, forced_edges=192`.

| Original-hole additions | Allowed original-F deletions | Completed queries | Search nodes | Cutoffs | Improvement |
|---:|---:|---:|---:|---:|---|
| 1 | 0 | 120 | 120 | 0 | None |
| 2 | 1 | 7,140 | 32,701 | 0 | None |
| 3 | 2 | 280,840 | 4,557,787 | 0 | None |

The pair and triple scans took about 0.15 and 15.8 seconds, respectively.

An independent deletion-first test examines all 2,927 deletion sets of size
zero through two. After each deletion it enumerates increasing sequences of
original-hole additions using the separately tested incremental DSU kernel,
pruning only infeasible prefixes. Feasibility is hereditary, so no valid
completion can extend an infeasible prefix. This opposite-direction check
agrees with the cycle-guided scans (about 0.29 seconds in the debug test run).

Together these checks exclude **any strictly better feasible board differing
from this witness by at most two original-F deletions**: if more additions
gave such a board, selecting only d+1 of those additions would already be a
feasible improvement for d deletions, and the corresponding scan covered it.

This proves neither that three deletions suffice nor that an escape must
make three simultaneous deletions. A sequence of neutral moves can change
the reference configuration. The known 77 witness proves this local trap
is not globally optimal.

## Reproduction and provenance

Persisted inputs:

```text
data/corpus_trap_14.txt
08d0408b293ec53fceabe69f4d4dd27b59c1348dd902e47786ea89f9c5429e91
data/corpus_seed_parallel_14.txt
f778c2a2ce40bd99bc595b126b36d47505192dcf837e5eca974264f52996e5c1
```

Full temporary outputs (regenerate with the commands above):

```text
/tmp/opencode/exchange-n14-comparison-long.json
2be9c79a11d22c9ef06a479a5af56e9217c864e2986d489c1dcc758ea62c02ad
/tmp/opencode/exchange-n14-one-for-two.json
7da785dd33ebd836b12cb73bce4f82d322a65cf65eef6a4027c568da608829dc
/tmp/opencode/exchange-n14-two-for-three.json
9aad5cf3b57bf8a181a2ccacaf69e17c68c13d97ccc0c8dc2b1583a8378d9830
```

The comparison includes wall times, so a rerun need not have the same file
hash. Seeds, witness rows, and algorithmic counts are deterministic for the
same implementation. The diagnostic output is
`/tmp/opencode/exchange-n17-diagnostics.json`; compact comparison output is
`/tmp/opencode/exchange-n14-summary.json`.

Targeted checks:

```bash
cargo test --lib certificate_corpus
cargo test --lib exchange_analysis
cargo test --bin certificate_corpus
```

They include exhaustive 3-square fixed-addition/minimum-deletion comparisons,
the cycle-basis counterexample, cutoff semantics, independent deletion-first
verification of the 14-square trap, fixed 17-square diagnostics, and the
existing exhaustive 4-square primal-kernel checks. These are Rust checks,
not new Lean theorems or an unconditional grid upper bound.

## Completed three-for-four search

The new `src/deletion_search.rs` enumerates exactly d-element subsets of
original F (originally d in 0..=3, now extended to 0..=4), then searches for d+1 jointly feasible original-hole
additions. It is exposed by:

```bash
target/release/certificate_corpus delete-first data/corpus_trap_14.txt 3 100000000 60000
```

The last two arguments are an overall work-node limit and a time limit in
milliseconds. One work node is a deletion-set evaluation, an initial-hole
eligibility test, or an insertion-prefix extension test. Limits are checked
before each such operation. `node_limit` and `time_limit` outcomes are not
negative certificates; `exhausted_neighborhood` means every stated deletion
set and all its candidate additions were covered. Searches above side 15
are rejected.

Immediately after deleting a set, any individually illegal hole can be
discarded: later insertions only add forced edges, so its existing cycle
cannot disappear. Increasing-index insertion prefixes enumerate every
remaining subset once. Each prefix must remain feasible. The implementation
uses union-by-size component tests without rebuilding a graph for every
candidate tuple. A discovered final witness must pass the separate literal
graph traversal and gain exactly one preserved vertex.

### Outcome

All **70,300** deletion triples completed in approximately **0.33 seconds**,
using **8,508,729 work nodes**, below the limits of 100 million nodes and
60 seconds. No four-addition completion was feasible. The saved summary is
[`data/corpus_trap_14_three_for_four.json`](../data/corpus_trap_14_three_for_four.json),
including input/source hashes and the full temporary output's hash.

The number of individually legal holes after deletion had this distribution:

| Legal holes | Deletion triples |
|---:|---:|
| 0 | 40,177 |
| 1 | 17,871 |
| 2 | 8,707 |
| 3 | 2,682 |
| 4 | 738 |
| 5 | 116 |
| 6 | 9 |

Only **863** triples therefore needed a joint four-addition check. Having
four or more individually legal holes was not sufficient: their forced
edges were incompatible in every case.

### Cross-checks and interpretation

- The new search agrees with exhaustive final-board enumeration on every
  feasible 3-square input, for deletion sizes zero through three.
- Explicit tests distinguish node exhaustion, time exhaustion, and vacuous
  empty neighborhoods.
- A separate unfiltered oracle revisits every one of the 70,300 triples,
  testing all original-hole insertion prefixes with the original mutating
  DSU insertion routine. It never calls the new `can_insert` prefilter.
  That check passed in about 6.76 seconds in the debug test build. It shares
  the previously tested DSU representation, so this is a separate enumeration
  check, not a wholly independent graph implementation.

```bash
cargo test --lib deletion_search
cargo test --lib certificate_corpus::tests::trap_14_three_deletions_have_no_gain_without_candidate_prefilter
```

Combined with the earlier zero-, one-, and two-deletion checks, this excludes
every improving board that removes at most three original F vertices. If
more than d+1 additions produced a gain after d deletions, their d+1-element
subset would already be a feasible gain, by heredity, and was covered.

The known score-77 board remains attainable by a larger change. This result
does not assert that four deletions suffice, nor that a path through neutral
configurations must temporarily lose four vertices. No new 17-square search,
unconditional upper bound, or Lean result is part of this continuation.

## Completed four-for-five search

The next bounded run extended d to four, with a 200-million-work-node and
60-second limit:

```bash
cargo build --release --bin certificate_corpus --bin audit_deletion_four
target/release/certificate_corpus delete-first data/corpus_trap_14.txt 4 200000000 60000
target/release/audit_deletion_four data/corpus_trap_14.txt 200000000 60000
```

The primary search exhausted **all 1,282,975 deletion quadruples** with no
improvement. It used **155,302,571 work nodes** in approximately **5.32 seconds**;
neither limit was reached. The persisted result and provenance are in
[`data/corpus_trap_14_four_for_five.json`](../data/corpus_trap_14_four_for_five.json).

| Initially legal holes after deletion | Deletion quadruples |
|---:|---:|
| 0 | 494,930 |
| 1 | 370,979 |
| 2 | 238,848 |
| 3 | 113,647 |
| 4 | 46,605 |
| 5 | 14,158 |
| 6 | 3,249 |
| 7 | 515 |
| 8 | 42 |
| 9 | 2 |

Only 17,966 quadruples left at least five individually legal holes. There
were 47,071 five-subsets of those eligible holes in total. None was jointly
feasible.

### Separate traversal audit

`src/bin/audit_deletion_four.rs` does not use `Forest`, `can_insert`,
incremental DSU insertion, or the primary combination cursor. It uses:

1. Four explicit loops for the original-F deletion choices.
2. An independently constructed grid adjacency list and BFS of each reduced
   forced graph to obtain actual component labels.
3. Those labels to identify individually legal holes. The same mathematical
   monotonicity argument justifies excluding illegal holes, but the component
   computation is separate from the primary implementation.
4. Five explicit loops over eligible-hole subsets. For every subset it
   rebuilds and traverses the entire resulting forced graph, checking
   `edges + components = vertices`, with no insertion-prefix pruning.

The audit completed all deletion sets and all **47,071 candidate five-subsets**
in approximately **10.90 seconds**, using **155,287,046 work nodes**. It agreed
on the complete eligibility histogram and found no improvement. Its own
200-million-node and 60-second limits were not reached. It shares the input
parser and initial witness validator; this is a separate neighborhood check,
not a formal proof or an independent reproduction of the 17-square search.

Both tools reject searches above side 15. Node and time interruptions have
explicit non-completion statuses. For the new depth, tests compare the primary
search against exhaustive final-board checks on small boards, including
positive and negative four-for-five cases. Tests also interrupt the search
inside an insertion prefix. The audit's graph traversal was compared with
the existing validator on all 65,536 four-square subsets, and its positive,
negative, and cutoff behavior was tested separately.

```bash
cargo test --lib deletion_search
cargo test --bin audit_deletion_four
```

### Conclusion and stopping point

Together with the completed smaller neighborhoods, these computations exclude
every strictly better feasible board differing by at most four original-F
deletions. Selecting d+1 additions from any purported larger improving set
would already give a feasible improvement after d deletions, and that case
was covered. Consequently at least **five original preserved vertices must
be absent from any better final board**.

This does not prove that five deletions suffice, require a temporary loss of
five vertices along a sequence of moves, or rule out neutral-move escape.
The known score-77 witness still proves that this score-76 local trap is not
globally optimal. As planned, no five-for-six escalation was run.
