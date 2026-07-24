# Finite-state tile grammar

## Purpose

The fixed residue-2 slab and copied-band families fail because they freeze too
much of the old witness. The replacement is a frontier grammar that can rewrite
the preceding 3-row band while retaining exactly the information needed to
compose another band.

`analysis/tile_grammar.py` implements the grammar kernel. It processes the
dual graph of U-U primal edges without constructing a spanning tree.

## State

After primal row `r` is processed, the exposed frontier contains the `n-1`
cell faces below that row and the exterior face `OUT`. A state records:

* `previous_u_mask`: U positions in row `r`, needed to evaluate vertical U-U
  edges when the next row arrives.
* `partition`: the connectivity partition of `OUT` and exposed dual faces.
* `u_cost`: number of U vertices consumed so far.
* `cycle_excess`: number of dual edges that joined vertices already connected.
* `row_index`: the next row to process.

A state is rejected as soon as a dual component disappears behind the frontier
without connecting to `OUT` or the new frontier. Such a component can never be
reached by later rows.

Three row transitions form one tile-band transition. A synthesis search can
therefore replace the previous band, recompute its outgoing state, and continue
without preserving the old pattern cell-for-cell.

The initial production layer assembles bands from the canonical named tiles in
`tile_alphabet.py`. Equivalent outgoing states are deduplicated, after which a
bounded beam retains states closest to the residue-specific U budget:

```bash
python3 analysis/tile_grammar.py --synthesize 6
python3 analysis/tile_grammar.py --synthesize 9 --beam 5000
python3 analysis/tile_grammar.py --synthesize 6 --oriented
```

The default alphabet uses six canonical orientations. `--oriented` expands it
to the 24 unique dihedral variants. Three synchronized partial connectivity
states compose these tiles one column at a time, deduplicating equivalent
prefixes before a complete band is formed.

The oriented grammar finds exact, independently checked residue-0 witnesses at
n=6, n=9, n=12, n=15, and n=18. A fixed boundary template inferred from n=6 and n=9 does
not reach n=12, but widening each boundary role to every geometrically
compatible oriented tile does:

```bash
python3 analysis/tile_grammar.py --zero-template 12 --beam 5000
python3 analysis/tile_grammar.py --zero-wide 12 --beam 1000
```

The wide search finds n=12 after 237,702 streamed tile extensions. Its witness
has 86 U vertices, a connected dual with one cycle, and a valid forced forest.
The generated n=6, n=9, n=12, n=15, and n=18 patterns are cached as regressions in
`diagonal_patterns.residue_zero_explicit_pattern`.

Every tile extension is now pruned by the exact attainable U-cost set of its
remaining domain suffix. For n=12 this reduces the wide search from 237,702 to
85,242 extensions. A second search processes the bottom bands after vertical
reflection and joins their connectivity partition to a top-down frontier:

```bash
python3 analysis/tile_grammar.py --zero-bidirectional 12 --beam 1000
python3 analysis/tile_grammar.py --class-pattern data/diagonal_u_15.txt \
  --fix-bottom-band --beam 100
```

The second command fixes only the final tile band. Every upper tile remains
free within the dihedral class observed at that position. It finds a new exact
n=15 orientation after 190,877 extensions; notably its top row is empty. The
unfixed class-neighborhood beam and the old wide-boundary domains do not find
this state, so those geometric boundary roles are not an invariant of the
residue-0 family.

## Correctness checks

The grammar's final acceptance condition is dual connectivity. The command

```bash
python3 analysis/tile_grammar.py --verify --max-n 4
python3 analysis/tile_grammar.py --verify-streamed --oriented
python3 analysis/tile_grammar.py --verify-bidirectional --max-n 3
```

exhaustively compares it with `construction_lab.dual_connectivity_check` on
every U pattern through 4x4. The streamed check compares every canonical or
oriented two-tile band at both reachable band positions of a 6x6 grid against
the original complete-row transition. Cached residue-2 traces are available
the original complete-row transition. The bidirectional check tests all 1,040
possible row cuts through 3x3 and verifies both connectivity and cycle excess.
Cached residue-2 traces are available with:

```bash
python3 analysis/tile_grammar.py --trace 14
```

For a connected final dual graph, `cycle_excess` is its cyclomatic excess.
Thus the expected residue-2 tail state has excess 1, while n=8 has excess 0.

## Synthesis work remaining

The transition kernel and horizontal composition are implemented. Prefixes are
deduplicated by

```text
(previous_u_mask, partition, u_cost, cycle_excess)
```

subject to the exact residue-specific U budget. The remaining mathematical
problem is the production rule: neither a copied tile row/column with a free
crossing tile nor all exact-cost 2x2 crossing rewrites extends cached n=15 to
n=18. A tail construction therefore needs a rewrite spanning more than one
local crossing. The bottom band is enough to anchor a broad n=15 orientation
search, suggesting that the next production should preserve a frontier state,
not the previously guessed per-position boundary roles. Once found for residue
0, the same transition kernel applies unchanged to residue 2 with a
boundary-cap production.

## Nonlocal production experiment

`search_tile_production.py` tests n→n+3 directly. It keeps the old tile matrix,
inserts one complete tile row and column, and synthesizes all 11 new tiles
jointly. New bands can copy a source class profile, leave one whole direction
free, rewrite nearby preserved tiles, or use every same-cost 3x3 pattern at
selected old positions:

```bash
python3 analysis/search_tile_production.py 15 --all-insertions \
  --copy-row 2 --copy-col 2 --beam 100
python3 analysis/search_tile_production.py 15 3 3 \
  --copy-row 2 --free-old 1,1 --free-old 3,2 \
  --free-old-patterns --beam 200
python3 analysis/search_tile_production.py 15 --observed-transfer --beam 20
```

For n=15→18, the target increase is 63 U vertices: the 11 new tiles must
contain eight 6-U and three 5-U tiles. All 180 cost-compatible copied
row/column class profiles were tried at all 36 insertion alignments for each of
the cached and grammar n=15 orientations; none leaves compatible half states.
Freeing the inserted column along its full height reaches one top and one
bottom state at the central alignment, but each half already has one cycle and
their frontier join has excess four.

The cycle-closing preserved tiles are source positions `(1,1)` above the cut
and `(3,2)` below it. Beam-200 scans found no cycle-free half after replacing
any one preserved tile or the tested two-tile sets by every same-cost 3x3
pattern. The scans covered all 15 top singletons and 42 top pairs, plus all 10
bottom singletons and 50 bottom pairs, using over 13 million transitions. A
class/cost transfer of the best n=12→15 insertion footprint also seals the
bottom half. These are bounded negative results, not an exhaustive proof, but
they rule out another local-pump direction: a production must rewrite a
substantial state-producing region on both sides of the insertion.

## Frontier-targeted multi-band search

Cross-width trace projection deletes three consecutive mask columns and the
corresponding three exposed faces, then recanonicalizes the connectivity
partition. Cached n=9 and n=12 states match exactly after each of the first two
bands under this projection: deleting a slab near columns 3--5 accounts for
six additional U vertices per band without changing cycle excess. No projected
state match exists for n=12→15; the n=15 witness creates its cycle two bands
earlier. Thus the first recurrence fragment is real but is not the tail rule.

The production search can now free complete preserved bands within each tile's
U cost, cap horizontal prefix states with `--prefix-beam`, and rank final
backward states by their actual join with the retained forward frontier:

```bash
python3 analysis/search_tile_production.py 15 3 3 \
  --free-old-band 2 --free-old-band 3 --beam 500 --prefix-beam 500
python3 analysis/tile_grammar.py --compare-zero 9 12
```

Horizontal prefix pruning rejects a dual component as soon as it lies wholly
behind the processed tile prefix. This is exact and is covered by the streamed
transition regression. At the central row insertion, all six column alignments
were tested with both adjacent old bands free at beam 200; the central alignment
was also tested at beam 500. No exact-cost pair connects. The best joins have
two components, typically isolating a short left interval from OUT. Moving the
row insertion likewise leaves two components in viable interior cases, while
boundary cases lose one half-state set. An unrestricted oriented n=18 control
at beam 100 and prefix beam 200 has a best join with ten components. These are
beam-limited diagnostics, not impossibility results.

### Bridge-directed follow-up

The closest column-1 alignment isolates cut faces 0--1, so only crossing
columns 0 and 2 can directly attach that component to OUT. The production tool
can now replace selected synthesized tiles by every same-cost 3x3 pattern and
can expand the two tiles at a cut column, optionally requiring its crossing:

```bash
python3 analysis/search_tile_production.py 15 3 1 \
  --free-old-band 2 --free-old-band 3 --expand-cut-column 2 \
  --free-pattern 1,0 --free-pattern 4,0 --beam 200 --prefix-beam 300
python3 analysis/search_tile_production.py 15 3 1 \
  --free-old-band 2 --free-old-band 3 --bridge-column 0 \
  --max-cycle-excess 2 --beam 200 --prefix-beam 300
```

Expanding just the cut tiles, their neighboring boundary tiles, or the entire
left tile corridor leaves the same two-component join. Requiring either direct
crossing column removes every forward half-state, even with cycle allowance 2;
an exact upper-half check for column 2 exhausts after 590 transitions. Thus the
missing attachment cannot be repaired by inserting one cut edge under the
current per-position U-cost profile. The next relaxation must change the cost
profile across multiple boundary tiles or target an internal partition change
away from the meet row.

### Cost-profile search and n=18

Explicit synthesized-tile cost overrides and selectable forward/backward target
ranking are now implemented. The successful n=15→18 search uses insertion
`(3,1)` and changes only synthesized tile `(1,2)` from 5 U to 6 U. Every 6-U
3x3 pattern is allowed there; the inserted cross compensates with cost 62
(seven 6-U and four 5-U tiles):

```bash
python3 analysis/search_tile_production.py 15 3 1 \
  --tile-cost 1,2=6 --cost-patterns --target-side forward \
  --beam 200 --prefix-beam 500
```

The witness is found after 20,640 transitions from 5 forward and 200 backward
states. It has 200 U vertices, connected dual `290/290`, cycle excess one, and
a valid forced forest. It is cached in
`diagonal_patterns.residue_zero_explicit_pattern(18)`. Balanced donor/receiver
profiles all seal the forward half; the key is a net +1 preserved-tile change,
absorbed by one fewer 6-U tile in the inserted cross.

The same fixed-coordinate rule does not yet recur at n=21. A low-beam scan of
all 49 insertion alignments (1,098,253 transitions) identifies `(4,3)` as the
best baseline, with one isolated cut face and bridge columns 5 and 6. The
shifted +1 profile leaves three components. Forcing column 5 moves the isolated
component, while forcing column 6 removes all forward states. These are bounded
construction searches; no exact optimizer was run above n=15.

### Focused n=21 corridor search

The `(4,3)` baseline was rerun at beam 200/prefix beam 500. Its best exact-cost
join has one isolated cut face, with candidate bridge columns 5 and 6. Search
diagnostics now retain both half-partitions, costs, cycle excesses, and complete
tile-band provenance. `--bridge-column` is repeatable and combines all required
cut cells in one domain rather than overwriting earlier constraints.

The upper obstruction corridor has synthesized positions
`(2,0..2),(3,0..2)` with baseline costs `(5,6,6,6,5,5)`. Every net-0 or net-+1
profile of Hamming radius at most three was screened using all patterns at each
changed cost. None improves the baseline: most remove all forward states, and
the surviving profiles leave four or more components. Simultaneous bridge
requirements `(5,6)` and `(5,8)` either move the isolated interval or seal the
forward side.

Lower-side searches constrain inserted cut tiles `(4,1),(4,2)`, the next band
`(5,1),(5,2)`, and bottom-cap tiles `(6,1),(6,2)`. Cut-tile changes move the
obstruction to the interval with exits 6 and 8. Changing the next band from
6 U to 5 U seals the backward side exactly within 7,016 transitions; changing
bottom-cap tiles from 5 U to 6 U leaves at least three components. No larger
beam is justified for these profiles. The next search needs a different state
template or insertion geometry, not another local cost flip around `(4,3)`.

### Parallel geometry and frontier wave

`search_phase_shifted_production.py` now represents a three-row/column insertion
at arbitrary cell phase. Every aligned target tile is enumerated subject to the
fixed source cells outside the cross and an allowed tile-cost set. The domain
contains the exact cached n=15→18 insertion at cell starts `(9,4)`, including
its one-column sliding variant, so this closes a real gap in the aligned search
model. A beam-20/prefix-beam-50 sweep of 36 n=18→21 starts used 2,922,306
transitions. No candidate was found; only `(8,3)` and `(13,3)` retained joins,
both with four components. Larger checks and alternate cuts did not improve
them. Since the same scalar beam does not rediscover the known n=18 member,
these are search-ranking diagnostics rather than impossibility results.

Five other lanes ran concurrently. All eight dihedral n=18 cores and 392
insertion configurations were screened; none improves the identity `(4,3)`
two-component join. The predicted four-class n=21 boundary grammar loses its
forward half at beam 100. Variable insertion-domain cuts `2/5`, `3/4`, `4/3`,
and `5/2` all reach two components, with `4/3` strongest and `5/2` cheapest.
Initial 2→3 and 3→4 wide-band replacement probes also lose a half. The grammar
API now accepts an explicit bidirectional split for future non-insertion lanes.

The frontier-lift lane produced the strongest reusable artifact. Exhaustive
enumeration of an oriented all-5 final band yields 3,784 exact cost-35 backward
states. Eighteen states project exactly to rotated/reflected n=18 suffix states
over 56 orientation/slab matches. Thus an n=21 production can target cost 240
after six bands and one of these exact cost-35 caps. An unrestricted beam-100
forward search collapses to two poor states and leaves 19 components, showing
that the next implementation needs diversity or per-band target guidance, not
another local geometry.

### Exact suffix-cap driver

`search_frontier_caps.py` reconstructs the suffix artifact before every run. It
asserts 59,952 streamed transitions, 3,784 exact cost-35 states, 18 target caps,
and 56 projection certificates split as 27 rotated and 29 rotated/reflected
matches. The first six bands are unrestricted over the 24 oriented tiles with
exact cost 240. Complete states are retained by exact-partition diversity and
scored against projected n=18 traces through band 5, then directly against the
18 caps at band 6.

The planned smoke widths `(50,100,200,400,800,1600)` with partial beam 500 use
159,264 transitions. They preserve exact projected partition matches in the
early bands but collapse to 16 final prefix states; the best cap join has 17
components and cycle excess one. This does not meet the promotion criterion,
so larger complete-state beams are not justified under the same partial-band
selector and score. The next search-semantic change should diversify horizontal
partial states or target a certified quotient transition, not simply enlarge
this beam.

`frontier_quotient.py` independently pins the exact n=15/n=18 recurrence
anchors at prefix rows 3 and 6 and shifted-tail rows 12/15 versus 15/18. The
removed cross costs are exactly `(5,12,58,63)`, giving the affine decomposition
`12 + (4n - 14) + 5 = 4n + 3`. These are executable quotient anchors, not yet a
right-congruence or pumping certificate.

### Partial diversity and multicut follow-up

`stream_band_domains` now accepts a validated optional partial-state selector;
the legacy ranking remains the default and final-column partials are still never
beam-pruned. At partial beam 500, bridge-first regresses to 19 components,
port-diverse reaches 14 with 76 final states, and obligation-balanced reaches 13
with 115 final states. Doubling the obligation partial beam to 1,000 leaves the
result at 13 components and 116 states, so that policy is stopped.

The cap driver also supports a cap-seeded multicut smoke search. With backward
width 500, cut `4/3` checks 54,946 cost-compatible pairs and reaches 9 components
with cycle excess 2; cut `5/2` checks 52,230 pairs and reaches 11 components with
cycle excess 1. The run uses 1,424,976 transitions. Neither cut meets the
two-component promotion threshold.

The quotient verifier now includes an exhaustive 24x24 one-band collision
audit. Eight incoming slab states collapse to three naive projected keys. In
particular `O02` and `O03` collide, but the common `O20` continuation produces
cycle excess 1 and 3 respectively. The existing projection is therefore not a
right congruence even on the oriented alphabet. Any pumping quotient must record
hidden slab attachment and cycle information before use in synthesis.

### Exact-cardinality n=21 breakthrough

The tile grammar did not produce the first n=21 witness. A pump-seeded
exact-cardinality anneal reached a score `(1,1,0)` near-hit with one isolated
face and 400 dual edges. Exhaustive bridge-containing two-for-two exchanges and
all same-count 4x5, 4x6, and 5x5 rewrites at that corner were negative. Adding
component-directed three-for-three proposals then found valid witnesses from
three independent seeds. The cached seed-25 witness has 275 U vertices, dual
`401/401` with cycle excess one, and a valid forced forest. This closes the
finite n=21 construction target but does not supply a pumping transition.

### Phase-boundary family extracted from n=21

The n=21 witness has a simpler row grammar than its 3x3 tile history suggests.
Ordinary rows `R_a` move a four-U phase junction through periodic `.UU` stripes;
seam rows `S_a` delete one junction vertex. The recursive word
`B_(k+1) = R_(k-2) S_(k-2) B_k R_k` supplies exactly `k-2` seam corrections and
generates valid exact residue-zero patterns for every `k>=7`. This is not a
copied 3x3 slab production. The proof scaffold and edge formulas are in
`PHASE_PATTERN.md`.
