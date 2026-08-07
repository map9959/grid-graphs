# Proof-oriented run/rank prototype

This prototype records algebraic identities and exact finite certificate
semantics. It does not prove the final counting theorem, and a valid frontier
certificate says nothing about transitions omitted from its declared finite
scope.

## Generic identities

Let `U` be any subset of the vertices of an `m x n` grid. Let `Rr` and `Rc`
be the numbers of maximal nonempty U-runs in rows and columns, and put
`R = Rr + Rc`. Let the dual multigraph contain all
`F = (m-1)(n-1)+1` faces, including `OUT`, and one dual edge for each primal
U-U edge. Loops and parallel boundary edges are retained. Write `E` for its
edge count, `C` for its component count, `rho` for graphic rank, and `beta` for
cycle rank. Then

```text
E          = 2|U| - R
rho        = F - C
beta       = E - rho = E - F + C
rho + beta = E
R + beta   = 2|U| - F + C
C - 1      = R + beta - (2|U| - F + 1)
3|U|-2rho  = 2R + 2beta - |U|.
```

The first identity sums `k-r` adjacencies over every line containing `k` U
vertices in `r` runs. The remaining identities are the standard graphic-matroid
rank and nullity formulas, including isolated dual vertices.

For `m=n=17` and `|U|=178`, `F=257` and
`2|U|-F+1=100`. Thus, with `delta=C-1`, every 178-U pattern satisfies exactly

```text
delta = R + beta - 100.
```

In particular, dual connectivity is equivalent to `delta=0`, not merely to an
edge-count bound. `proof_oriented_identities.py pattern FILE --n17-178` checks
the specialization for a supplied pattern; `check_pattern_identities` checks
all displayed generic identities.

## Certificate semantics

Schema `grid-graphs.frontier-inequality.v1` contains a finite list of states,
exact reduced rational potentials `[numerator, denominator]`, and a finite list
of transitions. Every transition has integer `dU`, `dRank`, and `charge`. The
checker accepts exactly when every listed transition satisfies, using
`fractions.Fraction` arithmetic,

```text
3*dU - 2*dRank >= Phi(out) - Phi(in) + charge.
```

State and transition identifiers must be unique and all references must
resolve. Negative U/rank increments and noncanonical rationals are rejected.
The mandatory scope value `enumerated-transitions-only` prevents interpreting
the checker as a coverage proof. `complete_for_source` is metadata; the checker
does not infer or certify source completeness.

`frontier_inequality_demo_certificate.json` gives two genuine `2x2` all-U row
transition deltas. It includes a half-integral potential and one tight
inequality. Verify it with:

```bash
python3 analysis/proof_oriented_identities.py demo
```

## Feeding `tile_grammar`

For an accepted row or band transition, retain its incoming and outgoing
`FrontierState` and the exact emitted row masks. The adapter
`tile_grammar_transition_record` computes

```text
dEdges  = new horizontal U-U edges + new vertical U-U edges
dCycles = outgoing.cycle_excess - incoming.cycle_excess
dRank   = dEdges - dCycles
```

This works because `tile_grammar` increments `cycle_excess` exactly when a dual
edge joins vertices already connected. A state ID used for potential synthesis
should encode the chosen finite quotient, normally row phase, previous U mask,
and canonical frontier partition; cumulative U cost and cycle count belong to
transition deltas unless the proposed quotient needs them. Row-packet charge or
another proposed local charge can be passed unchanged as `charge`.

## Proof boundary

Before using a finite certificate in a theorem, one must separately prove that
its quotient and transition set cover every admissible extension and prove the
initial/terminal potential and total-charge bounds that make the inequalities
telescopic. The complete sources below deliberately establish neither claim
beyond each declared `nxn` operational transition system.

## Complete small source and synthesis

`export_complete_tile_row_source(n, 0)` declares one complete finite source:
the reachable `nxn` row-transition quotient keyed by
`(row_index, previous_u_mask, partition)`. From every reachable nonterminal
quotient state it passes each of the `2^n` masks to
`tile_grammar.advance_row`; a non-`None` result is an accepted transition and a
`None` result is counted as rejected. This is completeness only for this
operational quotient source at that declared `n`, not for larger grids, another
transition alphabet, or a theorem-level class of patterns. The CLI currently
allows complete sources for `2 <= n <= 6`.

The exact `n=3` census is:

```text
reachable states by row: 1, 8, 14, 8
mask attempts:           184
accepted transitions:     84
rejected attempts:        100
total quotient states:     31
```

`synthesize_difference_potentials` treats each transition as the exact
difference constraint

```text
Phi(out) <= Phi(in) + 3*dU - 2*dRank - charge.
```

It runs Bellman-Ford from an implicit zero-distance super-source to detect a
negative cycle, then computes exact `Fraction` shortest distances from the
declared initial state. A negative cycle raises `InfeasiblePotentialError`.
`build_complete_tile_certificate` attaches the reduced rational potentials and
checks every inequality. `reverify_complete_tile_certificate` separately
regenerates the complete declared source and synthesized certificate, requires
exact structural equality, and reruns the independent inequality checker.

Emit and immediately reverify the default source with:

```bash
python3 analysis/proof_oriented_identities.py export-small \
  --n 3 --output /tmp/opencode/grid-graphs-n3-certificate.json
```

For zero charge, the complete synthesis results through `n=6` are:

```text
n  states  transitions  tight  terminal Phi range  rank  implied |U|
2       9           13      8                 4..4     1            2
3      31           84     50                7..10     4            5
4     106          504    162                6..12     9            8
5     369         2966    690               10..13    16           14
6    1264        16381   3058               10..19    25           20
```

Writing the desired connected-grid bound as

```text
B(n) = 3*q(n) - 2*(n-1)^2,
```

the synthesized minimum terminal potentials are exactly `B(n)` through this
range. The closed forms for `q` give `B(n+3)=B(n)+3`; the observed values are
`7,6,10,10` for `n=3,4,5,6`. This period-three scalar recurrence is the target
for a uniform quotient proof, but matching it at finitely many widths is not
such a proof.

At `n=3`, 50 of 84 transitions are tight, split `8,19,23` by destination row.
Every accepted final state is dual-connected and therefore has graphic rank 4,
so telescoping gives

```text
3|U| - 2*4 >= 7,
|U| >= 5.
```

The bounds are positive and sharp inside each finite source, reproducing the
known minima `5,8,14,20` for `n=3,4,5,6`. They remain shortest-path
restatements of complete small dynamic programs, not yet a scalable potential
or evidence that zero charge supplies the required global strip-counting bound.
Each generated certificate also contains `tight_witness_rows`, one
deterministically selected all-tight path from the initial state to a
minimum-potential terminal state; tests independently check its U count and
dual connectivity.
The next synthesis experiment is to choose a state-local charge with
theorem-relevant total charge, rerun the same negative-cycle test, and seek a
finite quotient and terminal-potential bound that are uniform in `n`.

## Row curvature and the first pooled quotient

For one accepted row transition, let `u` be the new row's U count, `h` its
number of U-runs, `v` the number of vertical U-U edges to the previous row, and
`gamma` the increase in dual cycle rank. Then

```text
dEdges             = (u-h) + v
dRank              = dEdges - gamma
3*dU - 2*dRank     = u + 2*h - 2*v + 2*gamma.
```

`tile_grammar_row_deltas` checks this identity from the exact incoming and
outgoing states. The complete-source regression checks all 19,948 accepted
transitions for `2 <= n <= 6`, including top and bottom rows, empty masks, and
boundary parallel edges.

Assigning charge one to every row turns a terminal potential `c` into

```text
3|U| - 2rho >= n + c.
```

`build_pooled_frontier_feature_experiment` projects every concrete transition
for `3 <= n <= 6` onto a common OUT-aware feature state. The coarse state keeps
row phase and boundary mode, previous-row U count and endpoint bits, OUT face
coverage, non-OUT component count, and left/right OUT attachment. It is
feasible but weakens the residue-two terminal constant:

```text
feature level    states    transitions    phase constants 0,1,2
coarse              920         11,751                 4,2,2
runs               1,065         12,722                 4,2,5
```

The `runs` refinement adds only the previous row's U-run count. It recovers all
three desired constants `4,2,5`; exact minimum witnesses for `n=3,4,5,6` use
only tight projected transitions. Richer OUT-interval, component-profile, exact
partition, and exact-mask levels are retained as CEGAR controls but are not
needed for these terminal constants.

Width two is deliberately excluded from the pooled phase claim. It is a
degenerate residue-two base with exact charge-one terminal constant two; when
its terminal state is identified with phase-two terminals, the pooled constant
correctly drops from five to two.

Run the reproducible comparison with:

```bash
python3 -B analysis/proof_oriented_identities.py pool-features --level coarse
python3 -B analysis/proof_oriented_identities.py pool-features --level runs
```

This remains a finite enumerated-width experiment. In particular, feature
values such as U count and OUT coverage are not bounded independently of `n`,
and no proof yet shows that the pooled transition constraints cover arbitrary
widths. The result identifies a compact candidate invariant: row-run curvature
plus explicit OUT-aware attachment debt.

## Sparse-formula falsification

`synthesize_sparse_frontier_potential.py` tests whether the finite `runs`
potential can be replaced by a short formula. Candidate discovery uses the
external HiGHS binary only to propose coefficients; the exact lookup control is
rationalized and rechecked against every constraint with `Fraction` arithmetic.

The training system for `n=3,4,5,6` has 20,059 transition, terminal, and anchor
constraints. HiGHS 1.15.1 reports the following unbounded-coefficient models
infeasible:

```text
basis                         candidate terms    result
piecewise linear                         260    solver-infeasible
positive-part attachment hinges        1,430    solver-infeasible
```

The 5,330-term quadratic/predicate model did not finish within three minutes
after removing coefficient bounds, so it has no feasibility result.

The exact one-hot control remains feasible: 951 of 1,065 lookup terms are
nonzero and all 20,059 constraints verify exactly. Thus the failure belongs to
the attempted compression, not to the underlying finite potential system.

A decision tree reproducing the 17-valued shortest-path table requires 332
leaves at depth 15. It is also not a held-out invariant: on `n=7` its first
violation occurs in the first row at the empty mask, with slack `-6`. Adding
OUT interval count gives 323 leaves but also fails at that same transition.
Width 8 was intentionally not run after width 7 falsified the candidate.

Reproduce the principal checks with HiGHS 1.15.1 or a compatible binary,
passing its location with `--highs` when it is not at the development default:

```bash
python3 -B analysis/synthesize_sparse_frontier_potential.py --basis linear
python3 -B analysis/synthesize_sparse_frontier_potential.py --basis hinges
python3 -B analysis/synthesize_sparse_frontier_potential.py \
  --basis lookup --denominator-limit 1
python3 -B analysis/synthesize_sparse_frontier_potential.py \
  --analyze-table --validate-tree 7
```

The infeasibility statuses are floating-point solver diagnostics, not exact
Farkas certificates, so they do not by themselves rule out these formula
families. The feasible lookup control is independently exact. Together with the
large tree and immediate held-out failure, the diagnostics show that the
arbitrary shortest-path table should not be treated as the invariant itself.
The next proof experiment should separate states that already have positive
unavoidable slack from the narrow zero-slack/equality corridor, rather than
fitting all reachable states with one global expression.

## Residue-two curvature localization

The exact row charges `3*dU - 2*dRank - 1` for the known residue-two controls
sum as expected:

```text
n=14:  2,12,-3,1,0,-2,1,0,-2,0,0,0,-5,1       total 5
n=17:  2,15,-3,1,0,0,0,0,0,0,0,-2,0,0,0,-6,1 total 8
```

Under the frozen radius-one `14 -> 17` moving-seam alignment, the per-target-row
charge differences are

```text
0,3,0,0,0,2,-1,0,2,0,0,-2,0,0,0,-1,0,
```

and sum to three. All three HOLD rows have charge zero. Therefore the `+3`
correction is not carried by the inserted rows themselves; it is distributed
among the cap and seam rewrites. Any equality classification must track that
transported attachment defect, not simply charge each inserted row.

## Exact equality corridors

`equality_corridor.py` avoids fitting a global potential. For each fixed width,
it computes exact forward and backward shortest curvature distances on the full
structural quotient

```text
(row_index, previous_u_mask, canonical frontier partition).
```

A state is retained exactly when its minimum prefix and suffix weights sum to
the connected optimum. An edge is retained exactly when it belongs to some
globally minimum row-mask sequence. Negative row weights are harmless because
the graph is layered. Transitions are regenerated during the backward pass, so
the hundreds of thousands of `n=8` edges are not retained as Python objects.

The exact corridor census is:

```text
n   all states   all edges   corridor states   corridor edges   paths   weight
3           31          84                25               40      24        4
4          106         504                18               27      14        2
5          369       2,966               117              220     242        5
6        1,264      16,381                56               94      96        4
7        4,307      87,968                33               41      16        2
8       14,582     463,002               208              368     704        5
```

Thus the equality corridor remains tiny while the full state graph grows, and
its minimum weights reproduce the phase constants `4,2,5` twice. This is a
better proof-search domain than all reachable states.

### Cross-width residue-two test

The exact `n=5` and `n=8` residue-two corridors were compared after subtracting
two U vertices per width-three packet. The profile hierarchy was deliberately
weakened one channel at a time:

```text
profile level                  n=5 rules   n=8 rules   common rules
packet: U count and row runs           31          38             11
+ vertical overlap                      49          60             19
+ cycle/curvature data                  65          79              0
+ incoming/outgoing transport state    163         176              0
+ OUT-aware attachment state           211         243              0
```

Four coarse transport state profiles are shared, but no complete transport or
attachment profile is shared. The still-richer `full` profile also appends raw,
width-dependent counts and is retained only as a disjointness control, not as a
normalization. Applied to the known larger controls, only row 12
of the exact `n=14` construction matches even a small-width packet/overlap rule;
the surplus-one `n=17` construction matches none. Neither has a full local-rule
match.

This is diagnostic evidence, not a nonexistence theorem. It says that these two
corridors do not reuse one observed row-rule support under the tested
normalizations; another width-independent alphabet or normalization may still
exist. Packet density and vertical overlap recur, but the observed cycle closure
and attachment transport are reorganized with width. The evidence favors
testing three-row bands, an open slab signature, or another geometric transport
state before another row-local feature fit.

Run the exact analyses with:

```bash
python3 -B analysis/equality_corridor.py --n 7
python3 -B analysis/equality_corridor.py --n 8
python3 -B analysis/equality_corridor.py --compare-residue-two
```

The compact residue-two comparison is cached in
`residue_two_equality_comparison.json`. Regenerating it includes the complete
`n=8` forward/backward corridor and is intentionally a slow analysis command.

## Exact three-row/open-slab lanes

`equality_slab_lanes.py` strengthens the profile comparison to concrete paths.
It enumerates all 242 optimum `5x5` row-mask paths and all 704 optimum `8x8`
paths. For every target path it deletes each contiguous three-row band and each
valid width-three open slab, then checks whether the remaining `5x5` pattern is
an exact source optimum. Every surviving deletion is replayed at all comparable
frontiers with exact mask, projected partition, accumulated U cost, hidden
attachment, and cycle channels.

The complete finite census is:

```text
target band/slab deletions tested                 25,344
deletions producing an exact 5x5 optimum          5,704
visible structure-and-cost lanes                    502
genuine two-sided interior lanes                     34
closed lanes with no hidden-only component            0
cycle-preserving visible lanes                       212
cycle-preserving interior lanes                        0
```

The cap cases account for 468 of the 502 visible lanes and all 212 globally
cycle-preserving lanes. The 34 interior lanes form 19 decorated attachment
transitions on 27 hidden interface states. Their directed transport graph has:

```text
cycle-offset-stable lanes       6
full decorated self-loops       0
vertices on directed cycles     0
```

Thus a nontrivial open-slab transport exists, but none of the exact interior
bands renews its complete hidden state. Every closed projection fails because
some intermediate component is represented only through hidden slab ports.
Even the six bands that preserve relative cycle offset change their mask or
attachment decoration.

This is exact for the declared `5 -> 8` language: all optimum paths, contiguous
three-row insertions, and fixed width-three slabs are included. It does not
exclude moving seams, noncontiguous HOLD schedules, cap-dependent recurrence,
or a different state appearing at larger widths. As a larger-width control,
none of the 225 literal row-band/slab deletions maps the known affine `n=17`
surplus-one pattern to the known exact `n=14` pattern, consistent with the
previous moving-seam rewrite census.

The result isolates the next plausible refinement: a moving decorated slab
whose interface state changes along an acyclic local transport and is restored
only after several bands or a cap interaction. A fixed-slab one-band pump is
now exactly excluded for literal cross deletion in the smallest two residue-two
equality corridors. Rewrites of retained cells remain outside this scope.

Regenerate the compact artifact with:

```bash
python3 -B analysis/equality_slab_lanes.py \
  --output analysis/equality_slab_lanes.json
```

## Exact moving-slab lanes

`equality_moving_slab.py` tests the next refinement without selecting a witness.
It again uses all 242 optimum `5x5` paths and all 704 optimum `8x8` paths, but
allows the deleted width-three slab to move by one column per row. Each target
row either advances the source path or is one of three noncontiguous HOLD rows.
At every interior cut, the compressed visible mask, projected partition, and
normalized U cost must equal the source state; the hidden slab attachment,
forgotten-only components, relative cycle excess, and source/target phases are
retained as the transport decoration.

The complete census finds:

```text
target optimum paths with an alignment                 58 / 704
moving-slab alignment paths                               3,517
terminal cycle-excess-preserving alignments               1,849
distinct ADVANCE/HOLD words                                  10
terminal cycle-excess delta range                         -2..3
```

Thus moving the seam and distributing the HOLD rows is materially less rigid
than literal cross deletion. However, the phased interior decoration graph for
all successful alignments has 154 vertices and 251 edges, with no self-loop and
no vertex on a directed cycle. Restricting to the 1,849 alignments that preserve
terminal cycle excess leaves 96 vertices and 159 edges, again with no self-loop
and no directed cycle.

This exactly excludes a renewable interior state in the declared `5 -> 8`
moving-slab language. It does not exclude renewal after multiple width
increments, a cap-mediated reset, states first appearing at larger widths, or
rewrites of retained cells. The positive alignments show that visible matching
alone is insufficient: even cycle-preserving endpoints can traverse only an
acyclic sequence of complete hidden decorations.

Regenerate the compact artifact with:

```bash
python3 -B analysis/equality_moving_slab.py \
  --output analysis/equality_moving_slab.json
```

## Cap reset and two-band composition

`equality_composed_transport.py` generalizes the same exact alignment DP to a
width-three `2 -> 5` relation and a direct width-six `2 -> 8` relation. It then
composes `2 -> 5` with the complete `5 -> 8` relation by literal equality of
the entire intermediate `5x5` row-mask path. No interface quotient is used at
the join: the intermediate object is one of the 242 complete optimum paths, so
this is an exact reset through both caps of a connected square.

The cap-mediated composition is nonempty:

```text
intermediate n=5 paths admitting both legs                    10
source/intermediate/target path triples                       80
alignment-chain multiplicity                              49,638
intermediate paths with cycle-preserving legs                   4
cycle-preserving path triples                                   8
cycle-preserving alignment-chain multiplicity                2,832
```

The 80 triples collapse to 53 distinct `n=2`/`n=8` endpoint pairs. Every one
of those 53 pairs also admits a direct moving width-six slab; all six endpoint
pairs obtained from cycle-preserving composed legs likewise admit a
cycle-preserving direct width-six alignment. Thus both a complete-square cap
reset and a two-increment transport exist in this smallest exact corridor
chain, despite the absence of an interior one-increment decoration cycle.

This positive result is not yet a recurrence. The `n=2` source has only one
interior frontier depth. As a continuation control, the analysis tests all 704
exact `n=8` paths against every distinct D4 orientation of the cached exact
`n=11` witness. It finds zero moving-slab alignments, including from all 58
`n=8` paths reachable from `n=5`. This control is exact for that witness orbit
and forbids retained-cell rewrites, but it is not a census of all `n=11`
optima. Consequently cap reset explains a real finite composition at small
width, while no repeatable `5 -> 8 -> 11` transport has been established.

Regenerate the artifact with:

```bash
python3 -B analysis/equality_composed_transport.py \
  --output analysis/equality_composed_transport.json
```

## Equality-classification groundwork

The first implementation stage for classifying residue-two equality now has
four independently checked pieces.

`proof_oriented_identities.py` exposes exact `Fraction` APIs for transition
slack and path telescoping. Given a potential table, `transition_slack` computes

```text
3*dU - 2*dRank - charge - Phi(out) + Phi(in),
```

and `verify_path_telescope` rejects negative slack or a noncontiguous path and
checks the exact telescoped identity. The residue-two terminal algebra helper
checks that terminal constant five gives `6k^2+5k+3` for `n=3k+2`. These APIs do
not provide the missing potential or transition-coverage proof.

`equality_band_macros.py` composes exactly three trusted `advance_row`
transitions. It retains both intermediate frontiers, sums U, edge, cycle, rank,
charge, and curvature deltas, and records changes in the number of live
non-OUT components. Exhaustive width-three tests cover all 512 mask triples and
verify that invalid intermediate transitions cannot be hidden by a macro.

`residue_two_attachment_history.py` independently replays the known exact
`n=5,8,11,14` witnesses and the 179-U `n=17` witness cell by cell. Its frontier
states agree with the row grammar at every row boundary. At the committed
`n=17` terminal hinge:

```text
state class                 count   attachment debt   remaining merge capacity
178-U survivors               18          2                       1
178-U survivors                2          2                       0
179-U witness                  1          1                       1
```

No 178-U suffix closes, while the 179-U witness has one accepted suffix. The
matched current-row mask is not the discriminator: the decisive information is
whether the hinge face is already in the OUT component. The committed 178-U
dump contains no predecessor IDs or backpointers, so survivor histories before
this two-cell suffix cannot be reconstructed from the existing artifact.

`residue_two_equality_classifier.py` is the first finite-width decorated-debt
census. It includes all 242 minimum `n=5` paths, all 704 minimum `n=8` paths,
and the fixed `n=11,14,17` controls. It verifies total curvature five for the
first four widths and eight for the 179-U witness. Across 6,884 transition
observations it records 497 exact width-dependent classes and 960 weighted
transition classes. Attachment debt and cycle excess are separate channels;
their sum is retained only as a diagnostic decoration.

The observed exact-state graph has five nontrivial SCCs on 17 vertices. This is
not a recurrence result: width and raw frontier words remain in the key, the
larger widths contribute only one witness, and edges pooled from different paths
need not compose. The artifact is explicitly marked finite-width diagnostic,
not a potential, coverage certificate, or theorem.

Two follow-up falsification experiments narrow the missing abstraction.
`residue_two_equality_cegar.py` compares complete outgoing equality behavior and
accepting suffix languages for all 325 corridor states at `n=5,8`. The coarse
packet/run/OUT/debt key has 51 behavior-collision groups, including 24 with a
cross-width witness. Adding non-OUT attachment profiles reduces this to 37
groups and only one cross-width collision: the top states, whose accepting
suffix words have different lengths. There are no sampled cross-width bulk
collisions at this level, but 36 within-width collisions remain. The exact
width-dependent structural control has none. Thus attachment profiles are
necessary and separate the sampled bulk across widths, but are not yet a
continuation congruence even on the enumerated corridors.

`residue_two_band_classifier.py` verifies 4,986 sliding three-row macros. After
normalizing six baseline U vertices and nine baseline rank units per packet
column, it finds 463 complete observed band classes. Only three recur at more
than one sampled width: one at `5,8`, one at `8,17`, and one at `14,17`. All are
interior classes; none by itself is a composable complete frontier recurrence.
This small overlap is more accurate than the unnormalized row-profile
comparison, but it remains path-sampled above width eight.

Finally, `residue_two_pooled_potential_n7.py` extends the complete charge-one
transition pool through `n=8`: 570,905 accepted concrete transitions and
173,367 strongest projected constraints. The old `runs` quotient develops a
negative constraint cycle when `n=7` is added. Adding an explicit
rows-to-terminal coordinate restores finite feasibility through `n=7`, but the
`n=8` constraints lower the residue-two terminal constant from five to two.
The resulting implied bounds are only 13 at `n=5` and 36 at `n=8`. This exactly
falsifies that refined quotient as a sharp cross-width residue-two invariant;
an attachment relation, rather than another scalar row countdown, is required.

The remaining theorem-critical steps are therefore unchanged but sharper:

1. derive a width-independent finite-control/affine-counter abstraction;
2. prove the charge-one potential with residue-two terminal constant five;
3. retain only exact zero-slack symbolic transitions;
4. classify their SCCs using OUT-rooted debt and future merge capacity;
5. prove that every putative equality path beyond the small bases reaches a
   positive attachment deficit before the bottom cap.

## Exact symbolic packet frontier

The continuation collisions above can now be localized to ordered packet data.
For `n=3k+2`, `residue_two_packet_cegar.py` splits a frontier into two cap bits
and `k` ordered three-bit words. On the complete `n=5,8` corridors:

```text
signature                       within-width bulk collisions   cap collisions
ordered packet words                          45                     8
+ packet-local rooted restrictions            12                     2
+ overlapping local carry windows              0                     0
```

The zero at the local-carry level is observational only: all 325 sampled states
receive distinct keys. Independently canonicalized overlap windows are also not
lossless in general, because one component may join separated packets without
appearing in an intermediate overlap. The artifact therefore includes a true
`packet_global_carry` control: canonical rooted component labels are stored in
packet order, preserving arbitrarily long attachment arcs. This is exact but
its word length and label stack grow with width.

`row_packet_transition.py` exposes the existing partial-row DSU semantics as an
immutable public packet cursor. It supports `start_row`, `append_packet`, and
`finish_row`, checks component retirement after every packet, and preserves
exact U, cycle, packet-charge, and H-count channels. Exhaustive width-five tests
compare all eight packet values from every first-row frontier with
`advance_row`; known `n=8,11,14,17` witness rows provide larger controls.

`symbolic_packet_frontier.py` then gives a lossless variable-length symbolic
frontier:

```text
row index
left/right previous-row cap bits
ordered previous-row three-bit packet words
left face plus ordered three-face rooted component-label groups
cumulative U cost and cycle excess
```

Encoding and decoding are exact inverses. `advance_symbolic_row` consumes cap
bits and packet words through the packet cursor and agrees with `advance_row` on
all tested accepted and rejected transitions. Thus equality transport no longer
depends on width-sized integer masks as an interface, while retaining the full
connectivity information required for right congruence.

This also identifies the mathematical boundary of the approach. Arbitrary grid
frontiers have Catalan-many noncrossing partitions and can require attachment
nesting depth proportional to `k`; no bounded finite controller can represent
all of them losslessly. A uniform equality theorem must prove that zero-slack
paths lie in a smaller packet/attachment motif grammar, or use an algebraic
potential over the exact packet stack. The next CEGAR target is therefore a
compressed equality-only motif language, not another quotient of unrestricted
frontiers.

## Equality motif and compact transition grammar

The equality-only CEGAR pass now supplies a concrete candidate for that smaller
language. `residue_two_carrier_grammar.py` verifies on the complete `n=5,8`
corridors that each component has contiguous packet support and that at most one
non-OUT component crosses any packet cut. `residue_two_local_motif_grammar.py`
further reduces the observed rooted three-bit packet alphabet to

```text
empty 000 001 011 012 100 102 110 111 112 120 122 123
```

excluding `010`, `101`, and `121`. These are exact finite-corridor observations,
not yet a proof that every zero-slack path obeys the restrictions.

For the explicit affine residue-two family,
`residue_two_affine_motif_grammar.py` gives a lossless width-independent
description: one dominant packet/attachment atom, with exceptions confined to
the first two and last four packet positions. At most six exception positions
are permitted and the generated traces use at most five. The decoder rebuilds
the full global rooted labels, so no width-length carrier record is retained in
the compact code. All 2,415 encoded states from `n=17..119` pass exact expansion
and row-transition checks; the fixed `n=11,14` equality traces pass as well.

`residue_two_compact_transition.py` extracts a finite-control/affine-counter
machine from those traces. The control explicitly separates the finite bases
`n=17` and `n=20` from one stable `n>=23` regime. Its 2,380 observed transitions
have 56 regime-qualified controls, 14 actions, 55 rules, and no nondeterministic
source/action pair. The stable regime itself uses 19 controls and 19 rules; no
new observed rule appears after `n=23` through `n=119`. Each rule's U and cycle
deltas are fitted as affine functions of packet length and checked against all
of its occurrences.

This resolves the former `n=20` versus `n>=23` finite-observation conflict, but
does not establish an arbitrary-`k` theorem. The remaining proof obligations are
to verify the stable rules symbolically for every packet length and to prove a
coverage lemma forcing every zero-slack frontier into the one-carrier,
local-alphabet, boundary-defect grammar.

The counter part of the first obligation is now discharged by
`residue_two_stable_counter_certificate.py`. For each of the 19 stable rules it
derives affine formulas directly from the regular packet word: U count and
horizontal/vertical edge counts are local word statistics, while the compact
carrier roles give the exact incoming and outgoing frontier debts. The identity

```text
dRank = new_faces + debt_in - debt_out
dCycles = dEdges - dRank
```

then determines the cycle formula. These symbolic expressions agree with all
2,277 generated stable transitions through `n=119`, but the derivation itself
does not depend on fitting or on that finite horizon.

`residue_two_stable_topology_certificate.py` discharges the complementary
topological obligation. It streams the actual row graph and claimed outgoing
partition together, retaining only OUT, the old/new faces at the packet cut,
and the source/target carrier ports. A component is forgotten only when its
actual and expected blocks close one-to-one; an old-only closure is exactly the
sealed-component rejection in `advance_row`, while incidence mismatches detect
incorrect outgoing splits or merges. For each of the 19 rules the fixed first
two packets reach a canonical cut state, one dominant packet is a self-loop on
that state, and the fixed final four packets close to the claimed target. The
self-loop can be repeated `L-6` times, proving acceptance and exact rooted
partition transport for every packet length `L>=7`. Concrete comparisons at
all `L=7..39` are regression checks, not the induction argument.

Together, the topology and counter certificates prove all 19 stable transitions
of the generated affine family for arbitrary `n=3L+2>=23`. They still do not
prove the theorem-critical coverage statement that every zero-slack equality
frontier belongs to this compact boundary-defect language.

## Structural coverage falsification

The original coverage target is false. An exact two-channel extension of the
packed Rust frontier DP records whether any completed frontier has violated the
carrier/local grammar while retaining the minimum U cost for each structural
state and history bit. At `n=11`, both channels attain the exact optimum 72:

```text
minimum grammar-respecting U = 72
minimum grammar-violating U  = 72
```

`residue_two_n11_grammar_counterexample.py` replays a recovered 72-U witness and
checks charged curvature five. Its only rejected frontier is at row 8, where
component 3 occupies packet groups `(1,3)` while group 2 is empty; the next row
repairs the hole. Every packet motif remains in the learned alphabet, no two
components cross one packet cut, and maximum face-cut open width remains one.
Separate exact product searches at U=72 find no `n=11` equality path with a
concurrent-carrier, forbidden-local-motif, or face-cut-width violation.

Thus the complete `n=5,8` defect gap of three does not extrapolate even to
`n=11`: `residue_two_structural_defect_gap.py` remains an exact finite-width
certificate, but contiguous support cannot be a theorem lemma. The minimally
widened candidate is a hull-carrier language: at most one live component crosses
each face cut, but that carrier may pass silently through a packet containing no
face of the component. The compact atom decoder and stable transition census do
not yet represent this silent carry, so their arbitrary-length correctness for
the affine sublanguage does not establish equality-language coverage.

## Concentric thin-strip relaxation

Chapter 3 of Acquaviva's thesis gives exact bounds `P(2,s)=s` and
`P(3,s)=floor((4s+2)/3)`. Restricting globally full vertices to an induced
rectangle preserves a forced forest, so these are valid local inequalities in
the square problem. `concentric_strip_bound.py` applies them to nested squares.
For a side-`s` square let `F_j` be its full-vertex count and let `B_j` count its
full boundary vertices with corners counted twice. Exact forest counting gives

```text
3 F_j <= s^2 - 2 + B_j.
```

Summing four depth-two side strips gives

```text
B_j + B_(j+1) + X_j <= 4s,
```

where `X_j` counts eight corner-adjacent shoulder sites. The implementation
retains the minimum shoulder occupancy forced by the boundary and also checks
the analogous depth-three inequality with two shoulder layers. Known
`n=4,5,8,11,14,17,20` witnesses satisfy every inequality.

The resulting relaxation is not sharp. Its residue-two upper bounds on `P` are

```text
n                 5   8   11   14   17   20
concentric bound 13  30   53   82  117  158
target/exact     11  27   49   77  110  150
```

Depth-three strips improve only `n=6,9` and are redundant from `n=10` onward.
Thus scalar occupancy and corner multiplicity miss a growing gap; the next
annulus refinement must retain connectivity or ordered attachment ports, not
another strip-count total.

## Rank-aware annulus refinement

`concentric_strip_bound.py` also maximizes the exact number of perimeter
U--U edges and bounds radial edge capacity. This rank-aware relaxation improves
only `n=5`, lowering the bound from 13 to 12; its bounds at
`n=8,11,14,17,20` remain `30,53,82,117,158`. Exact censuses in
`concentric_layer_rank_census.json` explain the missing information:

```text
n   scalar-optimal placements   maximum rank   required rank   connected
5                     1,820             14              16           0
8                 4,462,920             45              49           0
```

At `n=8`, a placement attaining the scalar maximum of 49 dual edges has rank
only 42: it has eight components and seven cycles. A different placement
attains the maximum rank 45 with no cycles but still has five components.
Consequently edge supply and cycle penalties alone are insufficient; the state
must know which internal components attach to the next perimeter.

`concentric_connectivity_profile.py` records the exact centered-annulus identity

```text
M_s - (s-1)^2 = (q_s-d_s) + beta_s,
```

where `M_s` is the number of U--U edges in the centered side-`s` square, `q_s`
is the number of active perimeter ports, `d_s` is its number of internal dual
components, and `beta_s` is its internal cycle rank. It additionally compresses
the cyclic port word by retaining labels only for components that occur more
than once; singleton component names are immaterial. Across every centered
prefix of the known feasible `n=5,8,11,14,17,20` witnesses, this exact ordered
signature has at most four repeated components, at most three cyclic runs per
component, and at most nine compressed runs. These are observed bounds, not a
coverage theorem. The next proof obligation is to derive them, or comparable
constants, for every extremal residue-two pattern; that would turn the annulus
profile into a finite-state transfer argument.

`concentric_equality_census.py` strengthens the small-width scope from selected
witnesses to complete equality classes. It enumerates all 242 globally minimum
`n=5` paths and all 704 globally minimum `n=8` paths. None violates the declared
`4/3/9` bounds. The exact maxima are respectively `4/1/5` and `4/2/6` for
repeated components, cyclic runs per component, and compressed runs. This
remains finite-width evidence; the next exact falsification target is a product
frontier monitor over all 72-U `n=11` patterns.

That product monitor now exists in `search_n11_centered_product`. It augments
the exact global frontier with every selected-square bit until the centered
profile closes, then retains the exact threshold-violation flags. With no beam,
symmetry quotient, or heuristic pruning, the side-3 query completes:

```text
cargo run --release --bin search_n11_centered_product -- --side 3
connected=true  any_violation=false
peak_states=1,358,652  transitions=78,285,124
```

Thus every connected 72-U `n=11` pattern satisfies the `4/3/9` bounds at its
centered side-3 prefix. The independent Rust terminal monitor in
`src/exact_centered_square.rs` agrees with the Python profile on all known
`n=5,8,11,14,17,20` witnesses.

The side-5 query is now exact as well. A canonical streaming component monitor
was minimized backward by threshold-language equivalence: two local states are
merged only when both successors have the same class for every remaining input
suffix. This reduces the side-5 local automaton from 369,032 states to 78 and
the exact global product to 1,291,749 peak states, 96,819,952 transitions, and
about 274 MiB RSS. No `4/3/9` violation exists at side 5.

Side 7 remains open. Exact local-language generation reaches 14,614,444 states
after 34 of 49 cells and crosses the 6 GiB allocation gate. A deterministic
256-shard external repartition specification is committed in
`annulus_side7_threshold_automaton_shards.json`; no side-7 result is claimed
until every shard and both successors of every source state are processed.

The `4/3/9` constants are not a topological theorem and must not be the final
coverage abstraction. The valid but surplus affine A23 pattern has signature
`5/3/12`. The replacement reduced metric is

```text
branch_cost = sum over ported components (cyclic occurrence runs - 1).
```

Unconditionally, branching components are at most `branch_cost`, and on an
unsealed annulus `branch_cost` is at most attachment surplus. Complete n5
equality has branch cost zero; complete n8 equality and fixed n11/n14 equality
controls have maximum one. Affine A17,A20,...,A41 grow as `2,3,...,10`.
Therefore any constant-state theorem must derive bounded branch cost from
curvature-five extremality, not from planarity alone.

`residue_two_cap_merge_potential.py` gives the strongest current finite
potential. Cap phase, component deficit, suffix merge-capacity surplus,
previous-row U count, OUT-face count, and branch cost produce 268 exact
difference constraints on 133 states. All 588 complete n5/n8 equality
transitions are tight with terminal constant five; fixed n11/n14 and affine n17
paths extend consistently but are not covered. The n17 extra unit is instead
separated at the terminal by

```text
unpayable_debt = max(rooted debt - remaining independent merge capacity, 0).
```

Every 178-U survivor has positive unpayable debt (`1` for 18 states, `2` for
two), while the 179-U control has zero. The next potential must propagate a
persistent spent-merge/unpayable-debt flag and replace suffix-enumerated merge
capacity by a covered local upper bound.

`residue_two_persistent_debt_certificate.py` implements that history channel on
the complete n5/n8 equality languages. Its safe local capacity bound uses
remaining rank and U budget, with an exact terminal-row edge DP. All 783
complete history transitions are tight with terminal constant five; fixed
n11/n14 controls remain feasible and the n17 terminal separation is recovered
without suffix acceptance. Global propagation is still blocked because the
committed 178-U terminal dump has no predecessor summaries and arbitrary-width
low-curvature hull coverage remains unproved.
