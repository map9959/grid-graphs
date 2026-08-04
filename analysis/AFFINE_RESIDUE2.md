# Affine Residue-Two Pump

`residue_two_affine_pattern(n)` is the best current parametric candidate for
`n=3k+2`, `k>=5`. Every checked member is dual-connected and
forest-completable, but the family still lacks an inductive connectivity proof
and has a linear surplus over the conjectured minimum.

## Base

The base is the connected 179-U pattern at `n=17`. It is obtained from the
cached exact `n=14` witness by changing old cell `(4,8)` from U to a dot,
inserting three rows before row 6, inserting three columns before column 7 or
8, and placing 61 U vertices in the inserted cross. Thus

```text
179 = 119 - 1 + 61 = q(17) + 1.
```

Its dual has 257 vertices and 257 edges, is connected and unicyclic, and the
forced forest completes to a spanning tree.

## Pump

Given a pattern of width `m=3k+2`, form width `m+3` by duplicating rows 9, 10,
11 immediately before row 9 and columns 4, 5, 6 immediately before column 4.
Equivalently, use index lists

```text
rows:    0..8, 9,10,11, 9..m-1
columns: 0..3, 4,5,6, 4..m-1.
```

This is a fixed two-marker control state after the exceptional `14->17` start.

## Counts

For `n=3k+2`, `k>=5`, the construction has

```text
|U_k| = 6k^2 + 6k - 1
      = q(3k+2) + k - 4.
```

The pump increment is

```text
|U_(k+1)| - |U_k| = 12k + 12,
q_(k+1) - q_k       = 12k + 11.
```

Therefore each pump increases the surplus by one. The resulting spanning tree
has at least `3k^2+6k+5` full-degree vertices, `k-4` below the conjectured
residue-two value.

## Dual Edges

The induced U-U dual has

```text
E_k = 9k^2 + 8k - 8,
V_k = 1 + (3k+1)^2 = 9k^2 + 6k + 2.
```

When connected, its cycle excess is `E_k-V_k+1=2k-9`.

The checker confirms dual connectivity and forced-forest completion for every
generated member through `n=119`. This is computational verification, not yet
an inductive proof of dual connectivity.

`check_affine_residue2.py` reconstructs the pump implementation from the finite
base-word source codes

```text
rows:    (0..8) (9,10,11)^(k-4) (12..16)
columns: (0..3) (4,5,6)^(k-4) (7..16),
```

and checks the displayed U-count, induced-edge count, and cycle-excess formulas.
Its optional topology checks remain finite computation rather than induction.

## Exact-Count Status

The former conjectured n=17 target of 178 U vertices is globally impossible.
The exact frontier computation described below exhausts every pattern with at
most 178 U vertices. Combined with the validated connected 179-U base, this
proves that the minimum is 179 and therefore

```text
P(17,17) = 17^2 - 179 = 110.
```

Several 178-U patterns reach one isolated dual face. Before the global result,
the connected 179-U base was also shown to have no valid trim within any of
these complete neighborhoods:

```text
one addition / two removals,
two additions / three removals,
three additions / four removals,
four additions / five removals.
```

The exact affine 178-U packet is also negative under unrestricted global
two-for-two and three-for-three exchange. These remain useful neighborhood
certificates, but are superseded for `n=17` by the global exact frontier result.

The next constructive goal is a second pump control state whose transition
saves one U relative to the affine pump while changing the frontier attachment
state. A one-off trim at n=17 would not by itself remove the growing surplus.

At n=20, the affine member has 251 U. Complete global checks rule out every
single deletion, one-addition/two-removal trim, and two-addition/three-removal
trim to 250 U. A separate 250-U affine-lift candidate reaches `361/362` dual
faces but is globally negative under bridge-containing two-for-two and
three-for-three exchange. It was the first concrete target for the missing
second control state.

The stable `17->20` pump inserts rows 9--11 and columns 4--6 with cross cost 72.
An exact binary-cell search proves that the frozen-exterior cross cannot cost
71: after contraction, connectivity needs rank 118 while every cost-71 cross
has rank at most 116. Allowing the complete mutable column slab 0--6 is also
exactly negative at 250 U after 40,595,328 transitions.

The closest cycle-saving B state reconverges with the affine frontier after row
16 in mask, partition, and cost, but has one less accumulated cycle. Exhausting
all 77,520 cost-neutral 13-U row-16 masks leaves only 15 topology-valid incoming
states; 32,360,464 exact suffix joins prove that none has a connected three-row
suffix of cost 32. Finally, the connected 251-U affine member has no global
three-addition/four-removal trim to 250 U. The second state must therefore alter
an earlier prelude and the closing cap together; it cannot be represented by a
cross-only saving, a seven-column slab, or a late three-row suffix.

That split control was tested next. With affine rows 4--15 frozen, an exact
top-four/bottom-four synthesis checks 148,906,752 transitions and has no
connected 250-U join. A topology-guided three-box decomposition then couples
the early cycle, delayed reroute, and OUT cap. All 188 add/remove quota
distributions and 6,121,741 MITM signature pairs are negative. The sharp
one-face state produced by that language has no global repair through
three-for-three exchange. A successful B state must therefore change part of
the affine middle itself, not just its cross, prelude, suffix, or three
currently identified control boxes.

## Full-Middle Grammar

`search_residue_two_middle.py` tests a larger constant-surplus control language
at `n=20`. It fixes affine rows 0--2 and 18--19 plus the two boundary columns,
then represents each of the 90 interior three-cell packets by one of

```text
L=UU.  X=U.U  R=.UU  H=UUU.
```

The five fixed rows cost 54 U, every packet costs two U, and an exact quota of
16 H packets gives `54 + 180 + 16 = 250` U. This is the constant-surplus-one
target; the conjectured exact target at `n=20` is 249 U. Exact frontier
partitions are retained inside a topology- and quota-diverse beam. The search
now expands from both fixed caps, streams each row packet-by-packet, and joins
the exact retained frontier partitions. A beam of 100 found a valid 250-U state
with connected dual cycle excess two. Its count differs from the 179-U `n=17`
base by 71, exactly `q(20)-q(17)`, so the two states have the same surplus one;
an explicit recurrence mapping between them is not yet known.
No single deletion is valid, and every global one-addition/two-removal trim is
negative. At 249 U, beam 100 reached a two-component join but no witness.

The grammar is generalized to larger `n`. At `n=23`, beam 20 reached six
components for the 333-U constant-surplus target and eight for the exact 332-U
target. All failed beams remain non-exhaustive.

The `phase` alphabet adds the residue-zero center seam `S=.U.`; `balanced` adds
all one-U packet orientations. Charge is measured relative to two U per packet,
so `H` has charge +1 and a seam has charge -1. This permits topology-changing
H/seam pairs at fixed total count, but the first bounded seam beams have not yet
found a quota-compatible connected join.

A narrower moving-phase grammar subsequently found another valid 250-U state.
Every row has form `. L^a C R^(k-a-|C|) .` with `C` over `X/H` and
`|C|<=5`. Unlike the first 250-U state, its connected dual is unicyclic. It has
no valid single deletion, no one-packet H downgrade, and no global
one-addition/two-removal trim. A beam-500 exact-count run in the same row
language still reaches only a two-component join.

Exact searches around the retained 249-U rectangle defect now rule out local
cell exchanges through order four, all binary packet changes through radius
four in the specified halo, and several suffix/two-lobe phase corridors with
alternate caps. See `RESIDUE_SHARED.md` and the corresponding JSON result
artifacts for exact scopes. The five-column two-lobe DP initially exceeded the
one-direction time bound, but an in-memory bidirectional solver completed it.
At cut `9/10`, none of 6,090 lane-counted compatible state pairs
is connected, giving an exact negative for that declared five-column language.

For `n=23`, the failure of the fixed affine cap is now isolated: affine top
depth three admits no legal bounded phase row, while depth four admits 212 and
the reflected bottom sandwich admits 63. An exact affine/D4 cap census records
841 one-step-live, charge-feasible full-state pairs for each of targets 332 and
333. No middle search has yet connected those cap seeds.

## Affine Deletion Neighborhoods

At `n=17`, only three single-U deletions from the connected 179-U affine base
retain the necessary 256 U-U edges: `(0,1)`, `(16,1)`, and `(16,15)`. They are
three distinct D4 orbits. Each resulting 178-U pattern has two dual components,
with exactly one face detached from the 256-face OUT component. A direct census
of 59,607 one-for-one exchange candidates from these three patterns found no
witness.

The fixed-target SAT encoding then searched every same-cardinality pattern
within six exchanges of each deletion pattern, requiring at least 256 U-U
edges and a connected dual. All three declared neighborhoods are exactly
UNSAT. The radius-six solve times were 394.357 seconds for `(0,1)`, 475.704
seconds for `(16,1)`, and 466.382 seconds for `(16,15)`. This rules out a
bounded neighborhood of the affine base; it is not a global impossibility
result for 178 U at `n=17`.

A later exact moving-seam search tests a nonlocal lift from the cached 119-U
`n=14` witness. It fixes only the affine top three and bottom two rows, copies
the two boundary columns, and otherwise allows every binary width-three packet
inside a smoothly moving full-height radius-one tube. With the affine HOLD
placement fixed but all 94,932 affine-compatible seam schedules allowed, the
bidirectional frontier join has 279 connected 179-U pairs. At 178 U it exactly
checks 817,914 cost-feasible full-partition pairs and none is connected. The
single affine seam schedule similarly has 149 connected 179-U joins and zero
among 345,143 feasible 178-U pairs. See
`search_residue_two_moving_seam.py` and
`residue_two_moving_seam_result.json`.

Relocating exactly one of the three affine HOLD rows is also exhausted. The
exact control automaton retains 21 operation words and 1,274,550 compatible
seam paths. It produces 508 connected 179-U joins, but none among 1,807,842
cost-feasible 178-U joins. The automaton tracks one removed and one inserted
HOLD explicitly, so unioning schedules cannot silently create paths with
multiple relocations.

Exactly two HOLD relocations are now exhausted as well. Radius-one affine
compatibility leaves 63 operation words and 8,992,170 seam paths. At a cut
after row eight, the exact search builds 34,791 top and 42,993 bottom states.
It finds 1,172 connected 179-U joins, but none among 4,256,057 cost-feasible
178-U joins. Cost buckets avoid scanning rejected cost pairs, and an exact
connectivity cache reduces the 178 join to lookups of topology results already
computed by the 179 control.

Allowing one boundary-column cell to differ anywhere on the mutable rows is
also exactly negative for the fixed affine seam schedule. The global rewrite
budget distinguishes unchanged, left-toggle, and right-toggle lanes without
identifying the two boundary sides. It retains 177 connected 179-U joins, but
none among 1,527,250 cost-feasible 178-U joins. The reconstructed positive
control uses zero boundary rewrites.

The combined one-HOLD-relocation plus one-boundary-rewrite language is now
complete through 21 operation-word shards. They exactly partition the
1,274,550 strict-affine-compatible control/seam paths; aggregate counts are
lane/schedule sums because emitted patterns may overlap. All 21 shards have
validated exact 179-U controls, totaling 6,431 connected lane joins. At 178 U,
all 71,215,050 cost-feasible lane joins are disconnected. Per-shard artifacts
and the complete manifest are in `data/moving-seam-shards/`.

This certificate still inherits the parent schedule calibration: schedules
that require a boundary rewrite merely to become affine-compatible are outside
its scope.

These are exact scoped negatives, not a global result: three HOLD relocations,
boundary-enabled schedule calibration, alternate caps, multiple boundary
rewrites, and a radius-two tube remain
outside the completed language. Radius two and the full affine-compatible
schedule family were attempted but exceeded their resource gates and are
recorded as `INCOMPLETE`.

A subsequent native-backend gate exported deterministic global CNFs and used
CaDiCaL 3.0.1. The known-SAT `n=14`, 119-U, exactly-170-edge control returned
`UNKNOWN` after 110 seconds in all four combinations of default/SAT-targeted
configuration and no/D4 symmetry. The known-SAT `n=15`, 137-U,
exactly-197-edge control also returned `UNKNOWN` after 290 seconds with the
default configuration, both with and without D4. Since the backend could not
recover the smaller controls, no global `n=17` run or UNSAT proof attempt was
started.

A global single-commodity-flow MIP was tested as a second native-backend gate.
The deterministic LP exporter in `src/bin/search_n17_mip.rs` uses binary
vertex variables `x`, continuous variables `y` with the exact product hull
`y_e = x_a x_b`, and continuous directed flows from OUT that send one unit to
every bounded face. Singleton dual cuts and the necessary total-edge rank bound
are included. Thus its integer feasible patterns are exactly the same global
patterns as the rooted SAT model; this is a computational formulation change,
not a relaxation or a new mathematical search scope.

HiGHS 1.15.1 solved and independently revalidated the exact `n=3`, 5-U
positive control and proved the 4-U control infeasible. On the first hard gate,
however, the unpinned `n=14`, 119-U model found no incumbent in 1,800 seconds
after 282,904 branch-and-bound nodes and 69,434,554 LP iterations. The model had
196 binary variables, 1,092 continuous variables, 2,161 rows, and 6,696
nonzeros. Following the declared go/no-go rule, the `n=14`, 118-U negative
control and all larger MIP runs were not started. This flow formulation
therefore fails the same witness-discovery calibration as rooted SAT and gives
no evidence about the global 178-U target.

An independent exact frontier solver in `src/bin/search_n17_frontier.rs` avoids
SAT discovery. It streams primal vertices, stores the canonical connectivity
partition of exposed dual vertices, rejects retired components, and keeps only
the minimum U cost for each structural state. A dual-rank deficit bound safely
prunes any state whose target would require more future rank than two per
remaining U. The solver agrees with exhaustive brute force through `n=3` and
obtained these release-mode controls:

```text
n   minimum U   peak states   generated transitions   wall time   peak RSS
12         86       309,484                48,653,376         21s      71 MiB
13        101       942,584               175,652,061       2m40s     210 MiB
14        119     2,886,116               656,191,514      12m16s     446 MiB
15        137     8,878,120             2,341,368,355      21m11s   1,605 MiB
16        156    27,428,146             8,373,712,900      59m40s   3,461 MiB
```

Thus the known targets through `n=16` are independently certified as exact
minima despite the global SAT backend failing to recover even `n=14`.

The isolated experimental solver `src/bin/search_n17_frontier_pruned.rs` then
quotiented states by left-right reflection at completed row boundaries. This is
an exact symmetry reduction: reflection preserves U cost, the full processed
dual partition, and the set of possible future continuations. Exhaustive tests
compare every target through `n=3`; additional controls recover the exact
minima at `n=8` and `n=12`. The global target run returned:

```text
UNSAT n=17 u_count=178 pruning=Mirror
peak_states=45,898,352
transitions=16,359,946,462
mirror_merges=126,288,370
elapsed=1h53m45s
peak_RSS=8,784,308 KiB
```

The state set becomes empty before the final vertex, so no connected dual can
use at most 178 U vertices. Dual connectivity is monotone under adding U
vertices, making this equivalent to exact-target UNSAT. The result and source
hash are recorded in `frontier_n17_mirror_result.json`; together with the
validated 179-U construction, it proves `P(17,17)=110`.

The preserved unmirrored search was subsequently resumed from step 34 and also
returned `UNSAT`, emptying at step 288 after 30,053,510,406 generated
transitions. It peaked at 85,066,722 states and 14,006,952 KiB RSS; the resumed
segment took 9,449.550 seconds. Exact source, binary, initial-checkpoint, and
final-checkpoint hashes are recorded in `frontier_n17_unmirrored_result.json`.
This removes dependence on the reflection quotient from the computational
certificate, while retaining the same independently validated 179-U upper
bound.

An exact reverse transition and forward/backward meet mode were subsequently
added to the same solver (`--meet-step T`). The inverse enumerates every
predecessor partition allowed by the at-most-two local dual-edge unions and
then validates each candidate with the forward transition. Exhaustive tests
compare the complete inverse relation on every canonical pre/post state through
`n=3`; target-bounded meets agree with brute force at every cut through that
range.

The scaling experiment rejects this decomposition for larger widths. Terminal
co-reachability is too weak: the backward traversal quickly approaches every
set partition of the active bag for every row mask.

```text
n   meet step   forward states   backward states   reverse candidates
4           8               31               240                2,428
5          12              121             1,544               27,536
6          18              276            12,992              304,976
7          24            1,030           105,760            3,771,392
```

At `n=7` the exact reverse half already takes 5.7 seconds while the forward
meet layer has only 1,030 states. Prefix rank and selected-frontier lower bounds
do not reduce the backward plateau. Consequently this meet-in-the-middle mode
is retained as a correctness diagnostic, but witness reconstruction and larger
controls were deliberately not pursued. A useful next exact algorithm must
compress or avoid the reverse partition universe rather than merely split the
row-major schedule.

## Run/Rank Relaxation

`certify_residue_two_relaxation.py` records a hierarchy of genuine necessary
conditions for the exact 178-U target at `n=17`. Dual connectivity requires at
least 256 U-U edges. If `R_row` and `R_column` count maximal U-runs, then

```text
E = 2|U| - R_row - R_column,
```

so every target must have `R_row + R_column <= 100`. The old bundled witness
passes that scalar bound and coarse block ranks, but face `(12,3)` has singleton
cut zero. The strengthened hierarchy adds all singleton and row/column interval
cuts, bounded rectangles, seam-preserving quotients, and radius-one
contracted-exterior windows.

An exhaustive one-for-one search from all three near-hits checks 59,274
candidates; four pass rectangles and none pass the seam quotients. A bounded
100,000-candidate second hop also finds no seam-quotient-feasible state. These
are restricted-neighborhood results, not an impossibility proof.

## Terminal obstruction and surplus-one B control

The final exact frontier layer sharpens the 178-U obstruction. After step 287,
all 20 surviving states have three separate active components: `OUT`,
`face(15,14)`, and `face(15,15)`. Eighteen can spend their final U to join the
two faces but remain one attachment short of `OUT`; the other two retire a
component. The accepted 179-U witness has already joined `OUT` to
`face(15,14)`, so its final U performs the remaining face-to-face merge. See
`RESIDUE2_TERMINAL_B_STATE.md` and the two exact JSON frontier artifacts.

The same note records a finite surplus-one, connected, unicyclic phase-carrier
descriptor shared by the 179-U `n=17` and 250-U `n=20` witnesses. An exact,
affine-calibrated test of its basic `X/H` carrier on the first strict radius-3
schedule finds the 335-U affine control but no 333-U connected state. This
negative now extends to the complete `X/H/S` phase carrier on that schedule:
the compiled exact search checks 1,677,381 top and 7,280,367 bottom states and
finds zero connected pairs among the 238 cost-compatible 333-U joins, while
retaining 705 connected 335-U controls. This disproves that fixed-schedule pump,
not another schedule, a broader B-state recurrence, or the global 333-U target.
