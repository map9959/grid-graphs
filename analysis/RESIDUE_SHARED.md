# Shared Residue Structure

The three conjectured diagonal counts obey one recurrence:

```text
q(n+3) - q(n) = 4n + 3.
```

This points to a common width-three transport mechanism with residue-specific
caps and frontier states, rather than unrelated constructions.

## Packet Charge

For a three-cell packet, measure charge relative to two U vertices:

```text
one-U packets: -1
L=UU., X=U.U, R=.UU: 0
H=UUU: +1
```

The residue-one construction uses dense `H` transport and sparse boundary
anchors. The residue-zero phase construction uses density-two `L/R` transport
and one-U seam corrections. An exact residue-two recurrence likely needs both:
a moving phase plus a balanced `H`/seam defect that changes topology without
changing total cost.

`analyze_residue_constructions.py` checks the shared run identity

```text
|E(U)| = 2|U| - R_row - R_column
```

and reports dual components, cycle ranks, OUT attachments, and packet charges.
Representative exact constructions show:

```text
n = 13, residue 1: connected dual tree
n = 21, residue 0: connected unicyclic dual
n = 14, residue 2: connected unicyclic dual
```

The three exact-count `n=17` near-hits instead have one isolated face. Their
edge budgets are concentrated in the 256-face main component rather than being
used to attach the final face.

## Residue-Two Control State

The bidirectional full-middle grammar found a connected, forest-completable
250-U pattern at `n=20`. Since the connected `n=17` base has 179 U,

```text
250 - 179 = 71 = q(20) - q(17).
```

Thus the two finite states have the same constant surplus one, and their count
difference is exactly the desired `n -> n+3` increment. No operation mapping
one state to the other is known yet. Literal affine row/column duplication of
the new state at `n=23` costs 341 U, so it is not the desired pump.

The 250-U state is cached as `KNOWN_250` in
`search_residue_two_middle.py`. It has 363 U-U edges on 362 dual vertices, so
its connected dual has cycle excess two. No single deletion remains valid, and
`search_residue_two_affine.py --n 20 --source middle250 --add-count 1`
exhaustively rules out every one-addition/two-removal exact trim.

A later moving-phase search found a stronger 250-U endpoint in
`residue_two_phase_front_witness.txt`. Its dual is connected and unicyclic:
362 U-U edges on 362 dual vertices. Every mutable row belongs to the
width-independent language

```text
. L^a C R^(k-a-|C|) .,
```

where `C` is a word over `X/H` of length at most five. This state has no valid
single deletion, packet downgrade, or one-addition/two-removal trim. It is the
best current surplus-one control state, but no iterable transition to it or
from it is known.

## Search Status

The packet-streamed bidirectional search uses exact full frontier partitions and
the reflected fixed bottom cap. In the basic `L/X/R/H` language:

```text
n=20, 250 U, beam 100: valid witness
n=20, 249 U, beam 100: best join has two components
n=23, 333 U, beam 20: best join has six components
n=23, 332 U, beam 20: best join has eight components
```

These are beam results, except for positive witness validation. The phase
alphabet adds the center singleton `S=.U.` and the balanced alphabet adds all
three one-U orientations. Their negative or timed-out beams are not language
exhaustions.

## Exact Local Closures

The unique retained 249-U near-hit has a detached 3x4 dual face rectangle.
Several finite neighborhoods around it and the phase-front state are now
exhausted exactly:

```text
cut-directed cell exchanges through four additions/four removals:
  20,413,000 candidates, no connected state

all eight binary packet patterns in an 18-packet radius-four halo:
  7,445,865 nominal variants, no connected state

KNOWN_250 suffix corridors over rows 11..17:
  packet columns 0..1 and 0..2, no fixed or alternate cap closure

phase-front two-lobe corridors over rows 4..9 and 14..17:
  packet columns 0..2 and 0..3, no fixed or alternate cap closure
```

The alternate caps exhaust row-cost distributions `(19,1)`, `(18,2)`, and
`(17,3)`. The five-column two-lobe widening was completed by an in-memory
bidirectional search. It censused cuts `8/9`, `9/10`, and `13/14`, selected
`9/10`, and checked 6,090 lane-counted compatible state pairs representing
166,540 assignment pairs. None was connected, so the declared five-column
language is exactly negative. The fixed cap overlaps the all-`(18,2)` lane;
lane totals are not distinct-union counts.

At `n=23`, an exact lightweight census of all eight affine D4 transforms and
top/bottom cap depths 2--6 produces 74 distinct full frontier states. The
original affine depth-three top admits no phase row, but absorbing row 3 gives
212 legal phase rows; the reflected bottom sandwich gives 63. Across all
ordered top/bottom depth pairs, each of targets 332 and 333 has 1,369
charge-arithmetic-feasible state pairs and 841 pairs where both caps admit a
declared next row. The middle gaps remain unsearched, so these are cap seeds,
not witnesses.

## Moving-Seam Lift Census

`census_moving_seam_alignment.py` compares residue-two witnesses under a
monotone `n -> n+3` row alignment with exactly three repeated source rows and a
smoothly moving inserted three-column packet. Boundary rewrites are counted
separately from a packet-radius tube. Across D4 orientations, the minimum packet
radii are one for `8->11`, `11->14`, and `14->17` (to the 179-U affine member),
but three for the 179-U affine `17->20` to the unicyclic 250-U phase-front
witness. The latter requires 100 aligned-cell rewrites, so it is similarity
evidence rather than a local recurrence.

`search_residue_two_moving_seam.py` turns the `14->17` radius-one alignment into
an exact dual-frontier transducer. It permits all eight patterns in every tube
packet, keeps full connectivity partitions, joins exact top and reflected-bottom
frontiers, and uses no beam or projected key. Fixed affine top-three and
bottom-two rows and copied boundary columns define the first declared language.

Two complete schedule families are now negative at 178 U while retaining many
positive 179-U joins:

```text
schedule                  paths   feasible joins at 179   feasible joins at 178
fixed affine                  1              1,126,025                345,143
affine HOLDs, free seams  94,932              3,252,699                817,914
one HOLD relocation   1,274,550              7,580,873              1,807,842
two HOLD relocations  8,992,170             19,759,638              4,256,057

connected joins at 179: 149, 279, 508, and 1,172
connected joins at 178:   0,   0,   0, and     0
```

Thus changing arbitrary packets throughout the full-height radius-one tube
cannot absorb the missing U under those caps when the affine row-duplication
placement is fixed or one HOLD is relocated. The relocation automaton contains
21 operation words and explicitly tracks its one removed/one inserted HOLD
budget, preventing paths from recombining into larger schedule changes. The
same exact product construction with two removed/two inserted HOLDs retains 63
operation words and is also negative at 178 after checking 4,256,057
cost-feasible joins. Its 179-U control has 1,172 connected joins.
This is stronger than a local Hamming-neighborhood negative but remains scoped:
three HOLD relocations, radius two, boundary changes, and alternate caps are not
excluded. Radius two reached 148,631 top states by target row five and was
stopped while processing row six; the full 50,234,264-path
affine-compatible schedule family was likewise stopped after reaching 54,265
bottom states. Both are `INCOMPLETE`, not negative certificates. Exact counts
and timings are in `residue_two_moving_seam_result.json`.

The first boundary widening is now complete for the fixed affine schedule. It
allows at most one changed cell among the two boundary columns on mutable rows,
tracked separately in each half and combined with a global budget at the join.
The 179-U control has 177 connected joins. At 178 U, all 1,527,250
cost-feasible joins are disconnected. This excludes both left and right
single-boundary changes throughout the full-height tube under the fixed seam
schedule.

The initially incomplete one-HOLD-plus-boundary search is now complete through
21 deterministic operation-word shards. The shards partition all 1,274,550
strict-affine-compatible control/seam paths, while emitted grid patterns may
overlap and all aggregate counts are therefore lane/schedule sums. Every shard
has an independently validated exact 179-U control; their 6,431 connected
179-U joins calibrate the language. At 178 U, all 71,215,050 cost-feasible
lane joins are disconnected. The full manifest and per-shard records are in
`data/moving-seam-shards/`.

This completes the existing strict-compatible one-HOLD schedule language with
one boundary rewrite. It does not include schedules that fail strict affine
compatibility but would become compatible only because the boundary rewrite is
allowed.
