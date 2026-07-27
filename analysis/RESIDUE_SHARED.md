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
