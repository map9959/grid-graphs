# Residue-Two State-Transfer Diagnostics

This note records the attempt to replace geometric pump matching with exact
frontier control states. It is diagnostic construction work, not a new global
bound or recurrence proof.

## Ranked frontier traces

`residue_two_frontier_signatures.py` replays the known `n=8,11,14,17,20`
witnesses while retaining exact vertex, edge, and cycle-rank payloads for every
live dual component. It agrees with the ordinary frontier transition
exhaustively through `n=3` and with independent whole-graph metrics at all five
endpoints. The complete trace artifact is
`residue_two_frontier_traces.json`.

The selected minimum-radius alignments are not state-preserving transfers.
Across 58 comparable cuts, only the first row of `8->11` agrees simultaneously
in compressed mask, visible partition, deleted-packet-normalized cost, and
global cycle excess. For `17->20`, mask equality occurs once, partition equality
twice, normalized cost equality never, and components represented only through
the forgotten slab occur at 18 of 19 cuts. Thus the previous radius-three
alignment is geometric similarity, not evidence that A17 and B20 are the same
frontier state.

`open_slab_signature.py` fixes the known lossy-quotient failure by retaining the
three deleted U bits and the complete hidden attachment relation. Its regression
separates the old `O02/O03` collision whose common continuation produces cycle
ranks one and three.

## Asynchronous landmarks

`residue_two_landmark_census.py` compares top and reverse-bottom cuts at depths
two through six over every D4 image and slab position. A match requires exact
compressed mask and visible partition equality and forbids components supported
only by forgotten slab ports.

```text
pair                       top   bottom   paired two-sided lanes
exact14 -> affine17          68       68       0
affine17 -> affine20         96       96      40
affine17 -> phase20           4        4       0
phase20 -> affine23           0        0       0
```

The affine family supplies the positive control: it has 40 composable two-sided
landmark lanes. The phase-front B20 witness is a genuinely different control
state, not an affine state in another synchronous phase.

## B20 self-renewal language

`export_residue_two_self_renewal_manifest.py` builds B20's own cap-to-cap
language. Its first three and last two rows are exact inserted-packet lifts that
reproduce B20's two-sided interfaces. The middle uses the complete bounded
`X/H/S` carrier and every compatible ADVANCE/HOLD/seam path with strict
boundaries.

The resulting manifest has six active slab lanes, 17 top seeds, 17 bottom
seeds, 2,318 signature states, and 10,521 middle transitions. An exact product
search is not feasible: it grew from 21,365 states after row four to 1,701,918
after row five, before the next expansion.

A minimum-cost dominance reduction is exact for connectivity under an upper U
budget, but the remaining all-schedule product is still too large. Discovery
beams preserve every reachable alignment signature before ranking by cost and
component count. Results were stable from beam 5,000 to beam 20,000:

```text
beam    333 tested  333 connected  best C   335 connected
5,000        15,767              0       3             675
20,000       47,410              0       3          14,086
```

These are heuristic results, not UNSAT certificates. They nevertheless recover
connected 335-U joins and repeatedly expose the same three-component obstruction
at 333 U under B20-derived caps. Full scope and provenance are in
`residue_two_b20_self_renewal_beam_result.json`.

## Consequence

The current obstacle is no longer a missing row alphabet or an affine-cap
choice. Exact enumeration over all schedules is computationally intractable,
while increasingly large calibrated beams retain a two-U topology gap. Further
progress should come from a stronger attachment potential, schedule-level
decomposition, or a mathematically derived control transition, not a larger
undifferentiated frontier product.
