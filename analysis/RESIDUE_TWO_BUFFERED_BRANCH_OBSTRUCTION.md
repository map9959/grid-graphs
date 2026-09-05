# Residue-Two Buffered Branch Obstruction

## Final Bounded Grammar

The two outer staircase walls have fixed separation three. They share one
advance in `{0,1,2,3}` on each row and both advance by three in a three-row
packet. The three cells strictly between the exterior vertical-rail and
horizontal-rail domains form a blank buffer.

The internal branch has exactly one of the nine minimal phases

```text
(packet row in {0,1,2}, buffer offset in {1,2,3}).
```

Thus it contributes at most one center per packet, the exact rate sought for
the missing stable unit. The endpoint state is either absent or one connector
in the first or last packet, giving `1+2*3*3=19` states. No wider island,
second branch, arbitrary interior mask, or packet-dependent phase is allowed.

The complete automaton state is

```text
(row mod 3, wall mod 3, shared advance, exterior phases,
 branch row, branch offset, endpoint state).
```

There are 10 wall packets and 1,251 locally valid phase paths. Every accepted
transition checks all unit cells crossing the two outer walls and internal
branch. Endpoint states are then checked directly for unit cells, forced
cycles, and branch/exterior forced-support intersection.

## Stable Singleton States

Exactly 60 states have an endpoint-only singleton articulation at each of
`k=7,8,9`. For every retained state the perimeter cap is optimized by the
finite max-plus forest automaton from the staircase classifier. The cap state
contracts core components and rejects every connectivity union that would
close a cycle.

The best stable singleton state is

```text
row phase       = 2
column phase    = 2
wall packet     = (0,3,0)
wall start      = 1
branch phase    = (row 1, offset 3)
endpoint        = (top, row 2, offset 2)
articulation    = (3,8)
```

Its exact observed formulas are

```text
branch centers  = k
core correction = -6k + 7
cap              = 8k + 3
total            = 3k^2 + 2k + 10.
```

At `k=7,8,9` the totals are `171,218,271`, against targets `196,248,306`.
The successor gains are `47,53`, not `52,58`; equivalently this class has
stable gain `6k+5`, five below `6k+10`.

The endpoint state, articulation vertex, and 14-state cap interface are stable
at all three checks. The full forced graph is a forest, and every pair of
preserved-component stars intersects in at most one physical vertex.
Nevertheless the component incidence graphs are disconnected: their node/link
counts are `23/8`, `26/8`, and `29/8`. No incidence parent tree survives, and
no state reaches the target count even before parent-tree acceptance.

## Complete Obstruction

The artifact is complete for fixed width-three blank buffers, one-site packet
branches, the 19 endpoint states above, all exterior phases, all monotone
net-three wall packets, and arbitrary perimeter caps accepted by the exact
forced-forest cap automaton. There is no target family in this class.

Together with the existing classifiers, this exhausts the declared affine
interval, neighboring-residue, periodic density-one-third, one-wall seam,
width-one/two elbow-island, and width-three buffered endpoint-branch grammars.
This is a lower-gate conclusion about those finite grammars, not a global
nonexistence theorem.

Further progress requires genuinely new mathematical input rather than a
larger bounded motif table. Plausible inputs are an unbounded or non-affine
branching incidence surgery with packet-dependent memory, a direct global
dual-tree construction, or a structural theorem converting nonlocal
connectivity data into a uniform coordinate family.
