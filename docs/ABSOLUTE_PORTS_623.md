# Side 623: equal absolute hop rows

**Axis 1 still admits deficit 1,062** with at most four connections per
cut, even when all columns have the true common height and every paired
connection has the same absolute row on both sides. This admission is
in the one-gap interface relaxation. **Axis 2 no longer admits that
price.** Requiring physical tile overlaps as well rules out every
one-gap candidate at side 623 with at most four hops per cut, on either
axis. This does not exclude candidates with a more crowded cut.

## Witness with a fixed height, not an insertion argument

Use tile coordinates on the `207 × 207` chart; a vertical cut has
`621` physical rows numbered `0..620`. The north isolate has index
`q=67` (rim distance `2+3q=203`). Until column 62 there are no outgoing
hops. The first two occur at rows 37 and 40 of its east cut. Here is
the complete nonconstant part of the outgoing row pattern. `W` and `E`
denote a two-site hop skipping the west or east site, respectively.

| column | outgoing hops |
|---:|---|
| 62 | 37E, 40E |
| 63 | 37W, 44E, 47E |
| 64 | 41W, 44W, 51E, 54E |
| 65 | 48W, 51W, 58E, 61E |
| 66 | 55W, 58W, 65E |
| 67 | 62W, 69E |
| 68 through 204 | both rows of column 67 plus `4(i-67)` |
| 205 | 614W |
| 206 | empty |

Each column was filled using the existing overlap/axis catalogues and
its actual isolate offset, including the real north and south fringes.
The transfer checks the middle column's marked components, their teeth,
and their incidences to the four ordered ports. Backtracking also
matches the component partition carried from the preceding cut. The
column costs are `3` for indices `0..62`, `7,9,9,9,7` for `63..67`,
`6` for `68..205` and `4` at `206`. Thus the price is exactly
`63·3 + 2·7 + 3·9 + 138·6 + 4 = 1062`.

The general search represents a cut by a word of length `k`, regardless
of how few hops are present. Its `j`th symbol codes direct/skip-west/
skip-east/no-hop separately at rows `3j,3j+1,3j+2`; first and last
symbols also carry the shared end masks. Suffixes with identical
continuations are stored once in a directed acyclic graph. Transitions
consume and emit one symbol at the **same** tile row. Leaves retain
partition-indexed bitsets of exact prefix deficits. Word union never
turns a missing price into an attained one. The chart index is clipped
only for selecting a homogeneous *catalogue*, never for positioning a
hop or shortening its column. In particular a displacement by three
rows can no longer pass a seam check merely because the phases agree.

## Physical replay distinguishes two kinds of agreement

The extracted witness replays 293 forced hops across 206 shared cuts.
Independently constructing the graph of actual middle-column marks,
with the matched crossing edges and all internal axial edges, gives
127,485 marks and 413 acyclic components with exactly one tooth each.
This is precisely the graph represented by the absolute-port state.

Superimposing the central tile assignments as one board introduces
**58 additional axial hops**, although it introduces no diagonally
adjacent pair of marks. The first extra hop is from `(11,6)` to `(13,6)`
(zero-based crop coordinates). No marked endpoints are missing from
the 293 advertised hops. Every extra edge either closes a cycle in a
singly rooted tree or connects two singly rooted trees. The two-column
overlaps disagree at 81 tile-row positions in this replay.

This is more than an accident in choosing a backtrack. Keep this fan's
positions, hop types and end masks, free the entire column interiors,
and **discard the deficit constraint**. If the center masks must not
create any unadvertised axial hop, no prefix gets through column 64.
If the two entire overlapping masks must agree at every tile row, no
prefix gets through column 62. These two pinned tests concern this fan.

## Free-isolate and free-pattern tests at 623

A separate east-to-west computation leaves the isolate and the hop
words free. Reversal exchanges the roles of the two port lists when
constructing the partition; it does not reflect the north-isolate
catalogue. Start at column 206 with the empty exterior word. Carry
the offset `q-i`, clipped to `[-4,5]`: on a step west it increases
by one, except that `-4` can also wait and `+5` stays saturated.
Filtering offsets at the two ends enforces `1≤q≤205`.

* **Absolute rows, axis 2:** the terminal bitset up to and including
  deficit 1,062 is empty. All offset classes die by column 4 (zero-based).
  Truncation at 1,062 is safe: marks of every tile in the catalogue
  union have popcount 1, 2 or 3, so no future column refunds deficit.
* **Full shared masks, axes 1 and 2:** add the ordered pair of
  overlapping tile masks to *every* symbol, rather than just to the
  north and south symbols. Remove the price filter altogether. On each
  axis the last offset dies on adding column **53**, even though the
  west boundary has not been imposed. The right-side search has no
  predecessor on cut 52.

As a positive control the same reverse full-mask routine accepts eleven
consecutive columns of an independently rooted physical region, with
the actual boundary words and exact price at every step. The audit
also checks nonnegative loss on all 33 catalogue masks.

Consequently, at side 623 **some cut numbered 52 through 205 must
carry at least five forced connections** in any physical one-gap
equality witness in the normalized chart. Only those cuts were
processed before extinction. The result is necessary even if the
western part of the board is unconstrained; it does not give an
unrestricted upper bound and says nothing about two-gap equality.

## Uniform axis-1 witness in the absolute-row relaxation

For the extension of the full-mask exclusion to five hops per cut, see
[Five forced connections per cut at side 623](FIVE_PORTS_623.md).

Put `k=39+14t`, `q=19+4t`, and let the first row in the fan be
`13+2t`. Use exactly the same offsets relative to `q` and to this
first row as in the table above. This pattern attains `198+72t` in
the axis-1 row-matched relaxation for **every** `t≥0`. Direct fills
handle `t=0..8`. For `t=9,10,11`, the audit finds repeatable
segments of one or two **blank tile rows** in the homogeneous
interior. Here “blank” means no hop on either cut; it does not
mean unmarked. The full tile triple, rooted frontier, internal
partition, retired components, port counts and running deficit
coincide on both ends of each repeated segment.

To pass from any of those three bases to `t+3s`, add `12s` western
copies of column 7 (empty partition, cost three) and `10s` copies
of columns `q+9..q+11` (same incoming and outgoing partition `(1,0)`
at the three-column join, cost 18). The north/south rim pairs are
constant at each insertion. In each original column before the
second insertion, add `2s` blank tile rows above the contacts and
`40s` below. In the `h`th inserted three-column block, counting from
zero, the corresponding numbers are `2s+4h` and `40s-4h`. Farther
east add `42s` above and none below. In columns with no contacts
all `42s` may go in one verified blank gap. Every requested count
is nonnegative and even. The audit checks the needed cycle on each
required side of every base column. Thus actual rows match on every
new seam, including both horizontal joins; the width increases by
`42s` and the cost by `216s`. As a check, the base templates also
materialize and physically replay the matched edges at sides 623,
665 and 707. This is an interface construction only.

```
export PYTHONPATH=target/pb-python
python3 -B -m analysis.research_program.absolute_port_audit
python3 -B -m analysis.research_program.absolute_port_fan 1 207 67 37
python3 -B -m analysis.research_program.absolute_ports 2 --reverse
for axis in 1 2; do
  python3 -B -m analysis.research_program.absolute_ports "$axis" --reverse --full-masks --support
done
python3 -B -m analysis.research_program.absolute_fan_pump
python3 -B - <<'PY'
from analysis.research_program.absolute_port_fan import whole_masks
for no_extra in (True, False):
    assert not whole_masks(1,207,67,37,no_extra)
PY
```
