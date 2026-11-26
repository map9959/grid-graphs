# Gluing rooted bands at the exact one-gap budget

For every `k=39+14t` (`n=119+42t`) the [band projection](ROOTED_TRACK_INDUCTION.md)
still admits a north isolate at distance five and **no forbidden east
arm** after joining a full-height eastern region of width `3k/4+O(1)`
tile columns. This holds separately for both deep axes. Every catalogue
plaquette in that region shares its tile masks, every forced edge is
present, and every component containing marks is a tree attached to
**exactly one** crop tooth. No such component relies on a future
attachment across the open western cut. This is a projection, not a
construction attaining the upper bound.

### The cut state

Work from east to west. Start with `H=12*floor((k-12)/16)` columns
(subtract three when `t mod 8=5` in the fully rooted test). Use the
diagonal rows of `neighbor_diagonal.row` as **columns**. This is a
candidate filling, not a symmetry assumption on the rooted square:
the test transposes every quadruple back into the physical `0133`
catalogue. The physical easternmost mask is never 192. The eastern
region costs `6H-2`. Because `H` is divisible by three, its western
frontier has `s=k-4H/3` initial tiles before the two transition tiles.

Label sites down that frontier from zero, relative to the first tile.
Its first `3s+2` sites are connected to the virtual root (the
contracted perimeter). Every other site has a distinct frontier class.
**Only one** of those nonroot classes contains a mark anywhere in the
processed region: its unique frontier site is `3s+4`, itself unmarked.
All marked components that have already left the frontier have a root.
The group transfer checks this strengthened invariant, retaining the
presence of marks and connection to the root; when a marked unrooted
class disappears the transfer fails. As in the [diagonal induction](ROOTED_TRACK_INDUCTION.md#coupling-the-southern-strips),
there are four reduced triple-column gadgets. Inserting homogeneous
margin tiles extends straight rooted paths with leaves, or adds unmarked
singleton frontier sites. Neither changes the distinguished component.

### A freely filled neighboring band

The adjacent band uses this *same* exposed column of marks on every
cross-cut plaquette. A forced edge to the rooted prefix adds a real
contact to the virtual root, even when only its eastern endpoint is
marked. A second route to that root is a cycle. At site `3s+4` the
new neighbor must be marked: it is the sole exit for the unrooted
component. Joining there attaches a tree by one edge. Other nonroot
frontier classes are unmarked singleton sites, each with at most one
contact. In the strict test no marked component may disappear unless
rooted, nor may an unrooted marked component remain at the end. No
marks inside the new band are frozen.

The DP retains a bitset of exact costs. An independent two-/four-wide
bulk band could cost 5/10; at the original tested cuts their minimum
costs are **12/24** respectively when further escapes are allowed.
In the four tested two-wide cases, requiring *all* marked components
to be rooted gives an empty cost set. With four columns, the strict
minimum was **`s+21`** at each `s` below. The minimum checks allow all
accepted paths; a separate backtrack selects an extendible witness.

| `t mod 8` | `s` (strict test) | Four-column cost | Total deficit at representative |
|---:|---:|---:|---:|
| 0 | 23 | 44 | 198 |
| 1 | 21 | 42 | 270 |
| 2 | 19 | 40 | 342 |
| 3 | 17 | 38 | 414 |
| 4 | 15 | 36 | 486 |
| 5 | 17 | 38 | 558 |
| 6 | 27 | 48 | 630 |
| 7 | 25 | 46 | 702 |

### Why the costs apply at all lengths

The part beyond the transition, in transposed coordinates, is
`448,...,448,192`. In the actual catalogue a 448 there forces 448 in
the next column west; the final pair forces the clipped 192. These
implications are checked before the search. Lengthening the
homogeneous tail only subdivides parallel marked paths and adds leaves:
it neither creates new mask choices nor changes the deficit. Conversely
the chosen paths have an explicitly checked self-loop of their full
labelled state at `s+4`, of cost zero. The compulsory attachment is
outside the insertion.

In the remaining western part use the independently replayed bands
with fixed-total costs. Passing from `t` to `t+8` adds 112 tile
columns, 84 in the joined east and 28 in the west. The eastern cost
rises by `6*84=504`, with unchanged `s` and interface surcharge.
Seven more four-wide western bands contribute 72 (six cost 10, one
costs 12). The total increment 576 is exactly that of
`5k-1+floor((k-5)/7)`. For each starting class the western star band
absorbs the surcharge at an explicitly attainable deficit. The checker
reconstructs the eight classes and an induction enlargement in memory,
traversing the **unsliced** eastern graph independently and counting
edges, vertices and physical teeth per component.

```
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.joined_arm_budget
```

The remaining gap is across the western cuts. A western component that
touches two distinct already rooted eastern branches would close a
cycle through the perimeter. This test does not certify that the rest
of the square can avoid such contacts, or that the tile assignments
extend to all physical arrow and face data.

The [western continuation test](WESTERN_CUT_TRANSFER.md) rules out
extending any fully rooted four-column cap by even one column. It also
gives a donor-independent deficit bound for opposing arms.
