# Pricing the lengths of full and pitch pieces on crossing interior cuts

Take one horizontal and one vertical detoured cut in a residue-one
square. Use the [three-line construction](RESIDUE_ONE_CHEAP_SEPARATORS.md)
in each direction. Let `K` be the total number of horizontal/vertical
chunks in the two cut descriptions, and `F` the sum of the **lengths**
of their full pieces. Singletons can be treated as pitch fragments.
The chunk positions, types, and phases may differ on every board.
For any forest of score `M` on `n=3k+1` a constructive upper is

```
M ≤ P(n+7,n+7) - 14n/3 + 4F/21 + 22(K+2) + 12.
```

The value on the right uses the **solved residue two**, not a conjecture
about another residue-one square.

**Insertion along one cut.** On a pitch piece, insert seven copies of
the pitch word: each old tooth and its two leaves become one longer
tree, retaining their contacts on the two sides. On a full piece
insert the [depth-seven motif](FULL_BAR_EXCHANGE.md), its first row
empty. It adds at least `15L/7` marks on `L` columns: its prefix and
all fourteen truncations check with zero deficit, after which its
complete frontier repeats. Each component has at most one contact to
the retained full bar. On the opposite side, the old neighbors of a
full piece of length at least two were empty by diagonal exclusion.
Any normal contact to them is a subset of the original bar spokes,
one per site. Contracting the replacement trees and identifying their
classes to the old bar class can only *increase* cycle rank in the
external gluing. Thus the replacement, which merely refines the old
single class, is safe for the actual exterior.

At each chunk boundary erase the marks in the two adjoining columns
in the five old rows centered on the original cut. Use those columns
as blank guards through the inserted band. The levels of adjacent
cuts differ by at most two, so in the whole zone where old and new
neighbors could be misaligned the two guard columns have no edge
between them. Outside the zone the old board is translated rigidly.
Within a chunk its surviving pitch centers are still at least three
apart; any newly uncovered end vertices on the added rows are leaves
or isolates rather than extra bridges. These guards leave the
previous contact argument valid independently in each chunk.

The cost is at most ten erased marks per join. At most two columns
per piece are unavailable in the band, costing at most `14/3` against
the nominal `7L/3`. A truncated pitch word costs less than seven
additional marks against its average; the full word has no further
truncation cost. Thus `22K₁` bounds all these errors on a cut of
`K₁` pieces, above its systematic `4/21` loss per full column.

**Crossing.** Insert along the first cut. Outside the five old levels
around it, every piece of the second cut survives unchanged up to
translation. Clip those pieces on the two sides and use a completely
empty insertion through the intervening zone. An empty band of height
seven creates no connection across it. This drops at most `5·7/3`
of the original promised gain and adds at most two chunks. The two
insertions yield a forest on side `n+7` and the displayed inequality.

**Linear-scale consequence.** Substituting the residue-two formula,
and using integer floor errors, gives

```
M - comb(n) ≤ (40F-31n)/210 + 22K + 81.
```

For cheap cuts `K=O(1)` (more generally `K=o(n)` suffices at the
linear scale). `F< (5/6-ε)n` improves on the unrestricted sector
coefficient; `F< (31/40-ε)n` rules out even the comb score for
large sides. The two chosen cuts refer to the *same* forest. These
tests do not require a rectangular frame reaching the rim.

There is also a version in ordinary row/column statistics. In each
three-row block every full chunk of length `L` contains `L-1` actual
horizontal marked-marked edges, and different chunks occupy disjoint
column intervals. Bound `F` above by the sum of horizontal edges in
the row block and vertical edges in the column block, plus `K`. This
can be averaged over any two families of disjoint blocks. For
near-comb squares the global bill is `O(n)` per direction, so on
families of linear cardinality the *average* number of chunks is
bounded, even without choosing bill-two blocks in those families.

**Obstruction.** A vertical comb with a single repaired-frame error
has vertical columns constant on all but `O(1)` rows. Along any
vertical cut of bounded complexity, pitch chunks in this long
region have bounded length (a pitch word agrees with a constant on
at most two consecutive sites). Thus `F≥n-O(K+1)` for that family.
The interface test closes the coefficient gap for sufficiently
mixed orientations but not for sparse frame avoidance in a coherent
bulk. See the independent [boundary debit](BOUNDARY_INTERFACE_DEBIT.md)
for propagation of extensive damage.

```
python3 -B -m analysis.research_program.phase_length_exchange
```
