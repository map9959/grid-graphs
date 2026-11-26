# Solved square values price a full-bar strip of arbitrary depth

Let a forest on a rectangle of width `L≥2` have a completely marked
first row and `d` more rows. Let `F` count marks in those `d` rows.
Set

| `d mod 3` | `δ` |
|---|---:|
| 0 | 0 |
| 1 | `31/210` |
| 2 | `1/10` |

Then **`F ≤ (L+2)(d/3-δ)`**. In particular the deficit is linear in
the segment length in the two shifted depth phases. The additive error
is `O(d)`; the constants do not require a bound on `d`. This strengthens
the elementary full-piece estimate for the [multiscale cuts](MULTISCALE_CAP_CUTS.md).

**Transfer.** The first free row of the strip is empty by diagonal
exclusion. Delete the full row. Every remaining component, including
an isolated first-row vertex, has at most one edge back to the deleted
bar, since that bar was connected. Repeat copies of these `d` free
rows tangentially with two empty columns between consecutive copies.
The neighborhoods of marks from distinct copies are disjoint. This
extension can be appended along any straight old side: the old marking
requires only a subset of the contacts that the full bar required, and
every new component still attaches at most once.

Take the side `n=3k+1` comb. Duplicate an ordinary interior pitch row
`d` times, giving a physical forest of height `n+d`, width `n`, with
exactly `d(k+1)` additional marks. Each pitch-row component has just
one center; duplicating it extends the center path and its lateral
leaves, preserving the attachment partition. Append the repeated strip
along the long side, fitting at least `floor((n+d)/(L+2))` copies.
The result is a forest in side `N=n+d`. For *fixed* `d,L`, the
construction works for arbitrarily large `k`.

The comb has `n²/3+(11/10)n+O(1)` marks. The solved residue-two and
zero squares have respectively `N²/3+(20/21)N+O(1)` and
`N²/3+N+O(1)` marks. Subtract the known terms, divide by `n`, and
let `k` grow: `F/(L+2) ≤ d/3 + β_N - 11/10`. This gives the last
two deficits in the table. For `d=0 mod 3`, repeat any such rectangle
in both directions with two blank rows/columns between copies.
The limiting density of marks of a grid forest is at most `1/3` by
the edge ledger. Thus `(F+L)/((d+3)(L+2))≤1/3`; to remove the
constant from the two blank columns, keep the full row through the
blank columns in the tangential repetition (the adjacent row is
empty). This gives `(F+L+2)/((d+3)(L+2))≤1/3`, as required.

**Consequence for a possible residue-one counterexample.** Its full
spanning rows and columns can only occur at indices divisible by
three (zero based) for `n=3k+1≥103`. Indeed an off-phase full row has
the two free depths congruent to 1 and 2. Apply the strip price on
each side *and round each side separately*. The total is at most

```
3k²+6k+1-ceil(31(k+1)/70)-ceil(3(k+1)/10) ≤ C(k).
```

At 103 the two individual fractional subtractions are 15.5 and
10.5: subtracting just their sum would miss the exclusion. The
general rounding is checked in `DenseCollarPrice.lean`.

**Stability for incomplete bars.** Let an off-phase row have `h`
vacancies, with `b` gaps of at least two blanks *between* successive
marks. For `h < floor(n/2)` it can be completed at net loss at most
`h+b`, on the actual board. Consequently a score above the comb
requires `h+b ≥ 1+C(k)-offBar(k)`, where `offBar` is the displayed
full-row bound. In particular **every off-phase spanning row and
column has `35h ≥ k-34`** (trivial for the omitted large `h`).

Erase marks on the two neighboring lines and erase depth-two donors
backed by vacancies. Their combined number on each side is at most
`h`: inject neighboring-line marks into adjacent diagonal vacancy
positions, which cannot back depth-two donors. For even width pair
consecutive indices. For odd width, some even index is absent on
the neighboring line (otherwise all odd bar sites are vacant); pair
all indices except that one by consecutive pairs on its two sides.
Now the old marked row meets the remaining deeper forests only via
spokes at marked bar positions. Contract its `b+1` marked pieces
(including intervening singleton holes), then the deeper components.
The incidence graph is a forest, so there are at most `b` contacts
beyond the first per deeper component, jointly over both faces.
Erase those depth-two donors; the completed row is now safe.
The empty-row case requires no joins. Replacing `2b ≤ h` in the
rounded bound gives the stated linear inequality. Physical tree
replay: `python3 -B -m analysis.research_program.spanning_bar_repair`.

**Lower comparison.** A full-bar strip of depth 5 admits deficit
`1/6` per column; depth 7 admits `4/21`. Additional triples can be
inserted at the bar by adding another full bar three rows away,
disjoint from the old one. The bounds above do not identify the
best strip in either shifted phase. `full_bar_price` verifies both
periodic words with the rooted physical frontier, then glues their
finite versions to the side-103 comb and completes the resulting
forests to trees:

```
python3 -B -m analysis.research_program.full_bar_price
# side 108: 3984 designated marks, 11663 tree edges, 3985 full vertices
# side 110: 4128 designated marks, 12099 tree edges, 4129 full vertices
```
