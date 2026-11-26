# The last exceptional residue-two tail

On `n=35+42t`, `P(n,n)=U(k)-1`, where `n=3k+2` and
`U(k)=3k²+7k-floor((k-5)/7)`. The rail supplies the lower bound
throughout. For example at 707 the forced forest replay returns
`(167287,499847,2,499848,167287)` after extension to a tree.

The finite exclusions through 623, the [two-gap cover](FOLDED_STRIP_ENLARGEMENTS.md)
and the [first synchronized exclusions](SYNCHRONIZED_FRONT.md) leave
only axis 1, odd `57≤q≤k-2`, `k=207+14t`. Here is the exclusion.

**North fan.** Use the fan word from the synchronized exclusions.
Seed odd isolates at base 57 with arbitrary insertions at 28 and 68
when `k-q≥24`, or at `81-(k-q)` with only the first insertion for
smaller eastern margins. The replay checks the entire top word and
rows 1 through 8, including the insertion interiors. For odd `q`,
the same step starting with center length 19 (rather than 20) gives
the fan until `y=floor((q-15)/6)` with `c=q-6y-2` in `{13,15,17}`.
Both row `y` and row `y+1` are known. The three intervening runs have
lengths `a=3y-2`, `c`, and `r=k-a-c-6`. In particular `a,r≥16`.

**Remaining-height catalogue.** Plant just those two rows in an
open-north rectangle with real west, east and south boundaries.
Allow arbitrary even amounts of extra width in each outer run,
and arbitrary even height below row 18. Base outer lengths 16/17
and heights 39/40 cover every parity. Both bonds of each expandable
block are homogeneous; every occurrence keeps its own full domain.
The whole rectangle is on the same physical square. From row `y+6`
on, every deep tile passes both axis filters; in the interior windows
used below its possible masks belong to
`{3,6,7,8,12,16,32,33,96,192,264,384,448}`. From row `y` through
`y+6` the eastern plateau (starting at `q-3y+2`) stays mask 7.

**Which teeth can leave the top of a window?** For `u>q`, the line
at physical column `3u` runs straight back to a north tooth. For
`q-3y+3≤u≤q`, its first mark is at physical row `q-u+2`, not at a
tooth. Above the slab this is a separate dangling line, with its
unmarked leaves. In the explicit fan word its marks have exactly
that column, at every height from birth to the cut. No other mark is
within Manhattan distance two of them, so their forced stars cannot
meet another component. `NorthFanLines.lean` proves these facts from
the right-hand tile bits, including the birth row. Only the right
part of the fan is used: even the neighboring tile to the west is
east of the left three transition tiles (`c≥13`). The north tooth
row is 1, whereas the birth height is at least 2. Subsequent mask-7
rows preserve this description when the tile immediately west is
also mask 7. At a cut in this plateau the only crossing per tile
is the straight edge at `3u`. Thus one may suppress leakage through
the cropped top for the dangling lines: each removed component has
only one incidence and no root. For a rooted line instead add *one*
attachment to the common root. Side cuts remain open, including at
the ends of a sealed top edge. All window marks below the input row
remain free.

**Speed certificates.** Maintain a suffix `u≥f` of mask 7 at the
current row, dangling for `f≤u≤q` and rooted for `u>q`. Initially
`f=q-3y+3` at row `y+6`. Once the dangling lines run out, the
invariant may be weakened by discarding columns up to `q+1`.
If the next `w` columns are dangling, use an open-sided `w×H`
window with a sealed top. In each test column `d-1` stays mask 7 at
*every* row through `s`. A 7 tile forces its eastern neighbor to
be 7, including at the true east fringe (checked for tags 7..37).
So the suffix starting at `f+d` has a full mask-7 buffer on its
west during the extension; all its line histories transfer.

| rows advanced `s` | columns lost `d` | width `w` | test height `H` |
|---:|---:|---:|---:|
| 6 | 4 | 5 | 13 |
| 13 | 7 | 8 | 20 |
| 20 | 10 | 11 | 27 |
| 27 | 13 | 14 | 34 |

For rooted columns use an open-sided `10×10` window, advancing four
rows and losing three columns. Rooted paths need only *stay connected*
to their own tooth, so do not need the extra western buffer. Stop
the windows before the southern fringe and use the actual south
boundary: with `14≤h≤43` rows left, the easternmost `floor(3h/4)+3`
columns of 7 on the top and **just the last line** attached to the
north root already give an empty rectangle. All other top contacts
are open. Both physical forest implementations replay these tests.

**Size coverage.** For `207≤k<2000` the arithmetic loop in
`src/bin/fan_speed_cover.rs` verifies all 67,467 `(k,q)` pairs:
at each row keep the smallest established `f` (a smaller one implies
all larger starts). It only applies windows wholly inside the proven
bulk, and ends in one of the checked caps. No squares are enumerated.
For `k≥2000` use the 13-row dangling step (`18×24` also checked).
With at least 44 rows left, apply it while `f+17≤min(q,k-8)`; then
use the four-row rooted step from `q+1` while at least 44 rows remain.
This switch only moves east: a previous dangling step required
`f_old+17≤q` and advanced seven columns. At every reachable height
with ≥31 rows remaining, there are ≥64 columns left from the
applicable front, by `odd_speed_room`. Thus each step fits and
the final height 31..43 has a checked 64-column south cap. This
argument uses the same width and height throughout.

Together these exhaust the one-gap case. The proof uses only
necessary domain deletions, exact mask transitions and arithmetic.
The computational checks are external to Lean.

```
rustc --edition=2021 -O src/bin/coupled_mask_grid.rs -o target/coupled_mask_grid
export PYTHONPATH=target/pb-python
python3 -B -u -m analysis.research_program.odd_fan_bulk
python3 -B -u -m analysis.research_program.rooted_window_speed
python3 -B -u -m analysis.research_program.fan_speed_cover
python3 -B -u -m analysis.research_program.fan_speed_replay
rustc --edition=2021 -O src/bin/fan_speed_cover.rs -o target/fan_speed_cover && target/fan_speed_cover
(cd lean && lake env lean GridGraphs/Geometry/NorthFanLines.lean && lake env lean GridGraphs/Geometry/SynchronousFront.lean)
```
