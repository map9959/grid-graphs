# A sharp infinite subprogression of residue two

Write `T=3k²+7k`. For `n=59+42t`, `k=19+14t`, `t>=0`, the
construction `zipper_rails.build(n)` gives

    P(n,n) = T − 2 − 2t.

This is a construction proof with two finite frontier checks, not a
Lean theorem. The upper half follows directly from the proved period-three
dual `P<=T+floor((23−2k)/14)`. It does not imply sharpness for every
`k mod 14`.

## From the witness at 38 to a different optimum at 41

The explicit side-38 witness admits a 21-by-21 enlargement: insert
three copies of its seven-row transition band, displacing the interface
by three columns each time. Widen the other rows by whole rail pitches
on either side (`seven_rail_block.block`). This gives 1211 at 59.
Two physical top-boundary repairs raised it to 1213; the saved grid
`block_repair_59.txt` can be checked with `extend_forest_28.verify`.
These are near misses, not the sharp construction below.

At 41 no score-597 seam extension was returned among 1521 placements
retaining all old marks. Unrestricted search instead found `forest_41.txt`,
which the new row generator reproduces exactly. It scores 597, one above
the best literal duplication at 38, and meets the unrestricted upper.
The seven-row interface in this new witness moves left rather than right.

## Geometry and why it stays acyclic

Index sites from zero. The first three rows of the generator are fixed
top patterns. Then two fronts advance from columns `0` and `n-1` by
three columns per row until their tips have separation four. Put
`F=(n−5)/6=9+7t`; there are `F` advancing rows. After the advance
the regular rail row `A(L)` consists of `0,3,...,L` and
`L+4,L+7,...,n−1`, with `L=3F`. The middle has
`n−8−F=42+35t` rows: `6+5t` whole seven-row bands, no partial band.
Each band starts with two regular rows and moves `L` left by three.
The cap is the last five rows of the generator with final `L=9+6t`.

To verify the prefix, consider the marked vertical runs and their
incident leaves. Runs in the central wedge have columns `2 mod 3`,
start at row 2, and end as the fronts approach. Distinct such runs are
three columns apart. Each meets the top bar at most once, through its
row-1 site. The rightmost one, at `n−3`, misses the bar and instead
meets the vertical right boundary through `(2,n−2)`. The exterior
runs start at column `3a` in row `3+a`, and at their reflected sites;
the right boundary itself starts in row zero. They are three columns
apart on each side. Apart from the rightmost contact just noted,
no exterior run meets a wedge run: on the left the nearby wedge
columns `3a+2` and `3a−1` end no later than rows `a+2` and `a+1`,
respectively, so Manhattan distance is at least three. Reflection
gives the same calculation on the right, treating its boundary run
separately. The same bounds apply at the first regular row as the
last two exterior runs start. The left boundary starts three rows
below the bar; the two boundary marks in row zero have two holes
between the right endpoint of the bar and the right corner. Thus
the prefix has no cycle and the exterior rails are mutually disconnected.

On the second regular row each marked rail vertex is in its own
frontier component with its immediate horizontal neighbors; the one
uncovered site in the gap is a singleton. Indeed the only vertical
edges between the two identical regular rows are on the rails.
This is the invariant tested by `zipper_frontier.py`. The checker
contracts the old frontier components, adds all forced edges of the
next row, rejects any edge within a component, then projects onto
the new frontier. Starting just after the two regular rows, the last
five band rows and the next two regular rows restore exactly the same
invariant with `L−3`. For the final band, substitute the five cap rows
for the next two regular rows: this also creates no cycle.

Why one finite check suffices for these transitions: use the representative
width 23, starting `L=12`. Every larger instance needed here inserts
whole three-column rail pitches on the left and right. For the last
band the starting `L=12+6t`; for earlier bands it is larger by a multiple
of three. The length to the right is always at least that in the test
and congruent modulo three. In the middle transitions the extra pitches
are straight isolated rails, each carrying an independent frontier
triple (rail plus its two leaves). In the cap they are still disjoint
vertical rails until the empty penultimate row, where each leaves one
independent tip on the frontier. The full bottom row can therefore join
each tip once without closing a cycle. Pitches may be inserted between
the boundary and the changing central sites; even in the minimal left
cap there are unchanged rails at 0 and 3 with two empty columns between
them. Inserting at this gap does not alter a central incidence. The
final bottom bar simply grows by three vertices per extra pitch.

## Count and replay

The top three rows contain `n−2, 1, k+1` marks. Each advancing row
has `k` (the two fronts replace one central rail from each end per
step). Each band contributes `7(k+1)+1`: six rows have `k+1` marks
and its center-marked third row has `k+2`. The cap counts are
`k,k+3,k,0,n`. Summing gives `T−2−2t`. This matches the upper for
all `t`, not just the physically replayed examples.

```
python3 -B -m analysis.research_program.extend_forest_23 --41
python3 -B -m analysis.research_program.patch_square --replay 41
python3 -B -m analysis.research_program.zipper_frontier
python3 -B -m analysis.research_program.zipper_rails
```

At sides 38 and 59 the deficits are respectively 1 and 2; this
matches the desired change across seven increments of `k`. The
construction above repeats **two** such blocks at once (side +42).
The intermediate `+21` sides are not covered by this induction.

## Side 53: the last band cannot fix the deficit, but the opposite corner can

`P(53,53)=985`. The unmodified side-53 prefix of 13 rows already seals
off the top-left corner's component from the top-right corner and all
later rows. Therefore every forest completion of this prefix can be
oriented with at least two corner sinks. Averaging over the eight
symmetries changes the corner row's lower RHS from one to two; its
multiplier is `-9/14`. This improves the upper from `13793/14` to
`6892/7 < 985` **for this prefix only**. Changing just the final band,
or even replacing all forty remaining rows, cannot improve on 984.

Instead a forest search varying the top-left six rows and twelve columns
found a gain of one. The resulting certificate differs on just nine
sites, leaving the entire bottom cap intact. The saved grid and its
union-find replay show 2807 acyclic forced edges in two components;
the completed tree has 2808 edges and exactly 985 full-degree vertices.
The original unrestricted bound `13793/14 < 986` then gives equality.

```
python3 -B -m analysis.research_program.cap53_prefix
python3 -B -m analysis.research_program.repair_53
```

The literal nine-cell edit does not simply transplant to larger sides.
Extending its diagonal of altered cells to column `9+6t` at `n=53+42t`
does give further matching **finite** witnesses: 3097 at 95, 6385 at
137 and 10849 at 179. The [uniform repaired-prefix proof](REPAIRED_ZIPPER_PROGRESSION.md)
now establishes sharpness at every `53+42t`.
