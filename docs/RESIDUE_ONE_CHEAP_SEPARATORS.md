# Short descriptions of cuts in an unrestricted high-scoring square

Write `n=3k+1`, `q=floor((3k-13)/10)`, and suppose a forest scores
at least `3k²+5k+q+g`, for `k≥5`, `g≥0`. In **each direction** there
are at least `1+q+g` disjoint three-line blocks whose middle line is
a concatenation of **at most five intervals**, each empty, full, or
marked in a single residue modulo three. The intervals can have arbitrary
lengths and need not have distinct types. In particular this applies
to an unrestricted maximizer, since the comb supplies the lower bound.
At side 103 a putative improvement requires at least ten such blocks
on each axis.

Take the row blocks `1..3, 4..6, ..., 3k-2..3k` in zero-based
coordinates. Bill a block for each start of a maximal marked run in
the three rows and each isolated vertex of the forced graph on the
middle row. A run starts where a mark has neither a west nor a north
marked neighbor; acyclicity precludes diagonal marked pairs, so these
are exactly the starts of the straight runs (including singletons).
With `R` runs, `c` forced components, and `b` missing boundary
incidences (an unmarked corner counts twice), edge counting gives
`3M+R+b+c=n²+4n`. The total of the row bills is at most `R+c-1`
because at least one component contains a mark. Also `b≥5`: at each
corner its two rim neighbors cannot both be marked. Four disjoint
such pairs already require four omissions. With exactly those four
omissions no two are adjacent for `n≥7`, so the full perimeter cycle
would be forced. Thus the total row bill is at most
`3k-1-3q-3g`. At most `k-1-q-g` blocks can pay three or more.
Transpose for the column bound. The choices on the two axes refer
to one and the same marking.

**Why the description is short.** For a block of bill `e` the sharper
bound is `1+2e` intervals at *any* width `3k+1≥4`. A finite transfer
reads the physical column of four bits (the row above, then the three
block rows). It retains the partition of these four frontier sites,
rejects cycles and diagonal pairs, and charges each start and each
middle-row isolate exactly when the needed neighbors become known.
On the middle word it tracks the five possible interval types,
extending the current interval while any type still matches. Taking
the longest possible prefix minimizes the number of intervals,
because suffixes of allowed intervals are allowed. Give a transition
weight `additional intervals − 2·bill`. The all-length transfer
verifies 2,282 integer inequalities on 382 states: the excess above
one initial interval is nonpositive at every accepting end, including
the last isolate debit. At bill zero the only possible middle line is
the ordinary phase-zero rail profile. For bills 1 through 4 the
local maxima are 3, 5, 7 and 9 pieces.

**Scope.** This permits synchronized horizontal and vertical separators
in unknown optimal boards without assuming they already have a comb
core. It does not imply that the separators are whole rail profiles;
terminal connectivity and the score of the adjoining rectangles still
have to be priced. A balanced cut follows by dropping fewer than
`1+q+g` blocks near the two ends in total.

```
python3 -B -m analysis.research_program.cheap_cross_section
```

## Detouring around every long empty interval

In the same three-row block there is a simple left-to-right path with
`L` vertices, `m` marks, and `C` components of the induced forced forest
on the path vertices (including isolates), such that, for `K=4+13e`,

```
n ≤ L ≤ n+2(K-1),        |L-m-2C| ≤ 10K .
```

In fact the path has at most `K` horizontal chunks, each full or
pitch-three, including single-site words, with at most two extra sites
per join. Different billed blocks give disjoint paths. Thus a balanced
cheap separator need not contribute any *long empty* terminal interval.

Start with the middle row's `P≤1+2e` pieces. Within empty pieces,
split out the at most `e` charged columns as singletons. This leaves
at most `P+e` clean or nonempty pieces plus `e` charged singletons.
On a clean empty piece discard its two endpoints temporarily. South
neighbors can be marked only in a prefix: a birth after an empty
south site would have neither a west nor a north mark. In the rest,
the north neighbor is marked, or else the middle site would be
isolated. Keep the singleton endpoints on the original middle line,
follow south on the prefix and north on the suffix. This uses at most
four chunks per clean piece; short pieces take at most two singletons.
Moving between chunks vertically in the new column preserves simplicity.

Along an isolated full or pitch chunk, `length-marks-2·components`
is between `-2` and zero. For pitch, each mark has two unmarked
neighbors except for end truncations, and any uncovered vertex is
an end isolate. Each path join changes the sum by either zero or two.
There are at most `3K-2` chunks including the added singleton sites.
Extra grid edges between nonconsecutive path vertices are horizontal;
across a column boundary their number is at most the number of vertical
steps in the next column. Thus there are at most `2(K-1)` chords.
Including their forced edges changes the discrepancy by at most
`4(K-1)`. This proves the stated bound for the *actual* cut components.
It does not specify which components the exterior connects.

`python3 -B -m analysis.research_program.detour_separator` checked all
411 cheap cuts of the two orientations of the combs at 103, 193 and
403. The largest observed extra length was four and the largest
absolute terminal discrepancy was six.
