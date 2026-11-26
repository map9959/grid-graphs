# Relating arbitrary square forests to a four-sided wired square

Let `W(m)` be the maximum number of marks in an `m×m` forest when
adding one edge from **each marked boundary vertex** to a common
external root must still give a forest (one edge even at a corner).
For `n=m+4≥11`, a square marking of score `M` and `g` missing
perimeter edges satisfies

```
W(m)+4n-13 ≤ P(n,n),       M ≤ W(m)+4n-5+c₀+g,
```

where `c₀≤4` counts unmarked corners. This applies with no rail
profiles, selected axis or bound on collar changes.

For the upper comparison delete the first two rings. For each crop
tooth (marked crop-boundary vertex) choose a normal foot on the original
perimeter, preferring a marked one when there are two choices. The
chosen feet and the intervening depth-one vertices are distinct.
Each backed tooth already has a forced two-edge path to the old rim.
Contract the components of the cropped forest and, separately, the
components of the forced *perimeter edges*. Those two-edge paths form
a bipartite forest, since a cycle would lift to the original forest.
The rim has `g≥1` components. Thus the number of backed teeth beyond
the first per crop component is at most `g-1`. Delete all unbacked
teeth and that many duplicates (or simply keep one tooth per component).
Deleting marks cannot create an extra connection.

Let `b` count missing rim incidences, corners twice. Depth-one marks
and unbacked teeth **together** cost at most `b`. On a straight side
charge each depth-one mark one half to each of its two diagonal rim
sites; they must both be unmarked, and each incidence receives at
most one unit. An unbacked tooth charges its own missing foot one
unit. The two depth-one sites that could debit this incidence are
diagonal to the tooth and therefore unmarked. At an inner corner
counting both depth-one side charges can only overcount. The rim
mark count itself is `4n-4-b+c₀`. Summing gives the stated upper.

For the reverse construction, place the wired crop at offset `(2,2)`,
delete at most its four marked corners, leave depth one empty, and
add the perimeter except at `(0,1),(0,2),(1,n-1),(n-1,n-2),(n-2,0)`.
The forced rim is a path. A depth-one corner cannot join its two
incident perimeter sides; every crop component attaches at most once.
The resulting forest extends to a tree.

**Comparison to residue zero.** When `m=3l`, let `d_s` count the
normal edges crossing from crop side `s` to its neighboring line
that have at least one marked endpoint. For any adjacent `s,t`,
every wired crop of score `w` satisfies

```
w ≤ 3l²-3l+5 + d_s+d_t .
```

Place the crop in side `m+3`, one site from `s,t`, two from the other
sides. On the two near sides delete the old boundary marks, and on
their first inward lines delete those marks not backed by an old
boundary mark. These deletions cost at most `d_s+d_t`. Delete the
four possible new corner teeth. Every remaining tooth either is an
old far-side tooth or was joined to its deleted backing tooth by an
edge. Its original component therefore certifies that it cannot be
joined to a different surviving tooth: the assigned original teeth
are distinct, including across the two near sides. Use the same
perimeter path as above. Applying `P(m+3,m+3)=3l²+9l+4` and subtracting
the added `4(m+3)-9` rim marks gives the inequality.

**Comparison to residue two.** For adjacent sides `s,t` let `T_s,T_t`
count their marked boundary vertices in the wired crop. Then
`w + T_s + T_t ≤ P(m+5,m+5) - 4(m+5) + 17`.
Delete the at most four corner marks. Duplicate the two chosen side
words, extending the crop one row and one column with an empty new
corner. Marked sites on each duplicated side are at least three apart
(otherwise their forced stars would join two wired teeth). The only
edges back across the duplication cut join corresponding copies of
a tooth. The lateral leaves are distinct; any new tooth near the
elbow traces back to its own original component. Thus the enlarged
crop is wired. This gains `T_s+T_t` less at most eight for the
deleted corners and their would-be duplicates. Reframing adds
`4(m+5)-9` with no further corner loss.

**Unrestricted interpolation.** The twelve-gap sector dual prices the
twice-counted rim-gap row at `-1/6`. Evaluating the same feasible
dual at the *actual* number of gaps gives
`3M+g ≤ 9k²+16k+3` on the step-six charts from 103 and 112.
Combining with the upper comparison and `c₀≤4` gives

```
4P(3k+1,3k+1) ≤ W(3k-3) + 9k²+28k+6.
```

Consequently `W(3l) ≤ 3l²-αl+O(1)` with `α>2/3` would improve
the unrestricted linear coefficient even for growing gap count.
The interpolation does not itself prove that wired bound.

At 103 the comb gives a wired crop of 3,243 marks; the reverse frame
replays to a tree of 3,646 full-degree sites. These comparisons do
not determine `W(99)` or `P(103,103)`. A numerical D4 sector LP on
the wired crop still admits a deficit of only about `0.2164m` at the
tested sizes even with the adjacent-side cut; this is not an exact
upper certificate.

`cross_residue_lp` also tested the neighbor-square inequalities
directly in the unrestricted deep chart at 103. The estimated optimum
was `3648.16666` both before and after. The two aggregate inequalities
alone did not improve that relaxation.

```
python3 -B -m analysis.research_program.wired_crop_exchange
```
