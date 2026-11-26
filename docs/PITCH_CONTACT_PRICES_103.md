# Side 103: seven parallel pitch cuts, and pricing their common terminals

**Subsequent result:** the [directed slit-word proof](FINITE_CAP_SLIT_PRICE_103.md)
establishes the target cap inequalities at every depth and closes side 103.

A 3647 candidate requires **at least seven aligned pitch lines, all
parallel, and at most five full-forest junction classes**. Aligned
means that the line index is also `0 mod 3`. There may be further
parallel pitch lines at other indices. At every aligned cut the two
caps together make between 30 and 34 independent tooth joins.

### Two exact prices

In the [weighted row chart](RANK48_FACE_PRICE.md) read horizontal
lines assigning empty-stub junctions to V. Change the no-H language
to accept the all-marked-junction line. Its cost is zero: the
vacancies beyond the first number `max(0,v-1)`. All other line
charges (wasted slots, undoubled gaps, and unhit vacancies) are as
before. The final `p0` transition now counts precisely a complete
pitch row on a junction line. Write `T` for twice this count after
square-symmetry averaging. It counts all aligned complete pitch lines
in the two orientations.

For a physical board, deleting the nominal mandatory zero-hit debit
for an inactive line can overdraft by one **only** when it has no
vacancy: that is a complete pitch line. Thus the horizontal charges
are at most `X+T` with `X=3605+F-C-M`, even if `X` is negative:
use one of the `T` credits for each empty mandatory allowance on
either axis, and bound the horizontal charges by the resulting
nonnegative ledger. The transpose uses the same bound. This is
not a bound on the sum of both horizontal and vertical charges.
Drop the old no-pitch-only rows (on empty stubs, rank floor, complete
teeth and phase differences). Retain the full corner-partition
alphabet. The final certificates do not need no-cheap-cross
constraints. There is no fixed `F`, `C`, rank, cut depth or terminal partition.
At score 3647 the integer duals give, including residual allowances,

```
10^12 (-T) ≤ -6937498337446
10^12 A    ≤  5813335418676
```

Here `A` counts components of the *forced forest* containing junctions,
including isolated junctions; these are not the components after
arbitrary completion to a spanning tree. Thus `T≥7`, `A≤5`.

If perpendicular pitch lines both exist, they must both lie on the
junction indices: if exactly one is off-index the marks at the
intersection disagree. If both are off-index, their two nearest teeth
are diagonally adjacent, which forces a four-cycle. At an aligned
crossing the junction and its immediate neighbors form a separate
star component: neither pitch line has a mark one or two steps
away, and the diagonals of its marked center must be blank. If there
are `p,q≥1` pitch lines in the two directions, there are at least
`pq≥p+q-1≥6` distinct junction classes. This contradicts the price.

### Two caps, not two independent forests

On an aligned pitch line contract its 35 tooth groups. The two cap
partitions give a bipartite forest with 35 edges, one per actual
contact. With cap ranks `u,v` it has `35-u-v` components, all
containing junctions. Thus `1≤35-u-v≤A≤5`. This price holds on
**every** aligned cut of the same candidate. In particular the
outermost aligned cuts enclose a band of depth at least 18.
Their two **exterior** cap depths sum to at most 84 and are multiples
of three. These are two different cuts, so their exterior ranks
need not sum to 34 or less. Instead the [unwired band
price](UNBOUNDED_RAIL_SEAM.md), used at `lambda=0,1`, bounds the whole
score by

```
3605 + b_top + b_bottom - max(0, j_top + j_bottom - 34)
```

where `b` counts free marks in excess of 35 per free row. Neither
exterior has another aligned pitch row strictly between its rim and
its cut (nor on its rim unless the cut is the rim).

One sufficient remaining tariff on these exterior caps is `b≤8`
at `j=0`, and `10b-7j≤90` at `1≤j≤33`. The connected case `j=34`
already has `b≤33` by the finite-end price below. With two nonconnected
caps the band charge then gives at most `(180+7·34)/10=41.8`
bonus. With one connected cap, the other contributes `b-j≤8`
after rounding; with two connected caps the bonus is at most 32.
This would prove 3646. It has not been established at all the
exterior depths. For example `outer_pitch_cap.py 36`, a relaxation
allowing arbitrary partitions and forbidding further aligned pitch
rows, gave about 102.8 rather than 90 for `10b-7j`.

An independent replay embedded the 3646 comb in the full physical
chart before imposing the candidate-score equality. It had 32 aligned
pitch lines, ledger slack −16 and horizontal/vertical debits 9 and 7:
the original no-pitch budget would be wrong on precisely this control.
All physical rows passed. All 2,278 eligible four-square masks were
also checked for the pitch-credit inequality.

### Exact shallow cap, arbitrary partner

For one cut of depth `h`, `pitch_cap_partner.py` computes the exact
shallow cap bonus at each possible rank. Its vertex transfer introduces
the contact of a pitch group once and pays one terminal class only
when its last representative disappears. The opposite cap pays the
[all-height reflection price](WIRED_PITCH_SEPARATOR.md) and the
following finite-end price for depth at least two:

```
3b ≤ 2k + j - 3 .
```

Indeed the rectangular edge ledger reads `3b = r+t-R-c-holes`,
where `r=k+1`, `t` counts far-row marks, `R` counts marked runs,
`c` counts all components, and `holes` counts lateral vacancies.
`R≥r`, `c≥r-j`. Of the `n-t` far vacancies and lateral vacancies at
least two are required by the inward diagonal pair at the far
corners (one per corner). If `n-t≤2` the far row has a horizontal
run of length at least two at width 103, disjoint from the `r` runs
meeting the pitch row. Hence `(n-t)+(R-r)+holes≥3`.

Depth 0 or 1 cannot support 3647. At depths 2,3,4 only shallow ranks
30 through 34 survive this partner test, and all five have shallow
bonus `j-1`. Replace that cap by an outside full bar, a blank, then
ordinary rails to the cut. Its bonus is 33, so this gains `34-j`.
Wiring the teeth creates at most `34-j` cycles in the opposite cap.
Each can be broken by demoting one free mark there: a path between
two teeth must turn, and at the first horizontal edge or the preceding
vertical edge there is a sole free marked owner. Thus this replacement
does not lose score. It reduces this class to the genuinely wired
partner problem, rather than assuming wiring for a mixed split.
Physical controls with rank pairs `(30,4)` and `(32,2)` replayed
four and two demotions respectively.

At width 103 the entirely wired cap of depth 11 or 12 has exact
free maximum 393 or 428, i.e. bonus 8 in both cases. These depths
alone do not cover an arbitrary partner. The numerical two-cap
chart in `paired_pitch_chart.py` also matches both cap patch measures
to a common square, sewing both first-row bits and the two compulsory
spoke directions at each tooth (never two departures). The centered
cut at depth 51 gave approximately 3648.17, not an exclusion. Nor
does an LP value above 3647 give a physical counterexample. The
unrestricted question is still 3646 versus 3647.

There is also a joint upper for two shallow exterior caps, leaving
the middle band entirely free. At depth 11 the exact maxima of
`10*free_marks+7*classes` are 4187 with one class and 4184 with
two or more. They give `b≤33` and `10b-7j≤89`, respectively.
Padding on the terminal side with pitch rows preserves both bonus
and classes. Thus having a pitch cut within 11 of **each** end on
the same axis suffices for the 3646 upper at 103.

```
python3 -B -m analysis.research_program.pitch_contact_dual
python3 -B -m analysis.research_program.pitch_contact_audit
python3 -B -m analysis.research_program.pitch_cap_partner 0 1 2 3 4 5 6
python3 -B -m analysis.research_program.pitch_cap_partner --two-ends 11
python3 -B -m analysis.research_program.seam_rank_cost 103 12 --free-top --wired-bottom
(cd lean && lake env lean GridGraphs/Geometry/PitchSkeletonPrice.lean)
```
