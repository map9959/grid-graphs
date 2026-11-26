# A wired cap needs actual joins of marked runs

Use the [periodic wired-cap conventions](CYLINDER_CAP_HEIGHT.md):
width `3r`, a wired pitch row on top, `H` free rows, and gain `b`
over `Hr` marks. For **every period and height**, a cap using only
vertical runs and complete horizontal bars satisfies

```
7b ≤ 2r.
```

This is strictly below the four-row comb's rate `3r/10`. In fact
attaining the comb rate requires deleting at least `r/70` marks to
eliminate partial horizontal runs (keeping any original full rows).

Normalize to end at a full bar with an empty row just above it. If
there is no full bar, add two blank rows and one full row: no change
in gain. Otherwise truncate at the first full bar. The suffix cannot
increase gain: the cylinder forest ledger on the last bar and suffix
bounds three times its marks by its area plus the two end incidences,
at most twice its width in total. Subtract the shared full bar. Pad at
the pitch end as needed so the prefix above the final blank has at
least two rows. The normalization has no interior full row.

Write `h=H-2` for the prefix height, `t` for its last-row marks, and
`E` for its runs other than the runs of first-row and last-row marks.
Remove the root spokes and the final blank and bar. The `r` top
contact vertices now belong to distinct trees. The `t` bottom teeth
are likewise in distinct trees, disjoint from the top trees: two
attachments to the final essential bar, or an attachment from the
wired root to it, are forbidden. Let `s` be the number of other
**tree** components. A floating essential cycle need not be counted.
If `T` is the first-row mark count, the run count is `T+t+E`.
Counting edges in the prefix, including the two boundary degree
corrections, gives

```
3b = 2r - t - E - s .
```

**Run-join inequality (also valid with partial horizontal bars):**
`b≤E`. Divide the circumference into `r` triples, each centered on a
top tooth. In every triple some prefix row is empty. Before its first
empty row the only possible word is the single center, by diagonal
exclusion starting at the pitch row. Continuing it all the way would
tie a top tree to a bottom tooth.

In one triple, pair a `110` or `011` with the empty row just below;
pair `111` with the empty rows above and below. All these rows exist:
the first row has only pitch marks, and bottom teeth are at least three
apart. The paid empty rows are distinct. The only possible conflict
would put two adjacent-pair words two rows apart with at least one
word `111`; two common marked columns would force a cycle. These
payments cancel the excess over one mark per row from those words.
Every remaining `101` joins its two distinct runs across the center.
If the first empty row has been spent, it is the row *above* a `111`.
Through its center there is a join from the top run (possibly just
the virtual top tooth) to that horizontal run.

Take exactly these joins, contracting each marked run to a vertex
and retaining the virtual top vertex if there was no first-row mark
there. Join interiors are distinct unmarked sites. There are `r+t+E`
vertices; the `r+t` distinguished end vertices lie in separate tree
components, and other components have at most one cycle. Hence at
most `E` joins can be present. Each triple contributes its doubles
minus empties plus one to the gain (a `111` counts as two doubles).
The cancellations just proved pay the plus one with the first empty
row or its join. Thus `b≤E`. In a period of 30 the actual comb has
three joins and three other runs: this inequality is tight.

**The second price when all prefix runs are vertical.** Put `q=r-t`.
Exactly `3q` bottom sites lie outside the disjoint horizontal stars
of the bottom teeth. To avoid isolation, their immediate upper
neighbors must be marked. At most `q` can be covered by a top run:
each bottom tooth covers the center of its own triple and the `t`
such triples are distinct. No bottom run can cover these sites from
above. Each other vertical run covers at most one. Thus
`2q≤E+s`. Together `b≤E`, `3b=r+q-E-s` imply `7b≤2r`.
Deleting a mark reduces gain by at most one and preserves the forest,
giving the deletion consequence.

```
python3 -B -m analysis.research_program.vertical_cap_tariff
cd lean
lake env lean GridGraphs/Geometry/VerticalCapTariff.lean
```

The Python check counts the actual joins, runs, and components of a
comb period and its thinned version. Lean checks the counting
implications, not the geometric reduction. The all-run inequality
alone does not exclude an improved cap with partial horizontal bars.
