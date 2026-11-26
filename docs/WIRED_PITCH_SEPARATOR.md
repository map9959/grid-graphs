# A spanning pitch cut at arbitrary depth

Consider a forest on `n=3k+1` with a row marked exactly at
`0,3,...,n-1`. Suppose that in **one** of the two caps, including the
shared row, the `r=k+1` pitch groups lie in distinct components. The
depths of both caps, the marks between them and the outer boundary,
and the partition in the opposite cap are free. This includes the
case in which that opposite cap already connects every tooth.

Let `v` count the runs of vacant sites on the two extreme columns
of the separated cap, starting just after the pitch row. Then

```
M ≤ 3k²+5k + floor((3k-5v)/10).
```

In particular the gap to the comb bound on this whole family is at
most two marks, uniformly in side, and **`v≥3` suffices for the comb
upper**. The sides need not be bars. At 103 two runs give 3647;
three give 3646. The construction has the same first unrestricted
lower bound regardless of this test.

**Separated cap.** Let its height, excluding the fixed pitch row, be
`h`, its mark count `m`. Repeat copies tangentially, alternating
reflections and identifying each common end column. The pitch rows
match, since the end columns are pitch centers. In the calculation
contract the virtual pitch row to a common wire (wire its distinct
groups first). Every original tile is a forest after this operation.
At a join the two graphs share the wire and the common column with
its forced bonds, including the compulsory first spoke. If that
column has `g` missing vertical bonds the common graph has `g+1`
components. The cycle rank increases by at most `g`, by the
vertex/edge/component identity; this remains true when earlier joins
have created cycles.

Each such unit can be repaired by removing one **free** mark. Indeed
no marked diagonal pair was introduced: every grid face lies in
one of the two original tiles. On a simple grid cycle, at a turn the
turning vertex must be marked, and at least one of its two neighbors
on the cycle is blank. Its removal therefore destroys a cycle edge.
A cycle through the wire leaves and returns at different teeth:
its interior path must turn, and the same reasoning works there
(including a turn adjacent to a terminal). A straight interior
horizontal path between two contact sites with no internal turn
turns at its endpoints when the two spokes are included. If one such
endpoint is unmarked, its horizontal marked neighbor would be
diagonal to the virtual tooth, which is impossible. Thus a protected
tooth need never be removed. Use finite chains, then separate copies
of each repaired chain by two blank columns to apply the
[wired cap price](WIRED_ENDPOINT_PRICE.md); the chain width is `1 mod 3`.

Per tile in a long chain the width tends to `n-1`. If an end column
has `h_s` holes and `g_s` missing bonds, the mark debit when shared is
at most `h-h_s+g_s`. The two ends alternate equally. Since
`h_s-g_s` is its number of vacancy runs, the cap bound gives
`m ≤ h(k+1)+3k/10-v/2`. This comparison does not assume that the two
ends have the same marks or the same component partition.

**Other cap.** For `h'` free rows put `b'=m'-h'r`, and include the
pitch row in the rectangle. Its `r` marks start distinct vertical
runs (a singleton is allowed). The exact edge count gives
`3b' = k+1+t-R-c-holes`, where `t` is the far-end mark count,
`R` the total number of runs, `c` all components, and `holes` the
vacant lateral incidences. Thus `3b'≤3k`. Equality would require
both sides and the far end completely marked, forcing a diagonal
pair at the corner when `h'≥1`. Therefore `b'≤k-1`; height zero
satisfies this bound as well. Add the two caps and the pitch row.

**Without any wiring hypothesis.** A second all-height price for just
one prescribed pitch row is `M ≤ n r + floor(29r/22)`; alternatively
`M ≤ nr + floor(29k/22-v_all/2)` using both reflected ends, with
`v_all` counted over the entire height. Its linear term improves the
unrestricted sector coefficient on this class. To obtain the first
bound, repeat the whole square with the usual two blank guard columns,
continuing the marked pitch row across periods (its two missing sites
are both blank). For the second, overlap reflected lateral columns
and repair redundant joins as above. In this case the overlap is just
the column, not a common wire. A grid cycle cannot turn only on the
prescribed row because the horizontal bonds between neighboring pitch
groups are missing.

In the periodic strip pad both free ends by two blank rows and a full
row, which does not change bonus. Remove the two full rows and their
adjacent blanks; the remaining rectangle has blank end rows. Let `b`
be the total bonus over pitch density before padding. There is no
wire on the central pitch row. With the same column colors the exact
identity is `4b=6r-K`. Here `K` charges all central run endpoints
except the two per run meeting the pitch row, noncentral overlaps,
isolates (central ones twice), and two units per other nonisolated
tree. Indeed, if `J` counts the nonisolated trees, `U` the isolates
and `R` the runs other than full rows, the ordinary ledger after
padding and removing the two ends gives `3b=6r-R-J-U`. The colored
ledger gives `4R=3A+2J-U+3V+3U₀`, where `A` counts central endpoints
and `V` noncentral joins. This includes floating winding components;
a full row contributes neither endpoints nor a run start.

Eleven consecutive triples cost at least eight units, independently
of both heights. The sweep begins and ends blank; it may switch
stages on any complete pitch row. Before the switch charge ends of
vertical runs, after it charge starts. Thus a vertical run crossing
the cut, even a singleton, is exempt exactly once. Keep one physical
partition throughout both stages. A two- or three-triple subwindow
costs at least one or two; sums give the lower bounds on complementary
intervals used to filter the eleven-window. Averaging yields
`11K ≥ 8r`, hence `22b ≤ 29r`.

```
rustc -O analysis/research_program/pitch_endpoint_tariff.rs -o target/pitch_endpoint_tariff
python3 -B -m analysis.research_program.two_end_pitch_price
```

**Reflection with partial wiring on both sides.** For the same prescribed
pitch row let `j_+,j_-` be its independent tooth joins on each side,
and put `d=k-j_+-j_-`. Contract the pitch groups in each half: the
bipartite incidence graph of the two partitions, with one edge per
tooth, is a forest (a cycle would lift to a forced cycle). It has
`d+1` components, so `d` measures actual disconnectedness, not the
number of missing bonds. With `v_all` as above there is a second bound

```
M ≤ nr + floor((27k - 15d - 10v_all)/20).
```

To see this, reflect a single cap of height `h` (not counting the pitch
row) into a chain of `L` overlapping tiles. Let `G` be the sum of the
missing vertical bonds on the shared columns. The unwired chain has
cycle rank `c≤G`: a new tile meets the previous chain in a column
with `1+g` pieces, so adds at most `g` cycles. Now wire the teeth of
the chain. Equivalently wire each tile before gluing, identifying
the shared end tooth. The common subgraph is still the column with
`1+g` pieces (one contains the wire); each wired tile has cycle rank
`j`. Thus `c+J≤Lj+G`, where `J` is the unwired chain's tooth join
rank. These two budgets are needed simultaneously.

Delete at most `c` free marks to break all cycles, by the turn argument
above. The surviving rank is at most `J`. Pad the chain by two blank
columns, giving width `3(Lk+1)` with exactly its old pitch teeth;
the padding adds at most leaves to distinct copies. Apply the
[partial-rank price](WIRED_ENDPOINT_PRICE.md). Restoring the deleted
marks costs at most `c`, and
`c+3J/4 ≤ 3Lj/4+G`, not `3Lj/4+7G/4`.
Restoring the shared marked columns and dividing by `L` gives in the
limit `m ≤ h(k+1)+3k/10+3j/4-v_side/2`: on each shared end the number
of shared marks plus missing bonds is `h` minus its vacancy runs.
Sum over the two caps and add the prescribed row.

At side 103 any such cut in a 3647 candidate must satisfy
`15d+10v_all≤78` (in particular `d≤5`). This applies also when both
ranks are nonzero. Replay the seam budgets with
`python3 -B -m analysis.research_program.reflected_pitch_rank`.
