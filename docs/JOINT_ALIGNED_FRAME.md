# A joint price for the aligned three-column margins

For `n=3k+1≥103`, suppose a strict frame has three columns outside
each lateral side. Both side bars are solid, and its end rows, at
depths `a,b≤9` from opposite board edges, have the pitch word
in columns `3..n-4`. The forest scores at most

```
3k²+5k+floor((3k-13)/10).
```

In particular the aligned frame with ends at rows 3 and 93 on side
103 **cannot** score 3647. The conclusion does not require solid
intermediate pins, pitch words outside the frame, or a marked outer
rim. The comb attains the class upper. This replaces the separate
charges on the four exterior regions by one joint rank inequality.

### The interface graph

Let `p=k-1` be the number of frame teeth per end and `H=n-a-b`.
Let `C` count the core components containing at least one end tooth.
The [unwired seam theorem](UNBOUNDED_RAIL_SEAM.md) gives both
`I≤Hp` and `I+C-p≤Hp` for the marks `I` in the core. Indeed
`C-p=m-t` in its notation, and adding the two pitch rows adds exactly
`2p` marks. The same theorem allows free lateral edges; prescribing
the two bars here preserves the inequality.

Split the side wings at a horizontal bond. The northern piece contains
the whole free north cap *and* both northern wing segments; the southern
piece contains the complementary regions. Represent each end tooth and
its lateral leaves by a private terminal. The terminal for either extreme
tooth is also its side bar: every adjacent wing vertex has a compulsory
edge to it. This contraction keeps actual terminal connections through
the outer corners. Middle teeth at the two ends are not identified.
All components of the interior meeting an exterior edge meet a tooth
or a side bar, so the `C` classes describe its interface.

At each of the two outermost columns, branch on whether the bond
across the wing split is forced. If absent, its two endpoints must be
unmarked. If present, tag each endpoint as an additional terminal and
retain their edge in the gluing. Other crossing edges may be discarded.
For the present case the transfer may leave either endpoint mark free:
this enlarges the set of allowed pieces, and every actual forest in
that case still has the specified connecting edge. Write `u` for the
number of retained bonds, `q=p+u`, `c_N,c_S` for terminal-class counts
in the two pieces. Components with no tagged vertex are not counted.

On the `2q` labels the core and the retained bonds give `C+u` classes.
The ranks of the north, south and core partitions sum to at most
`2q-1` by acyclicity. One way to see this is to replace each connected
piece by a tree on its contacts. The incidence graph is a forest
because the original was a forest. Side-bar contacts can be moved to
their corresponding tooth by contracting each bar first, then splitting
its north and south copies by a single connecting edge. Consequently

```
C+u ≥ 2q+1-c_N-c_S,
I-Hp ≤ min(0,c_N+c_S-q-1).
```

### Pricing both pieces

For each piece maximize `10*marks+7*classes`, separately for one class
and for at least two classes. Keep the physical frontier partition and
pay the class bonus once, on closing its last live representative.
The order follows the left wing toward the free cap, crosses the full
cap by columns, then returns down the right wing. The component tags
and side terminals persist across both changes of direction. Core
marks are not included in either price.

If both ends have at least two classes, add the two weighted prices,
subtract `7(q+1)`, divide by ten and round down; then add `Hp`.
If just the north has one class, use price one for the interior rank:
`I-Hp≤c_S-q`. If the south price is `B`, then the south marks plus
`I-Hp` are at most `floor((B-7q)/10)`, since `c_S≤q`. The north
mark count is its one-class price less seven, divided by ten. Reverse
the roles for the other case. With two connected ends subtract `q-1`
from the sum of the separate mark maxima.

For `(n,a,b)=(103,3,9)` split after 45 wing rows in the north. The
prices (one class, many classes) and resulting integer bounds are:

| Forced outermost split bonds | North | South | Square upper |
|---|---|---|---:|
| neither | 2267, 2264 | 4387, 4384 | 3644 |
| one (either by reflection) | 2277, 2274 | 4397, 4394 | 3645 |
| both | 2287, 2284 | 4407, 4404 | 3646 |

### Why the width and heights can grow

It suffices to price free cap depth nine at each end. To project a
shallower feasible piece into this larger transfer, put one copy of
the pitch row in the new free layer and absorb one row of its wing
arms into that layer. Along each tooth this merely extends a connected
star by a forced central edge and lateral leaves. The old cap and
wing contacts still belong to exactly the same terminal classes; in
particular the outermost wing bonds at the distant split do not change.
The price increases by `10p` for the inserted core row, canceled by
decreasing the core-height allowance by one. Repeat up to depth nine.
This pads the *cap price*, not the marking inside the actual frame.

At depth nine use 30 wing rows in the first piece and `n-18-30` in
the other. In each wing sweep two successive interior frontiers have
identical full normalized vectors with shift 10. Inserting one wing
row therefore adds 20 to the price of a piece (one step on each
side). In the across-cap sweep, columns 90 and 120 agree up to
shift 1000 in the width-pumping bases. The retained terminal appears
at the same residue in both frontiers. All inserted transitions are
interior steps with exactly the same relative incidence lists and
fixed bits. The deterministic max-plus transfer therefore repeats
for arbitrary numbers of insertions. Equality is tested on all keys,
including the truncated count of already closed terminal classes.

`--family` checks sides 103 through 154 in steps of three, pumping
width from the ten bases 127 through 154. On increasing the side by
30, `q` and `p` rise by 10. The summed prices rise by 2600: two
width shifts of 1000 and two extra wing lengths of 30. The cap
contribution after rank subtraction rises by at most 253 marks
(250 in the two-connected-ends case). Adding the core growth
`(H+30)(p+10)-Hp` gives exactly the comb increment at padded depth
nine. Lean checks the rank and increment arithmetic; the frontier
certificates use the integer Rust transfer.

As independent checks, `joint_cap_crosscheck` compares every terminal
price to an uncontracted enumeration of actual grid markings on two
small caps, for each of the four split-bond choices. `joint_frame_steps`
compares the vertex bits, tags, incident live-index lists and frontier
forget operations under 152 width/length insertions.

### A necessary error in an incomplete frame

Let `D` consist only of the required teeth in the end rows and the
two side bars. For an arbitrary marking count the following set of
marked sites, without multiplicity:

* off-pitch sites in the two prescribed row segments;
* for each *missing* site of `D`, the two sites immediately to its
  left and right, the two sites two steps left and right, and its
  four diagonal neighbors.

If the count is `e`, the original score is at most `comb(n)+e`.
Indeed, delete those sites (none is protected) and insert the missing
sites of `D`. At each insertion the two horizontal neighbors were
isolated: their other neighbors are empty and cannot be protected
sites. The normal edges create at most one unit of cycle rank (if
neither already existed the center was isolated). No diagonal pair
is introduced. In any cycle an unprotected turn has a forced edge
owned only by that mark. If every turn is protected, a horizontal
segment between turns cannot run along either end row: distinct
teeth there have two intervening unmarked sites. Thus such a segment
joins the two bars at a non-end row. Its first interior site is
unmarked by diagonal exclusion against the full bar, so the edge to
the second interior site is singly owned by that unprotected site.
Deleting a sole owner on a cycle reduces rank by at least one.
Consequently the insertions pay for all cycle repairs, the resulting
score is at least the original minus `e`, and the complete-frame upper
applies. In particular arbitrarily many missing teeth and side-bar
sites by themselves do not permit a gain.

`python3 -B -m analysis.research_program.frame_guard_repair` physically
replays the operation on the comb and its transposition at 103.

The [two-axis defect budget](REPAIR_DEFECT_BUDGET.md) localizes the
failure of every repair, prices adjacent persistent defects and excludes
a sparse pair of corner assignments from the remaining budget.

```
rustc -O analysis/research_program/annular_frontier.rs -o target/annular_frontier
python3 -B -m analysis.research_program.joint_frame_caps 103 3 9 3 3 45
python3 -B -m analysis.research_program.joint_frame_caps --family
python3 -B -m analysis.research_program.joint_cap_crosscheck
python3 -B -m analysis.research_program.joint_frame_steps
(cd lean && lake env lean GridGraphs/Geometry/JointFrameCaps.lean)
```
