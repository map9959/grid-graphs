# Side 103: a score-3647 search using the off-rail bound

For a score of 3647 the [depth-nine cut inequality](UNBOUNDED_RAIL_SEAM.md)
requires `min(q_N)+min(q_S)>=1`, and likewise east/west. Nonnegative
integrality means **one entire side in each pair** has a positive count
at *every* depth 0 through 9. The two such sides are adjacent. In an
unrestricted existence test rotate them to north and west, then root
the forest; the twenty clauses ask only for a marked off-rail site in
the specified three-line neighborhood. No other marks are fixed. The
deep matching/component model had 669140 variables and 4632447
clauses. CaDiCaL at 45 seconds returned `UNKNOWN`.

For a local-improvement test keep the *unrotated* physical 3646 comb
as reference. Use independent side flags for the two opposite pairs,
rather than assuming the comb admits the NW normalization. In the
outer collar (depth 0 through 11), count removed donor marks only;
every addition and the entire interior are free. The off-rail and
no-diagonal-pair clauses already require deleting **at least two of
the 1513 collar marks**. The relaxation passes with two deletions,
for example `(93,12),(95,12)` in zero-based coordinates; this is not
a score witness.

On the whole board allow at most two donor deletions and require
at least three new marks, with all locations variable. A prefix-count
chain certifies the additions; a primal/dual edge-owner matching
is necessary for extending the marked stars to a tree. This branch
is UNSAT. Together with the collar exclusions it rules out every
gain from the replayed comb using at most two deletions.

| proof input | CNF SHA-256 | `drat-trim` resolution steps |
|---|---|---:|
| `offrail103_collar_d0` | `5dddc6b81da30203d2d5a632f9d584801ef9668f88021f6a5437d654410955bf` | 653 |
| `offrail103_collar_d1` | `073e4530e4d7a225d8fa551a5a2d8b73ce1d17feda76d0c5209ff39c4b12bcc5` | 46725 |
| `offrail103_exchange2` | `3cf0f8e77f9bf34ad1e3717ffbd867478009c96b99f6af87d9f94bb52b874af7` | 98844 |
| `offrail103_exchange3` | `b6ef993520d9e267aeb51eb866737efe8b8f385a2be6619064215f59d02e6c54` | 16423747 |
| `offrail103_collar_d2_cover` | `befa6b565954213ee2995ce5602ab4083ae3d8553d29c5628182a9e42eb06cbd` | 30822 |
| `sector103_3647_deep_matching_component_offrail9_bins24_collar2` | `439141a807ddbefebd238c3b92040d4a279597265eaa327cfdfb53405481cf66` | 30072 |
| `sector103_3647_deep_matching_component_offrail9_bins24_collar3` | `85c4477355ab619ced9bab4cc3f29913f563a70e9fd6a2a709f1c8ada017ceb4` | 711842 |

**Stronger result:** the full score relaxation with the two side flags
excludes removing at most **three of the 1513 collar marks**, with no
bound on removals in the interior or additions anywhere. Thus every
score-3647 tree must omit at least four of these particular boundary
marks. The collar-three CNF had 673672 variables and 4643034 clauses.
The exchange-three test separately excludes a three-for-four edit via
edge owners and explicit cardinalities without using the sector budget.

For exactly two collar removals, the cheap local test has only seven
possible pairs: `(93,j),(95,j)` for `j=12,24,42,54,72,84,102`.
Blocking all seven and running `drat-trim` verifies their completeness.
There is a second check for these pairs. Retained rail marks force rows
2 and 92 to be exact profiles by diagonal exclusion from rows 3 and 91.
The top bar is intact. Straightening the intervening seam and paying
for lost lower connectivity as in the wired seam theorem leaves a free
ten-row cap. At width 103 its wired maximum is 358, so the upper is
`103 + 91*35 + 358 = 3646`.

```
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.offrail103_shell
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.offrail103_shell --exchange=2
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.diagonal_score 103 3647 --deep --matching --component --offrail9 --bins=24
# append --collar=3 for the checked collar branch (retain both side choices)
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.offrail103_shell --pair-cover
python3 -B -m analysis.research_program.seam_rank_cost 103 10 --free-top --wired-bottom
```

## Testing the complementary deletion branch

`--min-collar=4` demands four distinct missing donor marks among the
1513; it does not impose any ceiling. In anchored tests retain both
side choices on each axis. The entire `>=4` branch returned `UNKNOWN`
at 90 seconds. Adding `--collar=6` excluded the interval **4 through
6**. Input SHA-256 `5675f7903cfb5edca862abaddb1a8519f31f35fe97ac8cae01f1849acba75fcd`;
684230 variables, 4662632 clauses. `drat-trim`: `s VERIFIED`, 646021
resolution steps. Together with the previous `<=3` certificate this
requires **at least seven collar deletions** for any improvement.

```
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.diagonal_score 103 3647 --deep --matching --component --offrail9 --bins=24 --min-collar=4 --collar=6
p=target/sector103_3647_deep_matching_component_offrail9_bins24_collar6_mincollar4
target/drat-trim/drat-trim \"$p.cnf\" \"$p.drat\"
```

For side 103 the depth-ten cap also meets the two required price
limits: `10*marks+7*classes` has maxima 3837 (one class) and 3834
(at least two). Padding shallower caps as before extends the off-rail
clauses to depth ten at this side. A second uncapped run on `>=7`
added that cut and a binary adder requiring at least 3647 physical mark
bits (`--min-collar=7 --depth10 --count-marks`); it returned `UNKNOWN`
at 45 seconds. The bounds are still 3646 and 3647.

## Where can an off-rail neighborhood be empty?

**In a score-3647 candidate, at most one of the four sides can have
any empty neighborhood at depths 0 through 10.** On every side,
depths 0 and 1 must be nonempty. Here empty means that every mark in
the neighborhood is in a rail column relative to that side; it does
not require that the rail columns be marked.

First split the full `>=7` model by the least depth at which at least
one side is empty; include a twelfth case for no empty neighborhood.
Require all four bands at all lower depths nonempty. Four selectors
at the chosen depth implement “at least one is empty”; if several
sides are empty the depth case is still unique. The full input before
splitting has digest `2135390ba3f629102667d7e0c77d34c22aaca822f95280d2a71ca302d8c0d96c`.
At 15 seconds per case, depth 1 was checked UNSAT (depth 0 is a
subset of depth 1 on each side), and the other eleven returned UNKNOWN.

The following smaller necessary CNFs gave substantive exclusions.
Keep the charge budget for the whole board but price only complete
stars and patches in the chosen crop, with the deep certificate and
48 bins. A crop on the north side rules out an empty depth-0
neighborhood; by rotation this holds on each side. Next take the
union of north and west strips through coordinate 14. Select **any**
one depth in `2..10` on each side and forbid off-rail marks there.
The two depth choices are independent. The other marks are free and
there is no deletion ceiling or assumed donor orientation. This
single DRAT exclusion covers all 81 depth pairs, and square symmetry
covers every adjacent pair of sides. The two-profile inequality
already rules out empty neighborhoods on opposite sides. Together
these give the stated restriction. The unresolved cases are therefore
all four sides nonempty at every depth, or just one side having one or
more empty neighborhoods at depths 2 through 10.

| cropped proof input | variables / clauses | SHA-256 | checked resolution steps |
|---|---:|---|---:|
| `offrail103_crop_0_-1` | 56791 / 365830 | `990736386b3f624c6f329b81019bc5f119547c5acceab5d41888f2ac94020b56` | 42924 |
| `offrail103_crop_2to10_2to10` | 203617 / 1522385 | `21d86c804b2b3a222a41de32732a4e56f3e89feabad3092dd96b68e495fc6fba` | 165213 |

```
python3 -B -m analysis.research_program.offrail103_depth_split 15 0 1 2 3 4 5 6 7 8 9 10 11
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.offrail103_crop 0 -1 60 --deep --bins=48
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.offrail103_crop 2:10 2:10 60 --deep --bins=48
```

### Separate tests of the two survivors

`offrail103_survivors all 40` imposes all 44 positive neighborhoods.
`one 40` chooses north as the unique side with an empty neighborhood:
a disjunction over depths 2 through 10, with every tested depth on
the other three sides positive. Rotating a physical target before
rooting is legitimate since *every* physical target, rotated or not,
must delete at least seven marks of the reference collar. Neither
test caps deletions. Both used the explicit mark count and timed out
(`UNKNOWN`) at 40 solver seconds.

Both include the redundant edge-count bound: with `R` marked runs,
`E` missing boundary incidences, `I` isolated vertices and `M` marks,
there are `3M+R-412+E` forced edges (consecutive marks of one run
double-count their common edge). As a forest on 10609 sites with at
least one nontrivial component it has at most `10608-I` edges. Thus
`R+E+I<=79` at the target, and `E<=43` since each run has length
at most 103. These are upper bounds on *mandatory* contributions;
the CNF only needs implications to the counting bits.

Two cheaper projections give further necessary conditions. In the
all-positive case two adjacent depth-seven neighborhoods cannot each
have exactly one off-rail mark. A cropped proof excludes even counts
at most one on both (`720710` checked resolution steps). In the
one-side-empty case, if an empty depth is 2, 3, or 4, *each* adjacent
side must have at least two off-rail marks at *each* of depths 2, 3,
and 4 (`1497114` checked resolution steps for the joint disjunction).
Neither is a whole-case exclusion.

```
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.offrail103_survivors all 40
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.offrail103_survivors one 40
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.offrail103_crop 7 7 30 --deep --bins=48 --north-max=1 --west-max=1
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.offrail103_crop 2:4 2:4 30 --deep --bins=48 --west-max=1
```

### Unique empty side: partition by its first empty depth

Start with the unique-empty-side CNF (SHA-256
`ae60c4fafd6f1354ecca7b2e5d140bed96767fa67a1777bcbb9dda3608407ef4`).
For branch `d`, require every north band before `d` positive and every
off-rail bit of the north band at `d` false. Leave later north bands
free. Under the base conditions these nine branches are disjoint and
exhaust the case. For `d=2,3,4` impose the checked two-mark minimum
on both adjacent sides at depths 2 through 4. In every branch impose
the depth-seven adjacent-pair restriction (at least one side in each
adjacent pair has two or more marks there). The latter cut is valid
irrespective of whether some other neighborhood is empty: its crop proof
excluded counts *at most* one on both sides without an all-positive
assumption. No upper limit is placed on deletions.

Each of `d=2,3,4,5,6,7,8,9,10` returned `UNKNOWN` at 20 solver
seconds. No complete depth was excluded. Two additional crop proofs
using first-empty selectors show that in **every** branch both sides
adjacent to north have at least two off-rail marks at depth seven.
Check west, then reflect for east. Unlike the earlier adjacent-pair
cut at depth seven this applies even if the empty north neighborhood
is at a different depth.

| first empty north depth | extra hypothesis excluded | CNF SHA-256 | checked resolution steps |
|---|---|---|---:|
| 2–6 | west depth 7 has at most one off-rail mark | `d94023af419a8bd5edf36e266840b903f24f647aefcdedfdc75b6491daab6cf6` | 673750 |
| 7–10 | same | `e4449887245ca945574ab315580f1a4df54d29fe0161071de27966a86bef1aa7` | 329855 |

```
python3 -B -m analysis.research_program.offrail103_one_depth 20 2 3 4 5 6 7 8 9 10
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.offrail103_crop 2:6 7 35 --deep --bins=48 --west-max=1 --first
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.offrail103_crop 7:10 7 35 --deep --bins=48 --west-max=1 --first
```

The next full-board run explicitly required both west and east
depth-seven thresholds in all nine branches. With 25 solver seconds
per branch all returned `UNKNOWN`; their distinct input hashes and
results are in `target/offrail103_one_depth_adj7/d{2..10}.json`.

There is a further placement restriction: **on each adjacent side
the required marks occupy at least two distinct rows** (empty side
normalized to north). The west neighborhood is columns 6 through 8.
Assign one flag per off-rail row there, forced true by any mark in
the three columns; allow at most one such flag. DRAT verified the
exclusion both for first empty depth 2–6 (496564 resolution steps,
CNF `1530e314ef2d4f18e45478363bc8774201052af848a1a4464d9a5fd2bf1c29dd`)
and for 7–10 (268933 steps,
`75a24177c7a0153311e295c252385f99863430968fe0f047d2e6ec57ca201e81`).
Reflection gives the east restriction independently. The two sides
need not use the same rows. Replay the last two crop commands with
`--count-rows` added.

The full-board inputs now require distinct occupied rows independently
on west and east in every first-empty branch. For each side a witness
row flag implies a disjunction of that row's three mark bits; the
two-witness counter acts on those flags. For all nine suffixes,
pinning the three sites of just one row passed the old site threshold
but failed the row threshold, while two marks in different rows passed
the latter. At 30 solver seconds all nine full-board runs were
`UNKNOWN` (`target/offrail103_one_depth_adj7_rows/d{2..10}.json`).

**The rows cannot all lie in a single adjacent pair.** In the west
crop force a flag for each occupied off-rail row and forbid any two
flags whose physical row indices differ by more than one. Even with
arbitrary marks in that pair and outside the tested neighborhoods,
both north first-empty ranges are UNSAT:

| first empty depth | CNF SHA-256 | DRAT-checked resolution steps |
|---|---|---:|
| 2–6 | `1c8064bc5f4d25462cfb2e297403a519963b5ec6dc7d63f4bb1d94e115d65972` | 716650 |
| 7–10 | `838cb29cd06a9aab8f148d0b19a509a3b504c4656f9964a44f9bd8b816056da5` | 343900 |

Reflection gives the same restriction on east. This requires a pair
of off-rail row indices at distance at least two on each side, not
that all occupied rows be nonadjacent. Testing maximum distance four
instead returned `UNKNOWN` for both ranges.

```
python3 -B -m analysis.research_program.offrail103_one_depth 30 2 3 4 5 6 7 8 9 10
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.offrail103_crop 2:6 7 45 --deep --bins=48 --row-span=1 --first
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.offrail103_crop 7:10 7 45 --deep --bins=48 --row-span=1 --first
```

### Row separation in all nine branches; a local corner obstruction

Since the off-rail row indices are `1,2,4,5,...,100,101`, it suffices
to forbid having all the marks in any one doublet `{3t+1,3t+2}`.
For each doublet add the disjunction of all marks outside it in the
side's depth-7 neighborhood. Add these 34 clauses separately on west
and east. The nine full score-3647 branches, with the deletion lower
bound but no ceiling, each returned `UNKNOWN` in 30 solver seconds.
The saved input digests and outcomes are in
`target/offrail103_one_depth_adj7_separated/d{2..10}.json`.

The separated witnesses can in fact be required **near each corner
on the empty side**. Test a 30-by-30 NW window, keeping only sites in
its north 15 rows or west 12 columns. Suppose for some `d=2..10` the
north neighborhood has no off-rail marks even just in columns 0–29.
Across west columns 6–8 consider the off-rail marks **in rows 0–16
only**. For each such mark force its row flag and forbid any two flags
at distance greater than one. The resulting CNF is UNSAT. This proof
uses no first-empty conditions, no minimum number of comb deletions
and no mark assumptions elsewhere. Reflection gives the other corner.

| side | CNF SHA-256 | `drat-trim` resolution steps |
|---:|---|---:|
|103|`f56e1961d799cdbb36bb931f0f737721b9133d309bd8db4179f0a8d5ccd4632b`|1281765|
|112|`d0fe638006ba345b94a4131539b52cf377d52db0dc056b5378f399fe878c3edf`|1053943|

This local obstruction transfers to sides `103+9t`, at the target
`3k²+(16k-7)/3`. On each reference progression with increment 18
the deep dual stays the same and the charge budget is always `7/6`.
In corner-relative coordinates all near-axis labels in the window
are unchanged, the periodic labels keep their residues, and the far
diagonal is saturated throughout the window even for the smaller
reference side. The same holds in the eight symmetry images (the
signed diagonals are permuted up to sign). The root, grid directions
and complete local incidences do not change. For instance the 630-site
charge and orientation part has exactly 376433 clauses at both 103
and 121, identical after variable relabeling. This is a restriction on
equality in the upper bound, not an exclusion of equality itself.

```
python3 -B -m analysis.research_program.offrail103_one_depth 30 2 3 4 5 6 7 8 9 10
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.offrail103_crop 2:10 7 45 --deep --bins=48 --west-section=0:16 --row-span=1 --corner-size=30 --side=103
# repeat with --side=112 for the other chart
```

### Applying the corner cut and coupling the two ends at 103

All nine full-board suffixes now include the separated-pair clauses
restricted to rows `0..16`, independently on west and east. The six
eligible row groups in this section are `{1,2},{4,5},{7,8},{10,11},
{13,14},{16}`. For each group require a mark outside that group but
inside the section. Each strengthened branch returned `UNKNOWN` at 35
solver seconds. The nine input hashes and verdicts are in
`target/offrail103_one_depth_adj7_corner16/d{2..10}.json`.

**The two corners cannot both use just two groups.** Count occupied
groups separately at each end (a group occupied at both ends counts
twice). Make one charge model on the disjoint union of the two corner
windows, sharing the board's single charge budget and using the actual
NW root. A common depth selector imposes the empty north neighborhood
on both cropped ends. Keep the certified two-group minimum at each
end and test a combined upper limit of four. The three independently
checked UNSAT results require a total of at least five: one end uses
at least three groups. The marks in those three groups include a pair
at row distance at least five. This excludes placements within every
branch but does not exclude a whole branch.

| empty depth | CNF SHA-256 | `drat-trim` resolution steps |
|---|---|---:|
| 2–4 | `6f141d3e01d389958570aca929092033b5d533ec99a576c627c1809ee5127e25` | 2984622 |
| 5–6 | `0ae9f9b34f5f142ecc4af33547658c8822ec1d15f7eb34aca44e8b474492862e` | 4047324 |
| 7–10 | `5812e02755be4318ae81fd0722403e8faab214f3118e2e3f1a56f467e09d36dd` | 3852955 |

```
python3 -B -m analysis.research_program.offrail103_one_depth 35 2 3 4 5 6 7 8 9 10
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.offrail103_corner_pair 103 2 4 4 40 --deep --bins=48
# repeat with 103 5 6 4 60 and 103 7 10 4 40
```

### Five-group full-board split and group identities

In each depth suffix encode each of the twelve occupied-group flags
as equivalent to the OR of its physical marks. Require every eight of
the twelve flags to include a true flag (at least five occupied).
The disjoint branches are `west`: at least three west groups, and
`east`: at most two west groups and at least three east groups.
The previous west minimum makes “at most two” exactly two; a board
with both corners at three or above belongs to `west` alone. The
group-count clauses were checked on all 4096 flag patterns. All
18 runs at 20 solver seconds returned `UNKNOWN`; there is no new
unrestricted upper. Input digests are in
`target/offrail103_one_depth_adj7_corner16_groups5_{west,east}/d*.json`.

Group identities matter as well. Number the row groups 0 through 5
from the north. A corner with exactly two groups cannot have pair
`01` (rows 1,2,4,5 only). At empty depths 5–10 it also cannot have
pair `02` or `12`: at least one of its groups reaches row 10 or later.
These are cropped exclusions with the opposite corner free to use
any three or more groups. Reflection exchanges the corners.

| depths | prohibited pair(s) at the two-group corner | CNF SHA-256 | DRAT resolution steps |
|---|---|---|---:|
| 2–6 | 01 | `4d26d2f9298cb6f325a4adc58326870996360bd25a6befe443010625156f2746` | 1977264 |
| 7–10 | 01 | `ab6d8aec0f9d41d9c6c82468395e97d535ce9ebcaaf7a1cea18e2ff97a8df36d` | 12037 |
| 5–10 | 02,12 | `22ac282ec6c77e0db0fcc50fd1d82d4f6b30e9fc72672b1a4db421a930d8328d` | 3305966 |

```
python3 -B -m analysis.research_program.offrail103_one_depth 20 2 3 4 5 6 7 8 9 10 --part=west
# repeat with --part=east
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.offrail103_corner_pair 103 2 6 2 45 --deep --bins=48 --west-only --pairs=01
# repeat for depths 7 10; for depths 5 10 use --pairs=02,12
```

### Exact two-group sweep

Reflect before rooting so the corner with exactly two groups, if any,
is east. Fix all six east occupancy flags, leaving the marks free;
west has at least three groups. The separate `both3` case fixes no
pair. This gives 114 exact-pair cases and nine `both3` cases. Tested
all 123 on the uncapped board and the two-corner crop, then retested
the 25 crop survivors with a larger crop and both root orientations
(shared marks, independent auxiliary variables).

| model | cases tested | DRAT-excluded | union CNF SHA-256 | resolution steps |
|---|---:|---:|---|---:|
| board |123|83|`4c17a5c8b99f8f6d79bffcd81d0500d971c200b4293087a1b4c6a35a2b6ca72d`|1066842|
| two corners |123|98|`948c89d874893c77720011d9e01bb2164b317bb933f9e9fe8b22c485506ab4d0`|2097973|
| enlarged, rerooted corners |25|8|`4ba700887dc016164f898eaa2d546f8db39bebab0a555a9d956bca83f08a5b50`|3643406|

All 83 board exclusions occur among the 98 crop exclusions. Thus 106
distinct cases are excluded. In depth order 2 through 10 the remaining
exact pairs are `12`, none, `12`, none, `23`, `23`, `23`, `23 or 34`,
and `23`. All nine `both3` cases remain open. `crop SAT` is not a tree.

```
export PYTHONPATH=target/pb-python
python3 -B -m analysis.research_program.offrail103_pair_sweep board 600
python3 -B -m analysis.research_program.offrail103_pair_sweep crop 1200 --deep --bins=48
python3 -B -m analysis.research_program.offrail103_pair_sweep crop 5000 --refine --deep --bins=48
python3 -B -m analysis.research_program.offrail103_pair_audit board 600
python3 -B -m analysis.research_program.offrail103_pair_audit crop 1200 --deep --bins=48
python3 -B -m analysis.research_program.offrail103_pair_audit crop2 5000 --deep --bins=48
```

### Depths 3 and 5: exact east occupancy when both corners have ≥3 groups

Fix all six east flags and require at least three west flags. There are
42 exact east subsets per depth (20 triples, 15 quadruples, six
quintuples, one sextuple). A selector audit recovered exactly these 42
masks from the six signed flag clauses for each depth. Every physical
mark inside an occupied group is still free subject to that occupancy.

| first empty depth | excluded / 42 | remaining exact east sets (digits name groups) |
|---:|---:|---|
|3|22|012, 013, 014, 015, 123, 124, 125, 0123, 0124, 0125, 0134, 1234, 1235, 1245, 01234, 01235, 01245, 01345, 12345, 012345|
|5|24|012, 123, 124, 125, 234, 0123, 0124, 0125, 0134, 1234, 1235, 1245, 2345, 01234, 01235, 01245, 12345, 012345|

At depth 3 **each corner occupies group 1** (rows 4 or 5 in its
depth-seven neighborhood). At depth 5 **each corner either occupies
group 2 or has exactly the set 0134**. Apply the east result to the
reflected physical board rooted anew for the west result. These are
necessary conditions; the lists make no compatibility claim.

| joint proof | excluded (overlap allowed) | CNF SHA-256 | DRAT resolution steps |
|---|---:|---|---:|
| full board |28|`d5341e20fc5ae7b01ba773f870b659516436145ca1e8785d2e05a82223c8054e`|707110|
| two corners |45|`600905b5a1dd08cd55edbb162a01d07dc4aa43bf0173849cab22848874bceadc`|3009212|
| enlarged corners with rerooting |36|`9c2bb4b73ec174e98cafe14b3baf4313845da39b911e4b3270168e64082498f8`|1110272|

Add `--exact35` to both sweep and audit commands above, using budgets
800 (board), 2400 (crop), and 1500 (refined crop). This mode writes its
own records in `target/offrail103_exact35/` and checks all 84 masks in
each model. No full-board SAT and no whole-depth exclusion.

### Joint west–east signatures at first empty depths 3 and 5

Use `--joint35` with the sweep and audit modules. Read the surviving
one-corner lists above and enumerate combinations **with replacement**:
20 choices give 210 unordered pairs at depth 3 and 18 give 171 at
depth 5. The twelve signed group clauses per selector fix both corner
signatures, without fixing any individual marks. Direct clause inspection
confirmed all 381 assignments, including all 38 equal-signature pairs.
For the opposite ordering reflect the physical board and root anew.
Earlier north depths are required positive on the full board; the
corner crop tests a relaxation requiring emptiness only at the selected
depth in the two windows.

The two-window charge crop excluded 31 pairs at depth 3 and nine
at depth 5. Its union proof was replayed (`s VERIFIED`, 2421469
resolution steps; CNF SHA-256
`e415c70e69ae07e741ec5911a6095034f9b8c0f40ce0cb5dd6c367a8d0c28859`).
In particular at depth 5, the only surviving one-corner signature
without group 2 was `0134`, and the joint pair `0134-0134` is
excluded. Hence **at least one corner occupies group 2** (row 7 or
8 in the adjacent depth-seven neighborhood). At depth 3 the two
corners cannot both have signature `125`, or both `1245`.

The full-board sweep at 500 conflicts/assignment returned 356 unknown
and 25 provisional negatives; its joint proof run timed out. None is
counted on that basis. The nine provisional negatives beyond the crop
and the group-2 cut were independently checked by a second crop union
(`s VERIFIED`, 2638841 resolution steps, CNF
`2131f53f7c27cd0aadbec81e95e0eaa3c8ce903c485255cb2be49048a07cafc7`).

A separate proof removes the exact signatures and first-depth assumption:
if **any** north band at depth 2–10 is empty, both corners cannot omit
group 2. The crop permits any two or more occupied groups per end and
puts no effective cap on the total (12 of 12). This uses the established
local two-group minimum. For 103 the CNF is
`0cc3b2808f3cd58fb6c1e1ab9cae950e2bb4b13298db28955d0db4bd35ffd17e`
(2786595 DRAT resolution steps); for 112 it is
`468dfe765b82d2061a0f08965e1d4c4a0dd70e0bf889f5cc013a5fcdcd7e9a78`
(2242803 steps). Both verified. At 103 this excludes 15 additional
depth-3 pairs beyond the two checked unions. Final deduplicated counts:
**55/210 excluded at depth 3; 9/171 at depth 5**. Every one-corner
signature still has an unexcluded partner. No score-3647 tree was found.

```
export PYTHONPATH=target/pb-python
python3 -B -m analysis.research_program.offrail103_pair_sweep board 500 --joint35
python3 -B -m analysis.research_program.offrail103_pair_sweep crop 750 --deep --bins=48 --joint35
python3 -B -m analysis.research_program.offrail103_pair_audit crop 750 --deep --bins=48 --joint35
python3 -B -m analysis.research_program.offrail103_joint_followup --deep --bins=48
python3 -B -m analysis.research_program.offrail103_corner_pair 103 2 10 12 45 --both-omit=2 --deep --bins=48
# repeat with side 112
python3 -B -m analysis.research_program.offrail103_joint_summary --list-open
```

### Eight remaining two-group cases: complete opposite-corner split

Orient the two-group corner east before rooting. Fix all six east
and six west group flags, leaving the marks inside each group free.
Require west group 2 OR east group 2 explicitly. Seven east/depth
cases already occupy group 2 and allow all 42 west masks of size
at least three. At `9:34` the cut reduces 42 west masks to 26. All
320 selector encodings were checked for their twelve signed bits.

| proof | selectors tested | checked exclusions (not additive) | CNF SHA-256 | resolution steps |
|---|---:|---:|---|---:|
| board |320|135|`98f281c556a7a63bebec2c545ab5f05ff5fc3a974ee0d16b9e2b8bfaa349f469`|1896658|
| corner crop |320|224|`0823cad48fa1f269cc4169eb39588a35a85702e80792f2d3ddd9b7707ffeadbd`|6735812|
| larger rerooted corners |96|74|`540ed770bf243d6ffafad845bb29aff1a8146bc5b8f844580f2dec7e8fb1a6fd`|6753871|
| joined north strip |22|16|`b395d55bc09afea3927b6b1982c9b75b82291239210415c54f06c40e9a1dada6`|6670454|
| full collar |6|1|`42667d64486c8fce141172e4d3ad48db8ee0c1899524d864fd878aec25c4f909`|1602861|

The strip contains the full north 18 rows, allowing the earlier
positive-depth clauses as well as the complete empty band. Together
these four checked unions exclude 314/320 assignments. Only east
`23` remains, at depths 6 (west `123,0123,1234,01234`) and 8 (west
`123,0123`). Extending the strip to depth 14 on the other three sides
and requiring their positive bands excludes `6:01234-23` as well.
This leaves **five** assignments (315/320 excluded). Thus at all
other first empty depths both corners must
have at least three groups. This does not exclude those depths.

```
export PYTHONPATH=target/pb-python
python3 -B -m analysis.research_program.offrail103_pair_sweep board 500 --two8
python3 -B -m analysis.research_program.offrail103_pair_sweep crop 1600 --two8 --deep --bins=48
python3 -B -m analysis.research_program.offrail103_pair_sweep crop 5000 --two8 --refine --deep --bins=48
python3 -B -m analysis.research_program.offrail103_pair_sweep crop 10000 --two8 --refine --joined-strip --deep --bins=48
python3 -B -m analysis.research_program.offrail103_pair_sweep crop 12000 --two8 --refine --joined-strip --full-collar --deep --bins=48
python3 -B -m analysis.research_program.offrail103_two8_summary
# Audit with offrail103_pair_audit and tags board, crop, crop2, strip, collar
# respectively, otherwise using the same budget and options.
```

### The two-group corner is impossible at 103

Split the five remaining assignments by all nonempty subsets of six
east sites: physical rows 7,8, in columns 96,95,94 (bit order runs
across row 7 then row 8; coordinates zero-based). These are all
sites of the occupied group 2. Comparing all 315 selectors to their
parent literals and six signed mark literals checked the partition.
The uncapped full board and north strip together exclude 308/315;
of the seven left the full collar excludes five. This exhausts **all**
depth-8 two-group cases. Both remaining assignments have first empty
depth 6, east `23`, west `123` or `0123`, and mask `09`: exactly the
two marks `(7,96),(8,96)` in this six-site set.

For the last two, take a separate necessary charge model with its
root at the physical SW corner (reflect rows before generating),
including the north 21 rows and 15 lines on each other side. Impose
the physical earlier positive north bands, the empty depth-6 north
band, all 33 other-side positive bands and the exact east sites.
On west require groups 1,2,3, forbid 4,5, and **leave group 0 free**:
this is the union of the remaining cases, without fixing a donor or
reusing the NW orientation. This single crop is DRAT-verified UNSAT.
Thus every score-3647 board with an empty side would need **at least
three groups at each adjacent corner**, in rows 0–16 of the depth-7
neighborhood. The both-at-least-three and all-positive searches
remain open; there is no change to the unrestricted interval.

| model | tested | excluded (overlaps allowed) | CNF SHA-256 | DRAT resolution steps |
|---|---:|---:|---|---:|
| board |315|305|`ae3835567ba0c89c02c4836c4edf86ab65e838f069b7e9a0c9b18a2298774dc0`|191485|
| north strip |315|308|`fa79bbad3fe4be4e1418d62d211b5076c327fe596ae07e49de2355280101d149`|234926|
| collar |7|5|`7752f1e6b03ee833726e98def79a50441c323190a151f65216c6af2f7026efa4`|2247654|
| south-rooted collar |2|2|`6c5af757d1bef67ac09bccf33bb5b2f973d05d2760bc213c667a7f7398fe4a19`|674814|

```
export PYTHONPATH=target/pb-python
python3 -B -m analysis.research_program.offrail103_pair_sweep board 500 --two8 --sites
python3 -B -m analysis.research_program.offrail103_pair_sweep crop 1200 --two8 --sites --refine --joined-strip --deep --bins=48
python3 -B -m analysis.research_program.offrail103_pair_sweep crop 16000 --two8 --sites --refine --joined-strip --full-collar --deep --bins=48
# Replay with offrail103_pair_audit using tags board, strip, collar.
python3 -B -m analysis.research_program.offrail103_sites_south 100 --deep --bins=96
```

### South-rooted collar on joint depth-3 and depth-5 signatures

Start from the 155 and 162 surviving unordered pairs, respectively.
Use the 5718-site collar from the two-group south proof: 21 north
rows and 15 lines along the other sides. The physical SW corner is
the root; physical `(r,c)` is represented at `(102-r,c)`. Fix the
first empty north depth and keep all neighborhoods on the other sides
positive. The entire six-group section on both east and west is
inside the collar. Each selector fixes the twelve occupancy flags
exactly; the marks themselves can rearrange. Horizontal reflection
of a physical solution before rooting covers the opposite ordering.

```
export PYTHONPATH=target/pb-python
python3 -B -m analysis.research_program.offrail103_joint_south 3 1200 --deep --bins=96
python3 -B -m analysis.research_program.offrail103_joint_south 5 1200 --deep --bins=96
python3 -B -m analysis.research_program.offrail103_joint_south 3 100 --deep --bins=96 --one-corner=omit2
python3 -B -m analysis.research_program.offrail103_joint_south 5 90 --deep --bins=96 --one-corner=0134
python3 -B -m analysis.research_program.offrail103_joint_south_audit --replay
```

The individual assignment probes (1200 conflicts each) gave 66
certified exclusions at depth 3 and 13 at depth 5. All other probes
were unknown. Two further collar tests leave the opposite signature
free subject to its three-group minimum and the known shared group-2
requirement. At depth 3 the tested corner cannot omit group 2. At
depth 5 the tested corner cannot be `0134`, previously the only
surviving signature without group 2. Reflect the physical board
before rooting to apply each exclusion at either corner.

| depth | previously open pairs | excluded by exact signatures | further excluded by one-corner test | still open |
|---:|---:|---:|---:|---:|
|3|155|66|16|73|
|5|162|13|9|140|

Hence **both** adjacent depth-seven neighborhoods require marks in
rows 7–8 at these two first-empty depths. This is stronger than the
older condition requiring one corner to contain such a mark. The
small 30-site corner projections alone still admitted assignments
without that group at both tested depths (separate crop SAT runs,
not complete boards). The depth-5 test omitting group 1 returned
`UNKNOWN` at 100 solver seconds. No 3647 construction.

| south proof | CNF SHA-256 | `drat-trim` resolution steps |
|---|---|---:|
|3, exact union A|`2595d7ad7a9167df323f2013f09b70618491183823ee30a7407c20df822849b5`|2612549|
|3, exact union B|`7c6d96b415a68a5e0edaeebb22644ba1cc64341508974870f3a5a70ffc7baa24`|1962272|
|5, exact union|`0042caff8bc8b42552aae00d040354a588ddafc52fb6ed0ee86d7045165aa280`|1040307|
|3, omit group 2|`03e89aa990620b13f2465d2a3fa08936a25e1b8796b3bab1e2cd4da209bc16b1`|905731|
|5, signature 0134|`b541b48f74035ce192176f285405c0734e8ebd9c27922f681f00ef943b622a7b`|458887|

The audit reconstructed the physical bands, groups and labelled
selector disjunctions directly from the union CNFs and independently
replayed all five proofs. Use `--list-open` to print the remaining pairs.

### Exact row-7/8 east sites for the 73 depth-three pairs

Use the west/east ordering of the 73 surviving pairs in the audited
south-rooted CNF. Number the six east sites by rows 7 then 8; within
each row use columns 96,95,94. Bit 0 is `(7,96)`. Every pair occupies
group 2, hence there are exactly 63 possible nonempty masks, including
multi-site masks. First project over *all* 73 parents. A checked proof
excludes 48 masks simultaneously (CNF SHA-256
`9e86453470f57aed6e1f4850223750d4321267f7dd3009ebb55c35a5398a7897`,
1741271 resolution steps). Of those, 40 already force a cycle among the
six marked-site stars; the other eight are `07,08,0c,20,25,28,2c,38`.
This leaves 1095 exact parent/mask combinations to test individually.

Mask `07` admits a stronger, corner-local exclusion. A 30-by-30 NW
window with north band empty locally at *some* depth 2–10 cannot
have all three row-7 sites in columns 6–8 marked. Any additional
row-8 mark in those same columns would itself force a four-cycle,
so testing `07` covers the triple. This test uses no exact group
assignments, no earlier positive bands and no charge outside the crop.
The checked CNF hashes (and resolution steps) are
`a4c62bc5e72eff571b55c56157e8f544fb90a38fe7e8cca94a305fb942905a32`
(1998719, side 103) and
`9518d915426cfd50d5b8a67d2f8b22e8e5d134568fe8c9e3cfb2b928aaffa74a`
(2298096, side 112). The same corner-window transfer by increments
of 18 as above applies: sites, clauses, chart and budget are unchanged
in corner coordinates. Reflection gives the east statement.

```
export PYTHONPATH=target/pb-python
python3 -B -m analysis.research_program.offrail103_d3_sites mask 3500
python3 -B -m analysis.research_program.offrail103_d3_sites board 120
python3 -B -m analysis.research_program.offrail103_d3_sites south 350
python3 -B -m analysis.research_program.offrail103_d3_sites_audit --replay
python3 -B -m analysis.research_program.offrail103_crop 2:10 7 30 --deep --bins=96 --corner-size=30 --west-sites=07 --side=103
# Repeat the last command with --side=112.
```

For a cheaper independent projection, fix just the selected corner's
group signature and site mask in its 30-by-30 window, with no charges
from the other corners. Of the 225 combinations of 15 signatures and
15 masks, checked proofs exclude 138 at 103 (CNF
`1406f2663ac3e54f0586cc2e63261679274cd8eed9a157217725d44bf609d9c2`,
5999450 steps) and 136 at 112 (`61f9fbbcb0b2f0bb41ea79908dcc4d216ef0e5f6d9fd396431fbd0eba9f75ad4`,
6738150 steps); 129 of those exclusions are common. These local
exclusions transfer by the same increments of 18. They are statements
about the *given* signatures, not an assumption that the side-103
catalogue exhausts possibilities at larger sides.

In particular **exact signature `{1,2,5}` is impossible at either
corner of an empty side** (empty depth in 2–10). Separate proofs
remove the site mask and all hypotheses on the other corner:
`5d6b6030cc33ed57ae89aa0125bddbb6784fea18fee555f54d407a032978472e`
(103, 3062840 steps),
`6592b70f70561bf6be38fbb3078cd48a6a5f83a943674c4d909ede1af36cfa5d`
(112, 3527916 steps). This also removes 15 of the previous 140
depth-5 pairs at 103. Neither projection fixes the rest of the board.

```
python3 -B -m analysis.research_program.offrail103_crop 3 7 30 --deep --bins=96 --corner-size=30 --west-sites=01,02,03,04,05,06,09,0d,10,12,18,21,24,29,30
python3 -B -m analysis.research_program.offrail103_d3_local
python3 -B -m analysis.research_program.offrail103_d3_local --replay
python3 -B -m analysis.research_program.offrail103_crop 2:10 7 35 --deep --bins=96 --corner-size=30 --west-signature=125
# Repeat all four with --side=112.
```

Putting the same physical window at the *far* corner from the root
also excludes `38` with a local empty depth in 2–10. The necessary
model simply reflects its physical rows before evaluating charges.
Hashes: `275db4a98855cdae3334070ebab625a2191d42201ca7599dd35ee510b83ea454`
(103, 1766480 steps) and
`6f44dc7026820f97f767628bf75e98571c758d27a081ec37557ef6f8e692cd03`
(112, 2595444 steps). In particular **neither row of this 2-by-3
window can be full** under the empty-band hypothesis, throughout the
same two upper-target progressions. This uses the four-cycle observation
to reduce the full row-8 case to exactly `38`. At side 103 the
far-rooted version of the signature-by-mask table also excludes 140
of 225 local combinations (`8f095606564697f97b80cda7c9cb69718d8dfbe7515269f3415d9f0d66800dba`,
6566942 resolution steps). Reproduce with `--remote-root` on the crop
and local table commands, testing `--west-sites=38` in the 2–10 crop.

**A group signature can force exact sites, independently of the other
corner.** With north depth 3 empty locally, forbid just the asserted
mask (one clause), impose the signature, reroot outside the window
and leave all other sites free. Both charts give the following
implications, with independently checked UNSAT proofs:

| signature | required mask | steps at 103 | steps at 112 |
|---|---|---:|---:|
| `124` | `01` | 443124 | 296599 |
| `1245` | `01` | 388116 | 258006 |
| `1235` | `09` | 495456 | 577755 |

Here `01` is the row-7 mark at inward distance six alone and `09`
is the row-7 and row-8 marks at distance six with all four sites at
inward distances seven and eight unmarked. The same statements hold
at either adjacent end, not just the one chosen in the ordered sweep.
Reproduce with `offrail103_crop 3 7 40 --deep --bins=96 --corner-size=30
--remote-root --west-signature=124 --west-except=01` (substitute the
signature and mask in each row; add `--side=112` for the other chart).
As a transfer check for this far-rooted region, the 504-site charge
CNF is identical after physical-coordinate relabeling at 103 and
121 (484597 clauses, digest
`3f42720b0bb0ca6b581f61dee93cd68187903a64ef4a127d1c366bffffcc5446`),
and at 112 and 130 (498780 clauses, digest
`0539a6634c536b2e4a2b9d161a182f5c62585232f300ab2e90aad09385b1f501`).
Use `offrail103_pair_transfer --single=3 --remote-root --deep
--bins=96 --side=103` or `--side=112`.

The single-window exclusions and exact `125` prohibition leave
361 joint parent/mask assignments. A two-window NW-rooted
crop tested those, excluding 70 in another checked union
(`99dbfaa6c9c89c9508fec444590a199bd8b4369135c57f8b1792ed452b00dc60`,
1302247 steps). Run `offrail103_d3_sites north 1000` after the two
local tables, then `offrail103_d3_sites_audit north --replay`. This
stage alone leaves 291 assignments from 65 parents before taking
the full-board and south-collar results into account.

The completed board and south sweeps reduce the deduplicated ledger
to **277 open site assignments in 65 parents** (4322/4599 excluded).
`offrail103_d3_sites_audit` checked the input hashes, physical group
and site selectors and verified output tags; the 27 pending full-board
negatives were not counted on the basis of that run.
