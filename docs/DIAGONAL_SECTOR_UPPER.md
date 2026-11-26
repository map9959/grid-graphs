# Residue one: an unrestricted upper with linear coefficient 16/3

**Uniform rounding improvement.** For `k >= 22`, `k = 1 mod 3`, the
integer upper is now `3k²+(16k-4)/3-1`, one below the former upper.
In particular `P(67)=1567`, `P(76)=2006`, `P(85)=2499`, and
`P(94)=3046`. The proof and replay commands are at the end of this file.
Combining this with the previous two rounding cases and the checked
side 58 gives the simpler unrestricted bound, for all `k>=18`,
`P(3k+1,3k+1) <= 3k²+5k+floor((k-5)/3)`.
The [unbounded-seam and two-profile theorem](UNBOUNDED_RAIL_SEAM.md)
also proves comb sharpness whenever the rail profile occurs within
six rows of each of two opposite sides, with the rest of the board free.

For every `k>=14`, setting `n=3k+1`, the diagonal-sector certificate gives

```
3k²+5k+floor((3k-13)/10) <= P(n,n) <= 3k²+5k+floor(k/3)-1.
```

The lower is the [explicit comb-cap tree](FOUR_ROW_COMB_CAP.md).
The real upper before rounding is `3k²+16k/3-1`. The difference of the
linear coefficients is now `1/30` in `k`, rather than `7/10`.
At side 109 this gives 4077–4079; the deeper chart below gives
**4077–4078**. It does not assume the tree
contains rails, has a cap, or respects a diagonal symmetry.

## The change in the dual

Use the oriented stars, legal `3x3` forest masks, edge consistency and
overlap marginals of the physical square. The variables are sums of
probabilities over location buckets, not probabilities tied across a
bucket. In addition to distance-from-end and period-three coordinates,
record two signed distances, clipped to a bounded interval. At location
`(i,j)` on an axis of length `S` they are `i-j` and `i+j+1-S`.
Thus charges can differ on opposite sides of either diagonal. The
two diagonal bands have length proportional to the side. Changing
their charges can improve the **linear** coefficient, whereas a fixed
number of extra corner constraints often changes only a constant.

For the two saved certificates, the coarse axis depth is two and the
coarse diagonal clip is `[-2,2]`; the fine axis depths are six (stars)
and five (patch origins), and both fine diagonal clips are `[-7,7]`.
The fine label determines every coarse label touching an occurrence:
the local changes in row, column and axis size cannot move a clipped
outer value back across the coarse threshold. D4 permutes/refects
the two signed distances and permutes the mask and star port labels.
Its action on the periodic axis labels is fixed throughout each
six-side progression. Therefore the pooled constraint matrix and
objective coefficients are independent of size once all fine types
occur. This is a statement about the certificate, not the forest.

## Exact counting, not fitting values

`chart_counts.py` counts a fine bucket at every `S+6t`. Fix the two
coordinate residues and write `i=3x+r, j=3y+c`. Axis ends restrict
the ranges. The two clipped diagonal tests give upper and lower bounds
on `y` with slope `-1,0,1` in `x` and affine intercept in `t`. For
each choice of active upper and lower line the verifier breaks ties by
index and derives an interval for `x`. Division by one or two in the
interval endpoints preserves integrality of the `t` coefficient.
The verifier checks that the chosen endpoint dominates every competing
line both at `t=0` and in slope. Summing `upper-lower+1` over the
interval is therefore a quadratic polynomial for **all** integer `t>=0`.
The counts for the fine types present sum symbolically to `(S+6t)²`;
there is no untested new type on larger boards.

Replay the rational column inequalities and the count polynomials:

```
python3 -B -m analysis.research_program.diagonal_chart 43 43 2 2 --replay
# 11797 columns, 2869 rows; Newton coefficients 1985/3, 572/3, 24
python3 -B -m analysis.research_program.diagonal_chart 46 46 2 2 --replay
# 11636 columns, 2817 rows; Newton coefficients 754, 608/3, 24
```

The Newton variable is `(n-43)/6` or `(n-46)/6`, respectively.
Both polynomials simplify to the same expression in `k`.

## Deeper sectors and finite equalities

With axis depth four and coarse diagonal clip `[-4,4]`, the real upper
improves by `1/6` on both parities. For **every `k>=18`** it is
`3k²+16k/3−7/6`. In particular its floor at side 109 is 4078.
Replay the two deeper certificates with

```
python3 -B -m analysis.research_program.diagonal_chart 55 55 4 4 --replay
python3 -B -m analysis.research_program.diagonal_chart 58 58 4 4 --replay
```

At 55 and 64, rounding already matches the comb. Independent
physical replay gives `(selected, forced edges, components, tree edges,
full-degree vertices)` equal to `(1066,3022,3,3024,1066)` and
`(1433,4094,2,4095,1433)`. Hence **`P(55)=1066` and `P(64)=1433`**.
There is also a separately priced four-row forest bound:

```
python3 -B -m analysis.research_program.diagonal_strip_replay 55 4 2 2 --source=109
python3 -B -m analysis.research_program.diagonal_strip_replay 64 4 2 2
```

**`P(58)=1182`** needs an integer exclusion. For a deterministic
forest orient toward the NW corner in its component. Under square
averaging, a local occurrence contributes its exact dual column slack
divided by its orbit size. Any further corner sinks pay the slack of
the corner-root inequality. At 1183 the available budget is 80 units
at scale 240. The physical CNF couples the actual marks, incident
arrows and patch masks, forbids inconsistent local patterns and bounds
the sum of charges. The two-sheet compass constraint is necessary
on every rooted tree: propagate sheet labels along its unique paths.
Thus a feasible forest at or above 1183 would satisfy the CNF.

```
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.diagonal_score 58 1183
target/cadical/build/cadical target/sector58_1183.cnf target/sector58_1183.drat
target/drat-trim/drat-trim target/sector58_1183.cnf target/sector58_1183.drat
python3 -B -m analysis.research_program.comb_cap_transfer 58 4
```

Checked CNF SHA-256 `8118b1e8e48cd213c4b4a88b30170d1dabb52cb5e583333087ba5a5f8c1b26fe`,
136423 variables and 1134071 clauses. Checker: `s VERIFIED`, 23805946
resolution steps. The comb replay gives `(1182,3361,3,3363,1182)`.

## Exact barrier for the oriented three-row repeating strip

Join the **depth-two** diagonal chart to an oriented forest on the
first three rows. A transition remembers two mark columns, the frontier
connectivity partition, and the arrows pointing left. It rejects forced
cycles and emits the complete first two star rows and the first patch
row. Their marginals must match the **same** sector-chart variables;
one does not add independent diagonal and boundary estimates. Any grid
forest gives feasible marginals by restriction and D4 averaging.

Keep fixed stages near both ends and pool the middle transitions by
column modulo three. Strip normalization counts increase by two per
middle transition type when the side increases by six. At the chosen
end depth the fine axis labels in the middle are periodic and the two
diagonal distances there are clipped. All repeated copies thus emit the
same labels. The replay checks closure of the middle-state transitions
and symbolic coverage of the square by the fine buckets.

For `n=55+6t` or `58+6t`, respectively, the exact dual Newton coefficients
in the basis `1,t,binom(t,2)` are

| Base | Constant | First difference | Second difference |
|---|---:|---:|---:|
| 55 | 6401/6 | 716/3 | 24 |
| 58 | 7099/6 | 752/3 | 24 |

**These are also the exact optima of this relaxation for every `t>=0`.**
For each base the saved three nonnegative rational flow vectors satisfy
the rows with right-hand sides given by the corresponding Newton
coefficients. Their scores are exactly the three displayed numbers.
Their sum with weights `1,t,binom(t,2)` is a feasible fractional point
at the full size, with equality in the dual bound. Thus changing prices
or optimizing at a larger training size cannot fix this relaxation.

```
export PYTHONPATH=target/lp-python OPENBLAS_NUM_THREADS=1
for n in 55 58; do
  python3 -B -m analysis.research_program.sector_oriented "$n" 3 2 2 --replay
  python3 -B -m analysis.research_program.sector_oriented "$n" 3 2 2 --check-moments
done
```

Replay builds the sparse integer matrix without optimizing and checks
every column inequality and every flow balance. The resulting upper
is `floor(3k²+16k/3−7/6)` for `k>=18`. Thus the strip recovers the
deeper chart bound, but its exact fractional optimum still has the
`k/30+O(1)` gap to the comb. At 109 it is `24473/6`, leaving integer
upper 4078; the fractional flow is not a tree attaining that score.

## Testing the saved flow against a fourth row

The particular three-row flow above **does not extend** with its chart
and transition masses fixed. For each positive transition enumerate the
fourth-row bits in the previous/current/next columns and the fourth
site's left-arrow bit. Orient the vertical edges of the enlarged column;
deleting the fourth row must recover the old directions (a down arrow
from row two becomes no outgoing arrow). Every completion emits a new
star in row two and, away from the ends, a new patch in row one.
Dropping connectivity and other compatibility checks only enlarges
this set of options.

If every option requires some star or patch whose old chart mass is
zero, the arc has no lift. More generally choose one such event per
option and let `J` be the set of distinct choices. Then
`mass(arc) <= sum(mass(j) for j in J)` is a valid inequality on
physical strip laws: each occurrence is counted by at least one term.
The labels are fixed within the arc's phase and the chart counts the
whole bucket. No equality of individual board probabilities is assumed.

```
export PYTHONPATH=target/lp-python OPENBLAS_NUM_THREADS=1
for n in 55 58; do
  python3 -B -m analysis.research_program.sector_oriented "$n" 3 2 2 --fixed-lift
  python3 -B -m analysis.research_program.sector_oriented "$n" 3 2 2 --lift-cuts --check-moments
done
```

For the 55-base family at `t=9` (side 109), 30 positive arcs fail;
arc 11901 has mass `3/8`. For the 58-base family arc 11725 likewise
has mass `3/8`. Across the three possible support regimes `t=0`,
`t=1`, and `t>=2`, the checker generates 34 and 22 support inequalities
respectively. Exact replacement flows satisfy **all** of these
inequalities with the same three objective moments as before. Thus
these explicit violated constraints strengthen the feasible set but
**cannot strengthen the score bound**, on either side progression.

The full four-row replacement search also finished. Replay with
`PYTHONPATH=target/lp-python python3 -B -m analysis.research_program.sector_oriented 55 4 2 2 --check-moments`
and substitute 58 for the other progression. The three rational
feasible moments have scores `(6401/6,716/3,24)` at base 55 and
`(7099/6,752/3,24)` at base 58, now satisfying the entire four-row
model (not just the projected cuts). Thus that relaxation cannot
reduce the side-109 upper to 4077. These are fractional witnesses.

## Full-board edge matching at 109

**A linear separation of the saved four-row optimum.** For
`n=3k+1 >=67`, consider the stored four-row moment mixture, with
positive coefficients for all three moments. In the `n=1 mod 6`
family take patch row 4; in the `n=4 mod 6` family take patch row 3.
At the three consecutive origins starting in column 18, there is
no `3 x 5` binary rectangle whose three `3 x 3` projections all lie
in the mixture's positive support. Enumeration only matches the
overlapping bits; even a cyclic filling cannot pass.

The same assertion holds at starts `18,21,...,3k-21`. All three
origins have the same fine axis labels as in the first triple,
and both diagonal coordinates there have reached their fixed clips
(`±7`), including in the reflected images. The fine labels near the
top edge retain its distance. These facts persist when adding six to
the side, and all three moment supports remain present. Thus **every
physical board has at least `k-12` off-support patch occurrences**
on this one row of origins: the triples of origins are disjoint.
This separates the particular saved fractional law, not every law
with its score, and so is not a numerical improvement to the upper.

```
python3 -B -m analysis.research_program.sector_track_support 67 --linear
python3 -B -m analysis.research_program.sector_track_support 70 --linear
```

Complete any forced forest to a tree, root at NW, and orient its
restriction to the forced edges for the sector charges. Every vertex
except NW owns its tree edge toward the root. The complementary edges
form a tree on the planar faces including the exterior, so each bounded
face owns its edge toward the exterior. Every grid edge thus has exactly
one owner. A forced arrow implies the corresponding primal owner, and
an edge owned by a face cannot touch a mark. This allows several
nontrivial forced components; it does not assume the isolated-site
extension rule from the different residue-two problem.

```
export PYTHONPATH=target/pb-python
python3 -B -m analysis.research_program.sector_matching 109 4078
python3 -B -m analysis.research_program.sector_matching 109 --check-tree
target/cadical/build/cadical -t 600 target/sector109_4078_matching.cnf target/sector109_4078_matching.drat
python3 -B -m analysis.research_program.diagonal_score 109 4078 --deep --matching --bins=24
target/cadical/build/cadical -t 1200 target/sector109_4078_deep_matching_bins24.cnf target/sector109_deep_match24.drat
```

The first command streams the existing exact score CNF, validates both
arc IDs on all 23,544 edges and adds 467,415 clauses. Result: 644,884
variables and 4,370,519 clauses, SHA-256
`d73ee0c77242267b34fe466bbf45fee2f011252f38bd160609108dd7ec6539fa`.
The explicit 4077 tree/cotree satisfies every added clause. CaDiCaL
returned `UNKNOWN` at 600 seconds. The deeper chart's unrounded PB
build was stopped for memory pressure. The 24-bin instance rounds
each admissible charge down, retaining individual over-budget bans;
it is a necessary-condition relaxation. Its 712,755 variables and
4,920,370 clauses returned `UNKNOWN` at 1200 seconds (SHA-256
`7e58aaf1a1ac2d03e48490642a854a0f235ab794fa8e20a4afa30c647ff8ddf8`).
Neither timeout gives a witness or an exclusion.

### Side 109: checked corner and boundary case split

Split on the six mark bits NW, NE, SE, SW, `(0,1)`, `(1,0)`, in that
order. DIMACS IDs are `1,109,11881,11773,2,110`. No rotational pruning
is used in the partition. All 64 assignments belong to exactly one
cube. Incremental conflict budgets 4000, 20000 and 100000 found 45
negative decisions; the other 19 returned UNKNOWN. Independently
exclude all 45 together by appending one blocking clause for each of
the other 19 assignments to the exact matching CNF. The checker tests
that this conjunction selects precisely the 45 claimed assignments.

```
python3 -B -m analysis.research_program.sector_corner_split check 3600 --certified --tag
# combined exclusion s VERIFIED: 45 cases; 19 outside this proof
```

Combined CNF SHA-256 `ff5f5de6cb6a68e82da2a119c5b43c3a34ae2ffbee670147da63dfb3a6586e27`;
4,370,538 clauses, 180,513,208 checked resolution steps. The remaining
words are stored in `certified_summary()`; none represents a verified
tree. To repeat discovery, use `search 4000`, then `search 20000
--resume` and `search 100000 --resume` with `PYTHONPATH=target/sat-python`.

**Physical consequence:** any 4078 tree has at least three full-degree
corners, and at every corner exactly one of its two perimeter neighbors
is full-degree. Indeed mark all full-degree sites and rotate any chosen
corner to NW, rerooting the tree for the matching encoding. Every
remaining word ends in 01 or 10. No word has fewer than two marked
corners. Two adjacent corners alone can be moved to NW and NE, but
no `1100**` word survives. Two opposite corners alone can be moved to
NW and SE; transpose if necessary to put the unique marked NW neighbor
on the east side. This gives `101010`, also excluded. This symmetry
argument applies to actual trees; it does not label any of the 19
remaining CNF cubes as independently proof-checked. The side-109
value remains 4077 or 4078.

### All four perimeter-neighbor pairs at 109

The 12-bit word lists NW, NE, SE, SW followed by four pairs: rotate
the NW pair `(0,1),(1,0)` clockwise to each corner in order. Enumerate
all 4096 words and apply the previous 45-case result at each D4
image, rerooting the physical tree at NW after transformation.
Exactly 80 signatures survive, in 12 orbits. This is exhaustive for
trees, without assuming the NW-rooted CNF itself is rotation invariant.

One first-neighbor mark per corner selects a direction. Further split
on the **second** perimeter mark in that direction, bit 0 at NW
through bit 3 at SW. Every mark set in an orbit of the 12-bit cover
has one of these 16 masks after mapping to the chosen representative.
The representative's stabilizer can duplicate masks; `tally` checks
coverage on the actual coordinates, not just on printed strings.

All 192 representative/mask queries were attempted. A checked DRAT
proof covers 161 in one disjunction; a second proof excludes mask 13
of `011101010101` by rotating it 180 degrees before the solve. This
leaves **22 of 167 physical D4 classes** (160 of the original 1280
oriented 16-site assignments). At least three corners of any 4078
tree must have *both* first and second perimeter sites marked along
their selected side. The remaining classes are not verified trees.

```
python3 -B -m analysis.research_program.sector_perimeter_split certified 3600
python3 -B -m analysis.research_program.sector_perimeter_split extra-proof 1200
python3 -B -m analysis.research_program.sector_perimeter_split tally
```

The selector CNFs append only clauses encoding the case disjunction
to the hash-checked exact matching instance. Their SHA-256 digests are
`2e0e5d5b6b2078e368647adf41eb37da10546d4eb66e86f8032990e7e2812aa0`
and `7a5431d8ee3eeb83121a0cde832cf61dcefd2b4167861afe5b8b59e3d5513171`;
`drat-trim` verified them using 2,089,922 and 977,768 resolution steps.

### Exact four-root budgets on the 22 surviving classes

Rotate the complete exact matching CNF by 0, 90, 180 and 270 degrees.
Its first 11881 bits are physical marks and are identified by rotated
coordinates. The last `4*108²` bits are face owners in top/right/bottom/
left order; rotate each face origin on the side-108 grid and add the
quarter-turn to its direction. Identify these variables across copies:
the complement of one spanning tree is one cotree rooted at the
exterior, regardless of the chosen primal root. Primal arrows, local
charge indicators, and PB auxiliaries remain private. In particular
each orientation gets its own **exact** scale-144, budget-144 inequality.
Every actual 4078 tree extends to an assignment of the joined model.

All 22 orbit representatives were queried. After a 6000-conflict pass
and a 35000-conflict pass on the remaining cases, `011101010101` with
continuation masks **7 and 11** was UNSAT. An independent proof for
their disjunction was verified (860992 resolution steps); the other
20 cases returned UNKNOWN. The joint base SHA-256 is
`ef70e47f0be33f4edaaa1b31adebd841f9c2ca8462c25b451c2a06d667354f2e`;
the proof-input SHA-256 is
`52aae83508d531c8c019384d4c3f0500d340a8654501a289c0917b54d05b15a2`.
These exclusions leave 144 oriented signatures. **If exactly three
corners are full-degree, all four second sites along the selected sides
must now be full-degree**: mask 15 is the only remaining such mask.

```
mkdir -p target/four_root_sector
rustc -O analysis/research_program/four_root_sector.rs -o target/four_root_sector/build
target/four_root_sector/build > target/four_root_sector/base.cnf
python3 -B -m analysis.research_program.four_root_sector prove 2400 --certified
```

For discovery use `PYTHONPATH=target/sat-python` and run `solve 6000`,
then `solve 35000 --resume`. No 4078 witness was obtained.

### Third perimeter site along the chosen direction

For every remaining parent, choose four new bits, in NW, NE, SE,
SW order: the site three grid edges from that corner on the side
selected by its first neighbor. They are defined even when the second
site is unmarked. No consecutiveness is imposed. The 20 parents give
320 representative/mask pairs; some masks are equivalent under a
parent's stabilizer. Transform all 20 **signed coordinate literals**
of each case under D4. The resulting 295 distinct orbits are disjoint
and contain exactly `144*16=2304` physical assignments.

On the same exact shared-mark four-root CNF, incremental conflict
budgets 1800 and 8000 found 211 negative classes. `drat-trim` checked
the disjunction of those classes. A separate proof excludes the last
two-mark third mask for the three-corner case (`011101010101_15_3`).
Together: **212 excluded classes, 83 unresolved**; only 624 physical
assignments remain. At least two of the third sites must be full-degree,
and at least three if exactly three corners are full-degree. When the
second-site mask has only three ones, the third-site mask must contain
all three of them. None of these necessary mark conditions is a tree.

```
python3 -B -m analysis.research_program.sector_third_split certified 3600
# s VERIFIED: 211 D4 classes; 1672 physical assignments
# s VERIFIED: 1 D4 classes; 8 physical assignments
```

The fixed case manifests reproduce the proof inputs from the four-root
base. Their SHA-256 hashes are
`f272dd77be6869b77e03a192ccded7a35a405b563c8e37f9175b110b0893146f`
and `a3c3f9a0658bfbe6bb307488cff0dccc2606dd1f51b7364ba57221627adf9723`.
The independent checker used 7,221,783 and 3,108,022 resolution steps.

### Fourth perimeter site along the chosen direction

Keep the side chosen by the first neighbor, regardless of the second
and third marks. For each of the 83 unresolved parents, assign the
four distance-four marks independently. Rotating and reflecting all
24 signed coordinate literals gives 1267 disjoint orbits covering
9984 physical assignments (`624 * 16`), from 1328 representative/mask
pairs. The four exact score budgets still use a common mark pattern.

Two combined DRAT proofs exclude **1163 classes**: 1160 in the
incremental search's disjunction and 3 by a separate targeted solve.
They leave 104 refined classes (792 physical assignments). Every parent
still has its all-ones fourth mask unresolved. In particular, a 4078
tree must mark all four distance-four sites if exactly three corners
are marked, or at least three if all four corners are marked. This
does not require that the intervening sites be marked. A disjunction
of the 21 other unresolved masks with a missing fourth mark timed out
at 1800 seconds; no exclusion is inferred from it.

```
python3 -B -m analysis.research_program.sector_fourth_split certified 3600
# s VERIFIED: 1160 D4 classes; 9168 physical assignments
# s VERIFIED: 3 D4 classes; 24 physical assignments
```

CNF SHA-256 respectively `03cffed2602979b592ecf99d7f63463afd6543eff6ea796eded3f87302ff49d1`
and `f566783bd3c5d5b1319673ad34bd9153bceeb957052155357d8ab536655f524d`.
Independent replay used 35,343,031 and 5,002,693 resolution steps.

### Fifth perimeter site along the chosen direction

Extend each of the 104 remaining parents by the four sites at distance
five on the sides selected at distance one. Assign those bits freely,
regardless of intermediate marks. Transform all 28 signed coordinate
literals under D4: the 1664 representative/mask pairs give 1603
disjoint orbits covering exactly `792 * 16 = 12672` physical assignments.

Two checked disjunctions exclude **1492 orbits**. The first, found by
incremental search with conflict budgets 700 and 7500, covers 1491;
the second excludes `011101010110_15_15_15_7`. That leaves **111
orbits, 848 physical assignments**, from 103 parents. In particular,
`111101010110_15_15_7` has no surviving child. All surviving cases
either mark all four fifth sites, or have four marked corners, all
second through fourth sites marked on each chosen side, and exactly
three fifth sites marked. These are necessary conditions on a 4078
tree. A separate search on the eight remaining non-all-ones fifth
masks returned UNKNOWN at 2400 seconds, not a proof.

```
python3 -B -m analysis.research_program.sector_fifth_split certified 3600
# s VERIFIED: 1491 D4 classes; 11816 physical assignments
# s VERIFIED: 1 D4 classes; 8 physical assignments
```

Combined CNF hashes (SHA-256):
`887df9d4d5b9dde3dff3083d309701161c281b8767bf735360b0b0d7102f2131`
and `ec40fb05e25cb42652a9b81dd80013284102de52e58d265bece4a5e3f419a514`.
`drat-trim` verified 26,187,067 and 676,224 resolution steps respectively.

### Sixth perimeter site along the chosen direction

Independently assign the distance-six mark on each of the four sides
selected at distance one. The 111 fifth-site parents yield 1776
representative/mask pairs. Transforming all 32 signed mark literals
gives 1715 disjoint square-symmetry orbits, covering all `848*16=13568`
physical assignments. All orbits were queried on the exact four-root
score-4078 CNF, with conflict budgets 800 and then 7000 on undecided cases.

`drat-trim` verified **1511 exclusions**. A disjunction covers 1474;
after a timeout on the remaining negative decisions combined, smaller
proofs (eight grouped and six individual) cover the other 37.
The resulting 204 unresolved classes cover 1568 physical assignments
from 108 parents. Three fifth-site parents now have no possible child:
`111101010101_15_15_7_15`, `111101010110_15_15_14_15`, and
`111101100110_7_15_15_15`. At least two sixth sites must be full-degree;
if exactly three corners are full-degree, at least three sixth sites
must be full-degree. These conditions do not assert consecutiveness
of the intermediate marks.

```
python3 -B -m analysis.research_program.sector_sixth_split certified 5400
# certificates 15 excluded orbits 1511 remaining 204 remaining physical 1568
```

`sector_sixth_proofs.json` records the fixed manifests and CNF hashes
(manifest SHA-256 `f3af63351d9c2ebe01a71a6bb8fe4d145225d00162e840af61e293db69577028`).
Use `audit` instead of `certified` to compare the existing checked
artifacts without solving again. No 4078 tree was found.

### Seventh perimeter site along the chosen direction

Each of the 204 surviving parents branches on four bits at distance
seven along the sides fixed at distance one. Rotating and reflecting
all 36 signed mark literals gives 3167 disjoint orbits among the 3264
representative/mask pairs, covering all `1568 * 16 = 25088` physical
assignments. Incremental passes used conflict budgets 500 and 3500.
One combined proof covers 2898 classes, nine proofs cover a further
35, and two targeted proofs exclude the last two-mark seventh mask and
five three-corner cases with a missing seventh mark. All twelve proofs
passed `drat-trim`.

The 2939 exclusions leave **228 orbits (1760 physical assignments)**.
At least three seventh sites must be full-degree, and all four must
be full-degree if exactly three corners are. All 204 parents still
have an unresolved all-ones seventh mask. No 4078 tree was found.

```
python3 -B -m analysis.research_program.sector_seventh_split certified 7200
# certified exclusions 2939 remaining 228 physical 1760 remaining parents 204
```

`sector_seventh_proofs.json` fixes the disjoint case groups and CNF
hashes (manifest SHA-256 `35bf908bc04f60ec61bf3b144b69a0cf8df24b02e78b8f05cdb34784dd8911a1`).
`audit` checks the existing artifacts and recounts the surviving orbits.

### Eighth perimeter site along the chosen direction

Split all 228 surviving seventh-site parents independently on their
four distance-eight marks. Under the eight rotations/reflections, the
40 signed physical literals give 3551 disjoint orbits covering all
`1760 * 16 = 28160` assignments (3648 representative/mask pairs).
The exact four-root model and physical mark IDs are unchanged.

`drat-trim` verified 3304 exclusions: one disjunction of 3266 cases,
eleven smaller proofs covering 36 more, and a separate proof of two
cross-distance cases. The audit leaves 247 orbits, 1912 physical
assignments, and 226 parents. Two parents lose all refinements:
`111101011010_15_15_15_15_15_7` and `111101100110_15_15_15_15_15_7`.
If any eighth site is not full-degree, the other three must be
full-degree **and** all distance-two through distance-six sites on
the four chosen sides must be full-degree. This does not require
all seventh sites to be marked. A targeted disjunction of four
consecutive seventh/eighth gap cases timed out at 1800 seconds.
No 4078 tree was found.

```
python3 -B -m analysis.research_program.sector_eighth_split certified 7200
# certified exclusions 3304 remaining 247 physical 1912 remaining parents 226
```

`sector_eighth_proofs.json` fixes the thirteen case groups and proof
input hashes (manifest SHA-256 `e059b0a3b6343adecf546430cb63106fe80e9560f9b8c3e607c87a60459c96d8`).
Use `audit` to check existing artifacts and recount the survivors.

### Common tree edge splits on the 247 eighth-site survivors

Select exactly the union of the 247 canonical assignments (one positive
selector suffices; distinct assignments disagree on physical marks).
Use the four-root CNF with common marks and common cotree. For each
undirected edge examined in one fixed direction, read the four primal
owner bits in cyclic root order. If it is not a tree edge, all are
false. Otherwise the set of true bits is exactly the corner set on the
head side of the cut obtained by deleting that edge. For an edge out
of the root in a particular orientation the omitted owner is false.
The owner numbering is checked against the positive outgoing-owner
clauses in the matching CNF before rotating.

Alternating masks `0101,1010` are impossible: two disjoint tree
components in the square cannot connect alternating boundary terminals.
Also the two remaining types of two-versus-two cuts (top vs bottom
and left vs right) cannot both occur anywhere in one tree. After
deleting one edge, any other edge lies in just one component, so a
second split cannot separate corners in *both* components of the first.
One Boolean shared by all edge cuts enforces this compatibility. No
two-versus-two split is required, and single-corner cuts are allowed.

The joint union timed out after 1800 seconds. At 6500 conflicts per
selector, 13 classes were found UNSAT and independently checked in a
single DRAT proof. Two additional checked proofs exclude three classes
with three marked corners and an incomplete eighth mask and one class
with both seventh and eighth masks incomplete. Thus **230 classes,
1776 physical signatures** remain. If an eighth site is missing, all
four corners and every site at distances one through seven on each
chosen side must be full-degree. A search over the remaining union
with marks of the verified score-4077 comb as nonbinding phase hints
returned UNKNOWN at 150000 conflicts.

```
python3 -B -m analysis.research_program.sector_survivor_tree build
python3 -B -m analysis.research_program.sector_survivor_tree certified 2400
```

Joined CNF SHA-256 `2b4af385c3c77fc1d909a70d29767984211b71c7289ad88baad062da26b8473b`.
The 17 class IDs and three checked proof-input hashes are in
`sector_survivor_proofs.json`. No 4078 spanning tree was obtained.

## Exact side 67 and a uniform component penalty

`P(67,67)=1567`. The four-row comb replay gives
`(1567,4487,2,4488,1567)`. The unrestricted sector bound is 1568;
the NW score model at 1568, including the primal/dual edge owners,
is UNSAT. `drat-trim` verified 3,888,174 resolution steps; input
SHA-256 `21f1a8a276ebd9769cf909c979bdfdb8ef35c8cbe224fda3f80e65abe761e979`.

```
python3 -B -m analysis.research_program.comb_cap_transfer 67 4
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.diagonal_score 67 1568 --deep --matching --bins=24
```

Let `F` consist of all edges incident to a marked vertex (an isolated
grid site is allowed). Write `B=3k²+16k/3-7/6` for the real upper.
Among the components **other than the one containing NW**, let `c`
be the number meeting a board corner, and let `m` be the number of
remaining components containing a mark. For every marking with
acyclic `F` and side `n=3k+1 >=55`, its score satisfies

```
score <= B - (5/6)c - delta*m,
delta = 1/3            for n=55 mod 6,
        1055/4953      for n=58 mod 6.
```

Indeed, orient the NW component toward NW. In every counted
component choose its sink to be the designated corner or a mark,
respectively. These choices are independent; they change neither
the marks nor the forced edges. Enumerate all legal neighbor masks
in the sink columns of the deep sector dual, including the extra
corner-sink debit. The least additional corner-sink charge is `5/6`
in both charts; the least marked-sink charge outside NW is `delta`.
All other charges are nonnegative. The symbolic fine-bucket counts
sum to the full board polynomial, so these minima apply throughout
each progression.

```
python3 -B -m analysis.research_program.sector_component_charge --deep
```

In particular when `k=1 mod 3`, attaining `floor(B)` leaves just
`1/6`, less than either marked-sink minimum. **All four corners
and every marked vertex must belong to one forced component.**
Every other component is an isolated unmarked site, since any
forced edge has a marked endpoint. For `k=2 mod 3` the budget is
`1/2`, so all four corners still have to be in the same component.
These restrictions apply before imposing a comb or a boundary frame.

For the `1/6` family, four disjoint `12 x 12` corner windows with
common marks across the four corner rootings separately exclude
(i) at most two marked corners and (ii) neither neighbor marked at a
specified corner. Both exclusions were DRAT-checked at 67 and 76.
The windows transfer at increments of 18: all axis residues, normal
depths, and clipped diagonal labels are unchanged in corner-relative
coordinates; the other diagonal stays saturated. The chart and budget
are unchanged. Thus at equality at least three corners are marked
and every corner has exactly one marked neighbor (two would force a
four-cycle). In the three-marked-corner case the exact conditional
dual gives `3k²+16k/3-4/3`, leaving **zero** charge at the target.

### The three-corner branch is impossible at every size in these progressions

For `n=67+18t` or `76+18t`, **every forest attaining the integer sector
upper must mark all four corners**. This is an all-size restriction on
the equality case; it does not exclude four marked corners.

Suppose there are three. Inside a `13 x 13` window enforce its complete
zero-charge stars, patches and local arrow consistency. The central
`3 x 3` patch on either diagonal staircase must be one of
`7,56,448,73,146,292`: a whole row or a whole column of three marks.
Here the staircase consists of patch origins with both end distances
at least seven in each coordinate and within one axis step of either
diagonal on the patch-origin board. The exhaustive local tests block
these six words and admit no completion, with all other marks free.

There are 56 DRAT-checked windows in each parity chart. In one
octant the origins are `(i,i+h)`, `h=0,1`. Keep the corner windows,
translate the central windows by `(9,9)` when the side grows by 18,
and fill the gap with the three periodic origins. Along this gap the
axis labels are periodic and the other diagonal is already clipped
throughout the halo. `sector_stripe_cover` checks the complete fine
label signatures, including the first step from each small base.
Reflection and transposition cover the other octants.

Two horizontally or vertically adjacent striped patches determine
the same axis **and the same absolute phase modulo three**: their
common `3 x 2` or `2 x 3` rectangle determines both, including when
it is empty. The two staircases are joined at the center. Their union
is side-connected, so the whole union has one phase. Transpose to
horizontal rows and write their residue as `p`; reflection exchanges
1 and 2. At `76+18t` an additional central proof leaves just masks
`292,448` (reference origin `(73,73)` at 148), hence `p=0`.

Now average only over square symmetries preserving the prescribed
horizontal phase. Forbid every other word in the diagonal staircase
buckets, impose the corner counts, and orient the unique nontrivial
forced component toward a uniformly chosen corner. This preserves
the corner-root inequalities even after restricting the symmetry
group. No noncorner sink can have a forced neighbor. Exact feasible
duals give these upper polynomials in Newton form (step **six**):

| base | phase | base upper | first difference | second difference |
|---:|---:|---:|---:|---:|
| 67 | 0 | 4703/3 | 860/3 | 24 |
| 67 | 1 or 2 | 102410899/66056 | 4702737/16514 | 24 |
| 76 | 0 | 6020/3 | 968/3 | 24 |

At phase zero the conditional upper is exactly **one third below**
the target at every step of 18. The phase-one polynomial starts
lower and grows more slowly, with the same second difference. This
exhausts the three-marked-corner hypothesis.

```
python3 -B -m analysis.research_program.sector_stripe_cover --drat
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.sector_diagonal_stripes 148 --deep --three-corners --central-phase
python3 -B -m analysis.research_program.diagonal_chart 55 67 4 4 --corners=3 --sinks=connected --phase=0 --replay
# also 55 67 with --phase=1 and 58 76 with --phase=0
```

Independently, the repeating north support cut above still permits the
exact four-row moment scores `9409/6,860/3,24` at base 67. A different
fractional flow pays for those off-support patches without reducing
the objective.

### The surviving branch has at most nine nonstripe patches on the X

In the four-corner branch, count **physical occurrences**, not
distinct masks, of nonstripe `3 x 3` words in the same two staircases.
Call that count `D`. Add the single inequality `D >= 10` to the
unrestricted four-corner, connected-sink chart. Its coefficient for
an orbit is obtained by summing the mask indicators over distinct fine
location buckets, with all the physical multiplicities represented by
the variables. Overlap at the central junction is counted just once.
Exact dual upper polynomials start at `84671/54` (side 67) and
`108377/54` (side 76), with the same first and second differences as
the target. Both are **1/54 below** it. Consequently `D <= 9` on the
entire board at every size of the two progressions.

Split off four disjoint square quadrants, omitting the central
row/column if necessary. In each retain the arm with patch origins
at depth at least seven and within one step of its diagonal. One of
the four has at most two nonstripe occurrences. **All its remaining
patches have the same absolute stripe phase.** To see this, consider a
five-by-five square of origins along the arm. Mark up to two arm origins
exceptional; on every side-connected component of the other origins,
overlap propagates one of six absolute phases. Enumerate the component
phases, rejecting inconsistent overlaps and diagonally adjacent
marked sites (they force a four-cycle). No assignment uses two phases.
Slide the five-by-five square along the arm: successive windows have
more than two common arm origins, hence share a pure patch. This
proves the assertion for unbounded arm length. In particular every
physical bit covered by at least three origins of this arm is fixed
by its stripe phase.

```
python3 -B -m analysis.research_program.diagonal_chart 55 67 4 4 --corners=4 --sinks=connected --band-debits=1,10 --replay
python3 -B -m analysis.research_program.diagonal_chart 58 76 4 4 --corners=4 --sinks=connected --band-debits=1,10 --replay
python3 -B -m analysis.research_program.sector_phase_gaps 5 2
```

### The cheap arm excludes the last branch

Rotate the arm with at most two exceptional patches to NW, and
transpose if necessary to make its common stripe horizontal. Both
normalizations preserve NW after the arm has been selected. There are
three possible absolute row residues `p`. Unlike a test of a donor
layout, the other three arms are free. Do not average over rotations
that would exchange the chosen quadrant or stripe direction.

In the unsymmetrized sector chart impose (1) no pure but wrong-phase
mask in the NW quadrant arm, and (2) at most two nonstripe occurrences
there. For five of the six certificates also prescribe each bit
covered by at least three arm origins: at least one of those covering
patches is pure. The test `covered` uses only guaranteed covering
origins of the fine type. In particular, a middle-axis label gives a
lower bound on the corresponding coordinate, and the clipped negative
far diagonal gives an upper bound on `i+j+1-S`. Thus possible
ambiguity at bucket ends weakens the test rather than ruling out
any physical placements. With `u=i-j`, `z=i+j+1-S`, the quadrant is
`z+abs(u)<0` on the principal staircase. These are location-type tests;
their rows and constant right sides persist when the side grows by six.

The exact upper certificates below list base value and first forward
difference in steps of six; the second difference is **24 in every
row**. Compare to the candidate polynomial `3k²+(16k-4)/3`. It has
base value 1568 or 2007 and first difference `860/3` or `968/3`,
respectively. Each row starts strictly lower and has no larger first
difference. On the relevant steps of 18 the candidate is the former
integer upper, so attaining it is impossible.

| Base | `p` | Base upper | First difference |
|---:|---:|---:|---:|
| 67 | 0 | 122297/78 | 860/3 |
| 67 | 1 | 3143611/2014 | 5432/19 |
| 67 | 2 | 12489/8 | 3431/12 |
| 76 | 0 | 3305054516/1646805 | 968/3 |
| 76 | 1 | 417700/209 | 6116/19 |
| 76 | 2 | 33979/17 | 3863/12 |

The four-row comb reaches the improved upper at the first four sides:

| Side | Marks | Forced edges | Components | Completed tree edges | Full-degree vertices |
|---:|---:|---:|---:|---:|---:|
| 67 | 1567 | 4487 | 2 | 4488 | 1567 |
| 76 | 2006 | 5772 | 4 | 5775 | 2006 |
| 85 | 2499 | 7222 | 3 | 7224 | 2499 |
| 94 | 3046 | 8834 | 2 | 8835 | 3046 |

```
python3 -B -m analysis.research_program.sector_one_sixth_ledger 67
python3 -B -m analysis.research_program.sector_one_sixth_ledger 76
```

This improves the unrestricted upper by one on an infinite family. It
does not close the linear gap to the comb: at side 103 the new interval
is still `3646..3647`.
