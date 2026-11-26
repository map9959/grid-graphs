# A perimeter restriction for residue-one equality

For `n=103+9s`, `k=(n-1)/3`, a tree reaching the current unrestricted
upper `T=3k²+(16k-7)/3` has **between one and seven missing perimeter
edges** in its forced forest. A missing edge has *both* endpoints
unmarked. This count is distinct from donor deletions in the side-103
collar. The perimeter cycle makes the lower bound one immediate.

Add `2g` as the lower bound on the star sum counting missing perimeter
edges at both ends. Each physical fine-location type contributes its
mass once; both incident tangential directions are counted at a corner
when applicable. With at least ten gaps the two exact sector-chart
duals give `T` on the progressions from 103 and 112 (step 18). Every
column charge must vanish at equality. A 15-square NW window is
already UNSAT with zero charges, for both charts.

For nine and eight gaps the exact real uppers at the reference sides
are respectively `T+2/15` and `T+4/15`. Their first differences at
step six are `1292/3` and `1400/3` at 103 and 112; the second
difference is 24 in each case. Hence on the required step of 18 the
charge budgets stay constant. In either branch a depth-five flat
side rectangle excludes any missing edge in its three central
positions. Its signed-diagonal labels are saturated and all
tangential residues repeat. Thus all the gaps lie on the first 22
edges from either end of the four sides. Corner-local labels stay
unchanged by adding 18. All three central phases and the complete
physical corner windows were checked with `drat-trim`.

For nine gaps the four disjoint corner crops sharing one budget
exclude the total directly. For eight gaps price the corners in
48 integer units, rounding charges down. Reroot at a largest corner.
Six gaps there cost at least 49. Two gaps at the root and two at any
other corner cost at least `25+24`. Otherwise the only partition of
eight still possible is `5+1+1+1`: it costs at least `34+3·5` at
103 and `37+3·4` at 112. All ten local price tests were DRAT-verified.
An UNSAT proof for the combined eight-gap shell is unnecessary.
At seven gaps the flat test has a SAT model: the same blanket
localization cannot simply be reused.

**Seven gaps, side 103.** The [canonical rim repair](RADIAL_COMPONENT_LEDGER.md)
eliminates straight singleton vacancies without loss or a change in the
gap count. In a canonical 3647 candidate with seven gaps, every gap is
among the first 38 bonds from one end of a side. This conclusion uses
a joint budget, not a one-window exclusion. In 32 rounded charge units,
one gap on the five central bonds of a flat 5-by-16 window costs at
least 27. Three gaps on the 21 central bonds of a 5-by-32 window cost
more than all 32 units. On a flat part (omit 24 bonds at each end),
any three either fit the latter window or two have disjoint
single-gap windows. Single-gap windows on different flat sides are
also disjoint. Thus at most two gaps are flat. Among the at least
five remaining ones some corner has at least two on its first 24
bonds per arm. This costs at least six units whether the corner is
the prescribed root or not. A gap at distance at least 38 from
both ends could pay its 27 units disjointly from this corner, which
is impossible. All four local exclusions passed `drat-trim`; the
translated flat windows have identical physical sector labels.
The second reference side 112 passes the same four tests. On both
step-18 progressions the seven-gap dual budget is `2/5` marks: the
Newton coefficients in steps of six are `18237/5,1292/3,24` at
103 and `21512/5,1400/3,24` at 112. Compare the target polynomial
on every third such step. Corner labels are unchanged by adding 18;
in the flat strip clip values are saturated and phases repeat modulo
three. Gaps more than 17 bonds apart have disjoint single-gap
windows; any shorter triple can be translated into a 21-bond window.
The finite coverage check handles truncation at either end; adding
18 inserts only regular interior phases.

**Excluding seven.** Choose a maximizer with maximal rim count. In
each `3×5` or `4×4` rim/corner patch enumerate the feasible masks.
Retain every vertex incident to an outside edge as a port. A mask
is dominated if an alternative with the same marked port bits,
refining port connectivity, and lexicographically larger (marks,
rim marks) exists. Such replacement works in its actual exterior.
The Boolean cube checker verifies that no surviving mask is
excluded. Also `##...` and its reverse are impossible on the open
rim: fill the first hole. If its right inward diagonal is marked,
delete it; the left inward diagonal is already blank and the
deeper normal donor is forbidden. Both newly contacted sites are
isolated. Otherwise the next rim site is isolated and the inward
foot has at most one deeper donor, which can be deleted if needed.
Neither surgery loses score and both gain a rim mark.

Use disjoint 44-site corner regions (arms depth six, central corner
depth twenty). In **64** rounded units, reroot at the corner with
most gaps. Its certified lower prices for 2 through 7 gaps are
`22,39,59,61,64,65`; for 1 through 3 at a nonroot corner they
are `2,22,30`. Every sorted partition of seven among four corners
pays at least 65. Both references use the same thresholds; the
individual exclusions are checked with `drat-trim`. Hence if the
current unrestricted upper is attained on `n=103+9t`, a canonical
maximizer has **one through six** missing perimeter edges.

```
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.canonical_gap_price --deep --rim-gaps=7 --bins=32 --localize
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.canonical_gap_price --deep --rim-gaps=7 --bins=64 --seven
# Repeat both with --side=112 for the other parity.
```

```
export PYTHONPATH=target/pb-python
python3 -B -m analysis.research_program.rim_gap_corners --deep --rim-gaps=10
python3 -B -m analysis.research_program.sector_gap_cover --deep --rim-gaps=9 --bins=32
# For eight use the two flat certificates from the same module (--bins=48),
# then the corner tariff instead of the combined-shell test.
python3 -B -m analysis.research_program.rim_corner_tariff 103 --deep --rim-gaps=8 --bins=48 --eight
python3 -B -m analysis.research_program.rim_corner_tariff 112 --deep --rim-gaps=8 --bins=48 --eight
```

**Separate zero-charge propagation.** With the original deep dual,
two depth-two teeth four positions apart on a flat clean side force
the two outward five-spacings in the subsequent rows. The local
birth test retains the six-row fan on a 33-position subinterval. A
second local rule in the flat sector transfers a right-moving
five-spacing by three positions from its last two rows. Both
reference parities and all three-by-three origin residues passed
(`sector_fan_rule --deep`, 24 checked exclusions, with satisfiable
input controls). These are implications on zero-charge windows,
not a restriction on unconditional bulk masks.

`sector_fan_collision --deep` replays 72 further DRAT exclusions. Two
inward-moving five-spacings with a single intervening phase cannot
collide inside a clean flat sector: at separation `g≥22`, `g≡1 mod 3`,
the two lips advance by three each and the common straight interval is
preserved. For the left lip the two input rows are prescribed only
on offsets `-6..11`, and the output is forced on `-3..8`; reflect for
the right lip. In the intervening interval a three-site buffer on both
sides suffices to preserve each straight-phase bit. Thus the next pair
at separation `g-6` is correctly planted on the overlapping rows.
The terminal spacings 16 and 19 are both impossible. This implication
requires all the local check windows to stay in the clean flat sector.
