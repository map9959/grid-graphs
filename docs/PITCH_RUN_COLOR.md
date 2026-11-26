# Charging runs that end on a prescribed column phase

Use the full forced forest (an edge is present if either endpoint is
marked). A run is a maximal connected set of adjacent marks. It is a
straight interval, since two diagonally adjacent marks would force a
unit cycle. A singleton is a run. Write `R` for their number, `J` for
the number of components containing a mark, and `U` for isolated blank
vertices. All other vertices are in the `J` components.

Color columns periodically. For `χ=(2,-1,-1)`, with cyclic shifts
allowed, a vertical run at the favored phase contributes **4** in
its closed neighborhood on the infinite lattice. Every other run
contributes at least `-2`. Indeed the three sites across each vertical
slice sum to zero and the two caps contribute the center color twice.
For a horizontal run from `a` to `b` the sum is
`3 Σχ(j) + χ(a-1)+χ(b+1)`; checking its start and length mod three
gives only `-2,1,4`. For `χ=(1,1,-2)` the corresponding favorable
vertical contribution is `2`, and every run contributes at least `-4`.

Let `E` be the sum over the board of `χ` **plus** the colors of the
outside neighbors of each marked boundary site. Count both neighbors
at a corner. This puts back exactly the clipped portions of the run
neighborhoods. The sum of the multiplicity corrections at shared
inside vertices has `R-J` terms: each run neighborhood is a tree;
their edges are disjoint, and their union is a forest. Isolates
contribute their own color. Consequently if `Z` distinct vertical
runs are at favored phases (including singletons),

```
χ=(2,-1,-1):  4R + U  ≥ 6Z + 2J - E
χ=(1,1,-2):   5R + 2U ≥ 6Z +  J - E .
```

**Two opposite normal arms of the nine-layer transfer.** Let `s=n-18`,
and suppose the two lateral open sides of the retained core are bars.
Let `p` be the total number of high sites on its two end arms (not the
number marked on the core rim). Erase the four core corners, then
append one pitch row on each end, marked exactly at the high sites.
All these new teeth attach to the original forest only at their
corresponding high sites. Each set of high sites was wired by its
arm in the exterior, including the unmarked tips. Thus within one end
their components are distinct; there is at most one path from one end
set to the other, since two would close a cycle through the two arms.
In particular `J ≥ p-1`. The new teeth are on vertical runs, distinct
except possibly for that one through path.

The augmented board is `s × (s+2)`. Its boundary mark incidence
count is `2(s-2)+p`. Its total color plus outside incidence color is
`E=4χ(0)+ap`, where `a=2` for coincident end phases and `a=1` for
distinct phases. Here `s=1 mod 3`, and the two lateral outside colors
sum to `-χ(0)`. Choose the favorable phase(s) to be the actual end
phases. We have `Z ≥ p-1` in the first case and `Z ≥ p` in the second:
a single vertical run cannot use two phases. Hence `R+J+U` is at least

```
p-1 + ceil((6p-8-4χ(0))/4)   same phase
p-1 + ceil((6p-1-4χ(0))/5)   different phases.
```

The unweighted ledger is `3M=area+boundary-R-J-U`. Subtract the new
`p` marks and restore the erased corners. The four corner transfer
prices already charge twice the marked core corners in their
three-times-mark units, so at most four more units are needed.
With `A` the straight-arm count, `B` the joint corner price, and `L`
the preceding lower bound, the original score is at most
`A + floor((B+s²+4s-2p-L)/3)`. The inner square need not repeat.

Replay: `python3 -B -m analysis.research_program.critical_arm_square`.

**Combining the corner and run tests at 103.** A 22-square corner
cannot have both incident arms marked at depths `0,3,6,9` throughout
tangential positions `10..21`. This is a DRAT exclusion with all other
marks free. It rules out zero or one normal arm, or two adjacent normal
arms, when all four straight arms follow recurrent modes. For two
opposite normal arms at different absolute phases at least one has
offsets 0 and 1 at its two ends (the alignment with offsets 2 and 2
is the only exception). Each end faces a bar. Root at the offset-zero
corner. In 48 rounded sector units this corner costs at least 33 and
the other end costs at least 17: their disjoint charges exceed 48.
All three possible normal masks were checked with **only their set
bits** imposed. The second reference, 112, gives prices 36 and 13.
These local implications hold at the integer sector upper throughout
the respective step-18 progressions: the chart labels in corner
coordinates and the `7/6` charge budget are unchanged.

Thus only two coincident normal phases need the color bound at 103.
Three and four normal arms already satisfy the critical-arm square
price. A 3647 example must depart from the seven recurrent mask cycles
on at least one straight arm. No periodicity of an unrestricted
maximizer follows.

```
export PYTHONPATH=target/pb-python
python3 -B -m analysis.research_program.critical_corner_charge 103 0 48 --bars --deep --bins=48
python3 -B -m analysis.research_program.critical_corner_charge 103 0 0 --shifted --deep --bins=48
python3 -B -m analysis.research_program.critical_corner_charge 103 1 0 --shifted --deep --bins=48
# Repeat with 112.
```
