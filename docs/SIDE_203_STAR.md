# Side 203: exact optimum 13927

**`P(203,203)=13927`.** The four northwest-square certificates and the
five three-quadrant certificates below exclude all 130 candidate charged
sites in each of the eight normalized one-gap frames. Together with the
previous two-gap exclusion, this rules out 13928 without restricting
the construction family.

For `203=3*67+2`, the unrestricted rational bound is `13928+1/14`.
The `U−1` rail selects **13927** marks. Their 41,207 forced grid edges
form two components on 41,209 vertices. Add the edge
`(0,200)--(0,201)` in zero-based coordinates: the result is a spanning
tree with 41,208 edges and exactly 13,927 full-degree vertices.

## What has to be excluded

The [single-defect and frame theorems](ODD_SINGLE_DEFECT.md) are
necessary for an arbitrary upper witness, not just for a repaired rail.
At 203 the two-gap case is already excluded (five frame classes
uniformly, the other ten by the checked unrestricted-depth full-board
connector proof). In the one-gap case the sole positive charge is a
depth-two star, the only isolate. Normalize the open corner to NW and
the gap to its north side. There are **eight** frame words; in each
the only candidate sites are `(2,d)` and `(d,2)` for `d=5,8,...,197`.

## How the site proofs cover the frames

* For `d=2 mod 6`, work inside a NW square. The eight frames and their
  NW-rooted perimeter arrows restrict identically there. Require the
  selected depth-two star to be charged and all other visible charges
  to be zero. Four checked disjunctions cover all 32 distances on both
  arms, including the far end: `8..98`, `104..146`, `152..170`,
  `176..194`, step six throughout.
* For `d=5 mod 6`, fill the north and east halves, both midlines and
  the full eight-layer rim. This leaves the southwest interior open.
  For a west-arm star **transpose the entire board** before this test.
  Thus the star is always in the north half, but the code permits both
  the eight north-gap words and their eight west-gap transposes.
  Rooting at SE makes 805 of the 808 perimeter arrows identical across
  all 16 words; guard the other three by their actual frame selectors.
  Use one common orientation/forest on the entire region, including
  across the quadrant interfaces. Only wholly visible charges are
  constrained. The sole charged site is always visible. Consequently
  UNSAT on the region excludes the original full-board case.

All claimed CNF exclusions are replayed with `drat-trim`. The compact
ledger checks the CNF hashes, exact disjunctions and frame coverage,
counts the remaining sites without duplication, and reconstructs the
lower-bound spanning tree:

```
python3 -B -m analysis.research_program.depth_two_203_ledger
# add --drat for full proof replay
# remaining per frame: 0 by distance phase {2: 0, 5: 0}
# physical lower-bound spanning tree: (13927, 41207, 2, 41208, 13927)
# two-gap certificate matches; upper equality case exhausted: P(203,203)=13927
```

| Phase-five distances (step six) | Sites per original frame | Checked resolution steps |
|---|---:|---:|
| 5 | 2 | 6,401,470 |
| 11 through 53 | 16 | 7,950,432 |
| 59 through 101 | 16 | 10,432,780 |
| 107 through 149 | 16 | 7,020,411 |
| 155 through 197 | 16 | 7,702,954 |

Thus `64+66=130` sites per frame are excluded, with neither a gap nor an
overlap in the disjunctions. The whole-progression claim does not follow:
larger boards introduce new distances and the filled quadrant interfaces
grow. The [subsequent side-245 proof](TILE_CASES_245.md) leaves **287**
as the first unresolved side on `35+42t`.
The [245-to-203 shortening test](SHORTEN_245.md) finds an explicit
wide-band obstruction and narrows the remaining one-gap star sites.

Generation commands for the first four certificates are in the
[site ledger notes](ODD_SINGLE_DEFECT.md#checked-side-203-location-update).
For a phase-five interval `[lo,hi]`, generate a fresh regional proof by
running `PYTHONPATH=target/pb-python python3 -B -m
analysis.research_program.depth_two_far_quarter 203 lo hi seconds`.
See also the [orientation-free score identity](ONE_GAP_MARKS.md);
no sufficiency of a local mark pattern is assumed in the exclusion.
