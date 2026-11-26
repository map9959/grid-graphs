# P(371,371) = 46,231

At `k=123` the unrestricted upper is 46,232. Equality on the
exceptional progression requires either two perimeter gaps with no
isolate, or one gap with one isolate. Neither is possible at 371.

For two gaps, normalize to `0011` with an ordinary bridge. By the
[exit transfer](TWO_GAP_EXIT_TRANSFER.md), keep the perpendicular
deep axis and exactly the 53 exits `107,110,...,263` on the north.
Unlike the length-42 projection, the test uses the full square.
Every occurrence of a site in overlapping tracks reads the same
physical mark; the arrows and complementary face owners of a
shared edge are likewise shared along the whole overlap. There is
no prescribed filling for a corridor. The single disjunction was
UNSAT (2,190,757 variables, 25,987,022 clauses).

For one gap, test the canonical `0133` frame with all 121 north-star
distances `5,8,...,365` in both deep-axis cases, using the same
rooted tile tests as at 329. The area-mod-2 run covering 278–365
timed out. Its two halves gave checked exclusions with a 540-second
solver limit; the timeout contributes nothing to the result.

| Gap case | Coverage (step 3) | `drat-trim` resolution steps |
|---|---|---:|
| Two gaps | All 53 remaining exits | 446101 |
| One gap, axis 2 | 5–365 | 35621 |
| One gap, axis 1 | 5–185 | 213587 |
| One gap, axis 1, area mod 2 | 188–275 | 3793634 |
| Same | 278–320 | 13665119 |
| Same | 323–365 | 13159395 |

The ledger checks all six input hashes, replays the proofs, verifies
the physical catalogue types and exact coverage of each one-gap
axis, and replays the rail construction. Its result is
`(46231,137639,2,137640,46231)`: one additional edge joins the two
components to give a spanning tree with exactly 46,231 full-degree
vertices. Side 413 is the next unresolved exceptional side.

```
export PYTHONPATH=target/pb-python
python3 -B -m analysis.research_program.two_gap_board 371 300 0011 --axis --stream --ordinary-bridge --linked-exits
python3 -B -m analysis.research_program.tile_family_board 371 2 --sat --colors=2 --all-phases --dist=5:365
python3 -B -m analysis.research_program.tile_family_board 371 1 --sat --colors=2 --all-phases --dist=5:185
python3 -B -m analysis.research_program.tile_family_board 371 1 --sat --colors=2 --all-phases --dist=188:275 --area=2
python3 -B -m analysis.research_program.tile_family_board 371 1 --sat --colors=2 --all-phases --dist=278:320 --area=2 --seconds=540
python3 -B -m analysis.research_program.tile_family_board 371 1 --sat --colors=2 --all-phases --dist=323:365 --area=2 --seconds=540
python3 -B -m analysis.research_program.exceptional_287_ledger --371 --drat
```
