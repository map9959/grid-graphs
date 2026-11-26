# The enlarged shared-edge core and P(413,413) = 57,247

The side-371 clauses do not give an immediate literal proof at 413.
**Completing their overlap constraints on the enlarged physical grid
does suffice.** At 413 the old upper is 57,248 (`k=137`). Frame
`0011` has 67 possible exits, columns 107 through 305 in steps of 3,
on the perpendicular deep axis. The tests below include all of them.

## What was transferred

On the side-371 full-board input, `drat-trim -c` verified the proof
and extracted 104,388 of 25,987,022 clauses (446,101 resolution steps;
core SHA-256 `07431f1ca5edc6ff9a93bcf47deedcf79f676506a1f2253cd119bd190fee7f8a`).
Reconstructing the physical IDs found 17,340 mark variables (maximum
depth 65), 44,401 arrows, 9,901 face-owner variables (all in rows
0–60), four gap-tooth label bits and 125 global variables. The
shallowest three-row cross section was at row 67 (occupied lanes
reach depth 5), and the shallowest three-column section at column
355 (depth 10).

Insert 42 rows at the row-67 section and translate surviving local
clauses in the column direction by multiples of three from 0 to 42.
This takes a **union of clauses**, on distinct physical target
variables; it never requires a mark, arrow or owner to equal its copy
42 sites away. Keep only exact clause matches in the full side-413
input (SHA-256 `75fc28810ae7ea53acb69653d35f00659b8c1fbed9f4c4ffa03ec448531aa4da`).
That last check matters, for instance where the longer board allows
a charged exit not available on the shorter one.

Let the support consist of the physical coordinates named by those
matched clauses. Keep the target's global flags, counter variables
and eligible exit bits. Within the support, vary which further physical
variable IDs are retained, and take every original target clause
whose literals all remain. The following counts include no new clauses:

| Side-413 projection | Clauses | Result |
|---|---:|---|
| Literal translated clauses only | 276,523 | SAT |
| All target clauses on retained IDs and flags | 1,596,440 | SAT |
| Add missing face-owner IDs at support sites | 1,816,683 | SAT |
| Instead add missing mark and primal-arrow IDs at support sites | 1,912,722 | **UNSAT**, 1,701,142 DRAT resolution steps |
| Add all physical IDs at support sites | 3,990,200 | **UNSAT**, 6,887,312 DRAT resolution steps |

The smaller exclusion still uses the face-owner information already
in the translated core. The comparison does not establish that faces
are dispensable. The audit replays all clauses of the three partial
SAT models and checks both UNSAT inputs as byte-for-byte ordered
subsets of the original target CNF. The smaller UNSAT input digest is
`4a7abca35d2c7b481c432b4f535264ddb95c51aeb4388862faa8091d3d86743b`.
These are finite exclusions, not an induction that such support works
on every subsequent board.

## Matching the unrestricted bounds

The ledger uses the 3,990,200-clause two-gap exclusion. For one gap,
normalize to `0133` and test **all 135** isolate distances
`5,8,...,407`. Both deep axes are covered:

| Case | Range, step 3 | DRAT resolution steps |
|---|---|---:|
| two gaps, enlarged overlap support | all 67 exits | 6,887,312 |
| one gap, axis 2 | 5–407 | 44,482 |
| one gap, axis 1 | 5–206 | 278,552 |
| one gap, axis 1, area mod 2 | 209–302 | 377,763 |
| same | 305–353 | 7,928,346 |
| same | 356–407 | 16,071,966 |

The independent rail replay is `(57247,170567,2,170568,57247)`: one
added edge yields a spanning tree with 57,247 full-degree vertices.
The first open side on this progression is now 455.

```
export PYTHONPATH=target/pb-python
target/drat-trim/drat-trim target/two_gap_371_0011_axis_ordinary_linked.cnf target/two_gap_371_0011_axis_ordinary_linked.drat -c target/two_gap_371_0011_axis_ordinary_linked.core
python3 -B -m analysis.research_program.two_gap_core_lift setup
python3 -B -m analysis.research_program.two_gap_core_lift map
python3 -B -m analysis.research_program.two_gap_core_lift candidates
rustc -O analysis/research_program/core_intersect.rs -o target/core_intersect
target/core_intersect target/core371_lift/candidates.txt target/two_gap_413_0011_axis_ordinary_linked.cnf target/core371_lift/shared_413.cnf
target/cadical/build/cadical target/core371_lift/shared_413.cnf >target/core371_lift/shared_413.log
python3 -B -m analysis.research_program.two_gap_core_lift ranks
rustc -O analysis/research_program/core_halo.rs -o target/core_halo
python3 -B -m analysis.research_program.two_gap_halo_test 0 180
python3 -B -m analysis.research_program.two_gap_halo_test 1 180 face
python3 -B -m analysis.research_program.two_gap_halo_test 1 180 primal
python3 -B -m analysis.research_program.two_gap_halo_test 1 180
python3 -B -m analysis.research_program.core371_lift_audit
python3 -B -m analysis.research_program.tile_family_board 413 2 --sat --colors=2 --all-phases --dist=5:407
python3 -B -m analysis.research_program.tile_family_board 413 1 --sat --colors=2 --all-phases --dist=5:206
python3 -B -m analysis.research_program.tile_family_board 413 1 --sat --colors=2 --all-phases --dist=209:302 --area=2 --seconds=400
# repeat the last command for 305:353 and 356:407 with --seconds=540
python3 -B -m analysis.research_program.exceptional_287_ledger --413 --drat
```
