# How much of the smaller 413 core transfers?

**There is a lossless strip transfer in the row direction. We do not
have a lossless transfer in both directions.** Nevertheless for every
`n=413+42t`, a two-gap upper witness in canonical frame `0011` would
require its ordinary north exit to be **at least 308 sites from each
north corner**. This eliminates the two-gap case at 455, 497, 539 and
581. It leaves three exits, `308,311,314`, at 623. It does not exclude
the one-gap case.

## Actual source and choice of seams

Running `drat-trim -c` on `target/core371_lift/halo_1_primal` retained
179,213 of 1,912,722 clauses (`s VERIFIED`, 1,701,142 resolution steps).
The extracted DIMACS itself has SHA-256
`147844e50f0c73f13a5e69205b6407c03293d57d056d43a6a16a0587f77ff53d`;
a new proof of that **standalone input** replayed in 2,991,205 steps.
Decoding the ID pool gives 20,459 marks reaching depth 75, 57,412
arrows, 15,691 face owners (all in rows 0–60, columns 49–304),
67 exit flags, two gap-tooth color bits and 210 global/counter IDs.

The cut at row 193 crosses only 18 local clauses. Deleting just those
already gives SAT. But in the entire neighborhood of the row interval
153–192 the only physical IDs are marks and arrows within five steps
of the west or east side. This is enough for the following stronger test.

* On each of those two sides take a strip eight sites thick. Its entry
  records two consecutive columns of marks (in the strip's longitudinal
  direction) and the arrows pointing into the preceding column. Its
  exit also records the connectivity partition of the end vertices and
  whether the strip used a charged exit. For the complete relation,
  **39 and 81 steps give identical sets** for all 1,022 entry labels:
  16,554 end records and 239,994 ordered pairs. Composition gives the
  same equality at `39+42t` for every `t`. Use a zero-charge filling.
* Restrict a putative larger forest to these two separate strips.
  Replace each long piece by **a** 39-step piece with the same end
  data, not necessarily the same interior marks. The two mark columns
  and backwards-arrow bits give consistent physical edge ownership
  at each join. The end partition allows gluing without creating a
  forced cycle. The pieces avoid corners, the short exit, and one
  another. No corresponding claim is made about shortening an entire
  two-dimensional board.
* Translate the other upper and lower data on the appropriate side of
  the cut. A clause involving changed strip variables is retained only
  if supplied by a common physical strip formula (zero-charge complete
  patches/stars and compatible arrows, with the marked straight frame).
  In particular no complementary face owner is inferred from a mark
  word at a join. Comparing signed clauses recovered **all 996** such
  clauses; the other **178,217** came from unchanged blocks. Including
  duplicates, all 179,213 source clauses are present. The resulting
  UNSAT certificate replayed in 5,001,801 steps.

The height insertion can therefore be handled in the core without
postulating a repeated filling. A square enlargement must *also*
handle the column insertion, and this is where the same proof fails.

## Testing arbitrary column insertions

Write the added width as `42u+42v`. In the reference square insert
before column 19 and before column 394, with the reference exit `e`
in the middle. The physical exit is then `d=e+42u`. Reconstruct the
perimeter directions from that exit and the NW root. Row and column
activation flags are global physical tests. Counter bits select just
one exit among the retained slots; they are not periodically copied
per-site data.

Using width-eight replacements starting at columns 12 and 360 as
well as the row replacements recovers 5,206 source clauses in
addition to 173,136 unchanged ones, but leaves **871 clauses** out.
All 67 individual exit assumptions passed the resulting *partial*
SAT test. The seam is not justified simply by moving all original
clauses apart.

A second test retains all original physical clauses whose literals
do not straddle an insertion, then links the two ends:

1. For each transverse pair of aligned tile rows or columns away
   from the other cuts, take the certified ordered two-by-two tile
   words with the actual straight frame and tangential arrow direction.
   Apply the surviving deep axis and, for a horizontal track, the
   two physical row flags. Compare whole powers of the resulting
   finite relation. The endpoint tile distance is `1+14u` across the
   first column cut, `1+14v` across the second, and `1+14(u+v)` at
   the row cut. All endpoint marks refer to the same physical sites
   in the adjoining blocks.
2. For the two side strips meeting each cut, retain the marks,
   backwards primal arrows and acyclic strip transitions using the
   same kernel as the height test. Around the cut the two stored end
   states are `2+42u` steps apart (respectively `v` or `u+v`).
   The DP compares the full labeled state maps, including partitions,
   before projecting to mark/arrow end pairs. No assumption about
   periodicity of a physical mark word enters either computation.

For an anchored exit (`u=0`) the **unions** over allowed lengths give
necessary constraints. The raw split core plus width-seven links
excluded 22 fixed distances `110,113,...,173` for every enlargement
on the far side; its physical input before extraction excluded 40,
`110,113,...,227`. The two union proofs used 4,902,424 and 7,190,970
DRAT steps, respectively. Each is an end-range result only.

For an explicit test of the remaining ambiguity take **intersections**
of the endpoint relations over positive insertion counts, not unions.
Here this stronger condition is used **only for a positive model**:
one set of end assignments must work at *every* such length. The DP
retains exact ordered-pair or labeled-partition maps until a repeat;
composition then covers every subsequent length. In the width-eight
owner track the maps agree at 44 and 86 steps. Retaining all available
mark and primal-arrow information of the 1,912,722-clause input except
at the three cuts still leaves 1,910,436 unchanged clauses. The stored
assignment at reference exit **182** satisfies them and **970,247**
further interface and perimeter clauses, with exactly one exit flag.
The audit checks every clause of both inputs. For `u=3+j,v=2+k`,
`j,k≥0`, this permits `d=308+42j` at side `623+42(j+k)` in this
projection. Both end distances can grow without bound. No new track
interior is frozen to the old one. Different projected tracks may
still disagree **inside** an inserted region; this is not a model of a
full forest or a proof that no other uniform transfer is possible.

## Uniform exclusion of two larger end ranges

Take physical NW windows on the side-413 chart. The full overlapping
mark, arrow and face constraints are shared throughout each window.
Set the perpendicular deep axis as required by the
[previous transfer](TWO_GAP_EXIT_TRANSFER.md). Require the selected
exit, give other marked north teeth their outward arrows, and give
distinct visible north teeth different component labels. Keep the
other marks free.

| permitted NW exit `d` (step 3) | width × height | CNF SHA-256 | DRAT steps |
|---|---|---|---:|
| 107–200 | 270 × 99 | `8768834ee23f064abceae9c096752c124d74f56cf37e4720b60db6c68ebfd89a` | 13982210 |
| 203–305 | 373 × 114 | `08acb26b563487cde76a3e164b68c44f3ce86f888a7f2d6f147de98729d13b85` | 18070144 |

These fixed boxes are already separated from the far boundaries at
413. Under enlargement, all coordinate tags (end distances clipped
at 16 and coordinate mod 3) stay identical, including a two-site
halo. Frame bits, root status and the perimeter paths on the visible
arms stay identical. The charge, matching, color and axis clauses
therefore restrict an actual larger witness to the same impossible
formulas. Unused axis flags outside a window give no restriction.
As a check, reconstruction at 413 reproduced the two proof-input
hashes. At 455, removal of unused flag implications and renumbering
yielded **identical ordered clause streams** to the normalized 413
inputs, with SHA-256 prefixes `0c00ff315b70` and `f69071087d90`.

For the NE end, reflect the *whole* board. Reset its corner words to
`0011` by [two-gap frame exchange](EXCEPTIONAL_287.md): the ordinary
bridge teeth and their interior component do not move, and the
ordinary north foot is still on the short arc. Root anew at NW.
Thus the same exclusions apply to `n−1−d`. Combined with the prior
end exclusions, the only arithmetically open distances are
`308+3j`, `0≤j<max(0,14t−67)`. The arithmetic and clipped-coordinate
implications are checked in `lean/GridGraphs/Geometry/TwoGapExitCover.lean`;
this Lean file does not replace the DRAT checks.

## Replay

```
export PYTHONPATH=target/pb-python
target/drat-trim/drat-trim target/core371_lift/halo_1_primal.cnf target/core371_lift/halo_1_primal.drat -c target/core371_lift/halo_1_primal.core
python3 -B -m analysis.research_program.core413_seams setup
target/cadical/build/cadical -t 240 target/core371_lift/halo_1_primal.core target/core413_uniform/raw_core.drat >target/core413_uniform/raw_core.log
target/drat-trim/drat-trim target/core371_lift/halo_1_primal.core target/core413_uniform/raw_core.drat >target/core413_uniform/raw_core.check
python3 -B -m analysis.research_program.core413_seams locations
rustc --edition=2021 -O analysis/research_program/core_seam_filter.rs -o target/core_seam_filter
python3 -B -m analysis.research_program.joint_rim_pump 8
python3 -B -m analysis.research_program.core413_pumped 1 N 0 --all
python3 -B -m analysis.research_program.core413_pumped 1 LR 15000
python3 -B -m analysis.research_program.core413_free_tracks core 10000 --flush --anchored --owner=7
python3 -B -m analysis.research_program.core413_free_tracks halo_1_primal 6000 --flush --anchored --owner=7
python3 -B -m analysis.research_program.core413_free_tracks halo_1_primal 50000 --flush --positive --stationary --owner=8 --only=182
python3 -B -m analysis.research_program.two_gap_exit_box 270 99 155 left 120 --axis=1 --side=413 --exits=107:200:3
python3 -B -m analysis.research_program.two_gap_exit_box 373 114 251 left 180 --axis=1 --side=413 --exits=203:305:3
python3 -B -m analysis.research_program.core413_corner_transfer
python3 -B -m analysis.research_program.core413_uniform_audit --drat
```
