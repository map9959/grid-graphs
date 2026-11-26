# P(287,287) = 27,727

At `k=95` the unrestricted integer bound `U` is 27,728. The
[single-defect](ODD_SINGLE_DEFECT.md) and [run](RUN_LEDGER.md)
equalities give one charge of 72, 326 runs, 325 joins and `I=2-g`.
Here `g` counts missing perimeter **edges**, `I` isolated vertices.
Zero perimeter gaps are impossible (forced boundary cycle); the
zero-isolate case has **two** perimeter gaps. The one-isolate case
has **one** gap. These are exhaustive for an unrestricted tree.

* **Two gaps.** Test all 15 frame classes together, with the sole
  charged exit on the nonroot perimeter arc, complementary matching,
  and the [deep-axis restriction](BULK_AXIS.md). No port is fixed.
* **One gap.** Transpose the entire physical board to put the charged
  isolate on the north arm; use [frame exchange](ONE_GAP_FRAME_EXCHANGE.md)
  to set the perimeter to `0133`. Include **every**
  `d=5,8,...,281` for the isolate `(2,d)`, not the survivor list for
  245. Check the tile catalogues against the actual halo at 287 and
  use the [rooted-crop color and area tests](TILE_CASES_245.md).
  Axis 2 forbids vertical deep-center adjacency; axis 1 forbids
  horizontal. They need not be disjoint but they exhaust the cases.

| case | scope | CNF SHA-256 | DRAT resolution steps |
|---|---|---|---:|
| two gaps | all frames | `65b8699338765af0b4b8481d77a77d6b610be05a2a34c92aa36807bbbb57dc32` | 5440843 |
| one gap, axis 2 | 93 distances | `0e0f1d5662b11f6ba80782dbf8f6716acd6da645e1aa8c1f0b34396bc7aa6afd` | 22454 |
| one gap, axis 1 | 5–143, step 3 | `7f45324fb0040c1e3ed012d9a4f78e9fa2e26b4c26dceeb2a9b308df773219ae` | 76054 |
| one gap, axis 1, area mod 2 | 146–281, step 3 | `09365d099a9a2e345243d2c31b27f6578f4b7429652afd4e2274bcc9e6252c78` | 5689636 |

The catalogue ledger checks the 169 base certificates and the
digests of the 198 additional certified templates needed for both
distance phases. The tile exclusions are for necessary relaxations;
the unrelated full-board one-gap timeout was not used. Physical rail
replay gives `(27727,82367,2,82368,27727)`: one connecting edge gives
a spanning tree with exactly 27,727 full-degree vertices.

```
export PYTHONPATH=target/pb-python
python3 -B -m analysis.research_program.two_gap_board 287 220 all --axis --stream
python3 -B -m analysis.research_program.tile_star_catalogue --287
python3 -B -m analysis.research_program.tile_family_board 287 2 --sat --colors=2 --all-phases --dist=5:281
python3 -B -m analysis.research_program.tile_family_board 287 1 --sat --colors=2 --all-phases --dist=5:143
python3 -B -m analysis.research_program.tile_family_board 287 1 --sat --colors=2 --all-phases --dist=146:281 --area=2
python3 -B -m analysis.research_program.exceptional_287_ledger --drat
```

## All-size reduction: the two-gap perimeter can be prescribed

Consider any hypothetical two-gap upper witness on `119+42s`. The
perimeter consists of two disjoint paths, named by their long side
segments. Remove both outer rings. Call a marked depth-two vertex a
*tooth*. Each ordinary tooth has exactly one marked perimeter foot,
two grid steps outward. A closed corner tooth cannot be marked:
both feet would be on the same perimeter path, making a cycle. At
each open corner the tooth **must** be marked: the unmarked depth-one
site behind the missing distance-two foot would otherwise be isolated,
whereas `I=0`. That tooth has one foot on the side without the gap.

Each component of the remaining crop contains a tooth: the forced
graph was a spanning tree and the empty depth-one ring has no other
connections inward. Contract each crop component and each perimeter
path, suppress the intermediate foot-tooth paths, and discard the
other depth-one vertices (leaves). This is still a tree. A crop
component cannot have two teeth on the same arc. Exactly **one**
component has two teeth, one on each arc, and all others have one.
Call the exceptional component the bridge.
The counting implication from these degree bounds and the contracted
edge count is checked in `lean/GridGraphs/Geometry/TwoGapBridge.lean`.

Change only the corner words, keeping the two gap **corners**. At a
closed corner either closed word works. At an open corner choose the
gap on either incident side: the tooth now attaches to the opposite
side's perimeter arc. The ordinary teeth's arc labels are unchanged.
Every depth-one vertex not on a foot-tooth path is still a leaf:
in particular a depth-one corner has just one marked perimeter
neighbor, and behind a missing distance-two foot the tooth is marked.
Thus the new graph is a tree whenever the two bridge teeth still
attach to different arcs. The number of perimeter marks is unchanged.

One can always assign the **two open teeth to opposite arcs** while
maintaining that bridge condition. If both are bridge endpoints they
were already opposite; if just one is an endpoint keep its label and
choose the other freely; otherwise both are free. In cyclic word
notation this chooses equal open digits, `00` or `22`. A reflection
swaps 0 and 2; the two closed words can be reset to 1 after applying
a symmetry. The normal forms are therefore `0011` (adjacent gaps)
and `0101` (opposite gaps). **Only `0011` needs further exclusion**
on the whole tail: `0101` was ruled out by the
[uniform annulus theorem](ODD_SINGLE_DEFECT.md#joining-the-strips-eliminates-five-two-gap-classes-on-the-whole-tail).
This is an existence reduction, not an assertion that every tree
originally has the canonical perimeter.

In fact **neither bridge endpoint is a gap-corner tooth**. After the
opposite-arc normalization, both arcs contain a corner (the corner
and its tooth belong to the same arc). Root at a corner on the
opposite arc to the proposed endpoint. The inward exit must now be
at that tooth's surviving foot. Rotate/reflect to put its open
corner at NW with the north gap: the foot is `(2,0)` and its arrow
must point east. In a `5 x 5` NW window, impose just the frame, this
inward exit costing 72, and the complete physical stencils with the
root outside. The necessary formula has 300 variables and 2478
clauses (SHA-256 `c213846edd23896af2b7e56ba96420234036175d97652b5d09b837cb5e405d7b`). `drat-trim` verifies UNSAT by unit propagation (35 resolution
steps). All stencils, frame bits and root status in this window are
unchanged throughout the progression. The normalization preserves the
interior bridge and the identities of its two teeth, so the conclusion
holds before normalization as well. Both open-corner orientations can
consequently be changed independently without disturbing the bridge.

```
python3 -B -m analysis.research_program.two_gap_exchange
PYTHONPATH=target/pb-python python3 -B -m analysis.research_program.two_gap_tooth 5 15
```

The all-size reduction does not rule out the ordinary-tooth bridge
in `0011`, or the one-gap case on later boards. The next unresolved
side is **329**.
