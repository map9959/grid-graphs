# What can be shortened from 245 to 203?

**The fixed-width, intact-band transfer fails.** In the one-gap
normalization there is an explicit side-245 regional forest whose
charged star is at distance 5 on the west arm. Its forced graph is
acyclic and all complete patches and stars have the required charges.
It has the correct frame. Nevertheless one of its actual 78-step
interfaces has **no 36-step realization**, even when only the marks
on the two ends are retained. This is an obstruction to a regional
shortening lemma, not an upper witness or a proof about *every* larger
full-board forest. The specific partial forest is not extendible.

There is also a global numerical test for a proposed *literal* surgery.
At 245 the target is 20,240 marks and 278 runs; at 203 it would be
13,928 marks and 230 runs. If the deleted rows and columns are aligned
with the interior `3 x 3` tiles and avoid the corner words, they delete
168 perimeter marks and `81²-67²=2072` tiles. To preserve the target
they must remove exactly **6312 marks**, i.e. exactly **72 units of
tile deficit** (three minus the number of marks in a tile). In fact any
such deletion from a hypothetical upper witness that removes *at least*
72 deficit units must create a forced cycle: otherwise its remaining
at least 13,928 marks could be completed to a tree, contradicting
`P(203,203)=13927`. This counting test does not imply that some cut
has the required port attachments.

## The comparison and the counterexample

Normalize the star to north, transposing the entire board for a west
star. Retain the eight-layer rim, the first **102 rows** and the last
**102 columns**. At 203 this is exactly the [certified phase-five
domain](SIDE_203_STAR.md). At 245 the same transverse widths give
41,800 sites, versus 32,560 at 203. The southwest hole grows from
`93 x 93` to `135 x 135`. Deleting 42 rows and 42 columns inside its
two axis intervals maps the *shape* exactly, without thinning either
band. For instance insert at row 150 and at column 100 for a near star
or 12 for a far star. The verifier checks the full coordinate image,
the mapped star, and the corresponding small-board proof.

The archived distance-5 donor has frame index 11 among the sixteen
transposed/untransposed choices: originally `0133`, west star `(5,2)`.
Direct replay on the normalized donor finds 41,626 forced edges, 174
components and zero cycles. It checks every visible edge direction,
the SE-rooted perimeter path, each complete zero-charge patch, and
every complete star (72 at the designated site, zero elsewhere).

There are precisely `94*94=8836` shape-preserving Cartesian pairs of
literal 42-row/42-column deletions. In short-board coordinates the
vertical cut may start at columns `8..101` and the horizontal cut
at rows `102..195`: the preimage of each axis of the hole must lose
exactly 42 entries. For **every** horizontal cut starting at `y`,
old rows `y-1` and `y+42` contain 10 to 12 pairs of marks that become
diagonally adjacent in the retained right band. At least ten pairs
are endpoint-disjoint at every cut. They lie in columns `>=143`, which
no legal column cut removes. A diagonal pair forces the four edges
of a grid square. Thus changing the cut position cannot make this
particular splice a physical forest.

This donor does **not** demonstrate a full-board counterexample. In
normalized coordinates `(102,7)` is uncovered by the known marks:
its only possible new cover in the omitted region is `(102,8)`, which
is diagonal to the retained mark `(101,9)`. Thus that frozen donor
cannot be completed on 245 either. A second archived west-arm example
at distance 29 also fails literal deletion at all 8,836 positions.

```
python3 -B -m analysis.research_program.long_star_quarters 5 5 -1
python3 -B -m analysis.research_program.long_star_quarters 11 53 -1
```

## Arbitrarily refilling the short channel does not repair the transfer

Take the 102 lanes inward from the right side, after the top 102 rows
end. Fix the marks of the first and last cross-sections of a 78-step
piece of the distance-5 donor. Allow all the intervening marks in
a 36-step piece to change. Require zero charge on complete patches
and stars, the two fixed rim rows and the necessary forest constraints.
Do **not** require the old end-to-end partition or old arrows in this
negative test. UNSAT is therefore enough to exclude a replacement
preserving them. The piece is far from the charged star.

This fails for **all 59 straight-piece starts from 102 through 160**,
not just one chosen pair of masks. Group starts by residue modulo three.
Within a group the complete short-piece stencil types coincide: their
normal distances from the side are fixed, longitudinal positions are
in the bulk (distance at least six from the other ends), and the phase
is identical. Each checked disjunction includes the *observed pairs*
of end masks from the corresponding long pieces, not arbitrary
independent left/right marginals.

| Starts mod 3 | Number of starts | Checked resolution steps |
|---:|---:|---:|
| 0 | 20 | 211,370 |
| 1 | 20 | 229,507 |
| 2 | 19 | 501,635 |

At start 150 the end-mask obstruction has a measurable width threshold:
**38 lanes already exclude the short piece**, whereas with just the
first 37 lanes both end masks admit a physically replayed short forest
and zero-charge orientation. This threshold is for these masks and
the stated charge test; the positive width-37 result does not assert
the full port relation there. In fact the same long witness restricted
to **any width from 38 through 102** gives a missing short record:
a short realization at a greater width would restrict to the forbidden
width-38 masks. This is a length/width obstruction for the local
strip rules, not an interpolation in `n`. It transplants to a clean
bulk side interval beginning at 12 on any `119+42s`: the far normal
distance is still at least 17 and the longitudinal stencil phase is
unchanged. No claim is made about other pairs of strip lengths.

```
export PYTHONPATH=target/pb-python
for phase in 0 1 2; do
  python3 -B -m analysis.research_program.star_strip_interface 5 5 1 0 60 "$phase"
done
python3 -B -m analysis.research_program.star_strip_interface 5 5 1 0 30 -1 37
python3 -B -m analysis.research_program.star_strip_interface 5 5 1 0 30 -1 38
```

## Control: the narrow channels really do shorten

Leave only seven-layer ports at the sides, cutting two thin interior
slits. Keep the four bulk blocks up to those slits; a one-site lip
separates a replaceable rim piece from the block alongside it. Clean
cuts can be chosen for **all** previously remaining distances, with
the star either stationary or translated by 42. On the near/far
domains we retained 40,648/40,658 of the 41,209 small-board sites.

For two saved mark/arrow patterns the verifier actually constructs
the four long channels by repeating an interior directed subword:
both successive mark masks, the backwards arrows, the phase, and
the full partition on the permanent and moving ports repeat.
Independent edge-by-edge replay on both boards checks the charges
and compares connectivity **for all retained exterior vertices**.
The early star stays at 5 (157 exterior component classes); the late
star moves `239 -> 197` (259 classes). Neither shortened pattern is
a forest on the *uncut* side-203 proof domain. For example, in the
early replay the marked vertices `(193,10)` and `(195,10)` already
belong to the same retained component. Restoring the omitted vertex
`(194,10)`, even unmarked, forces a cycle. Before shortening those
two terminals were 44 steps apart. There are 44 such single-vertex
closures across the early slits. Port connectivity and the defect
phase alone miss the transverse attachments needed by the proof.

```
python3 -B -m analysis.research_program.slit_star_transfer early -1
python3 -B -m analysis.research_program.slit_star_transfer late -1
```

## Which 245 sites are actually excluded?

These are **direct donor-side** exclusions, not an inference from
equality of the long and short strip relations. In the even phase the
previous fixed NW proofs through distance 194 apply unchanged. For the
seven new distances take the actual 203 forbidden square of side 173
or 197, keep the transverse dimension fixed, and add 42 longitudinal
positions. Each resulting rectangle is already UNSAT at 245. For
phase five use the intact 41,800-site domain defined above. The
following new disjunctions excluded every frame on both arms:

| Distance from open corner | Donor test | `drat-trim` resolution steps |
|---|---|---:|
| 200, 206, 212 | `173 x 215` NW rectangle | 6,501,558 |
| 218, 224, 230, 236 | `197 x 239` NW rectangle | 16,228,592 |
| 197, 203, 209, 215, 221, 227, 233 | two 102-layer bands and rim | 13,136,611 |
| 239 | two 102-layer bands and rim | 13,195,157 |

Both open-corner orientations are represented under the north-star
convention, so transposition covers both arms of each of the eight
original words. The two NW rectangles exclude the same fixed distances
on larger tail boards as well: even coordinate 238 has far-end
distance six at 245. This argument does not transport the full bands.
The phase-five range tests on the other bands returned partial forests
at original west-arm distances 5, 29, 65, 131, and 155. This is not a
positive conclusion about every site of those ranges.

Consequently only `d=5,11,...,191` (32 distances on either arm,
64 sites per frame) remain in the side-245 one-gap case. The rail
completion has 20,239 full-degree vertices; the unrestricted upper is
20,240. **The exact optimum at 245 and the all-size exceptional tail
remain open.** A shortening proof still needs constraints from the
omitted southwest region that rule out the bad long-band end masks, or
a move that also changes those masks.

**Update:** the [southwest completion tests](SOUTHWEST_PORTS_245.md)
exclude all 59 recorded end-mask pairs for upper witnesses across the
entire remaining one-gap site list. Other possible band interfaces are
not classified by that result.

```
python3 -B -m analysis.research_program.shortening_ledger
# append --drat to recheck the recorded proofs
export PYTHONPATH=target/pb-python
python3 -B -m analysis.research_program.long_star_rectangle 2 240
python3 -B -m analysis.research_program.long_star_rectangle 3 240
python3 -B -m analysis.research_program.long_star_quarters 197 233 240
python3 -B -m analysis.research_program.long_star_quarters 239 239 120
```
