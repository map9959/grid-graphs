# A cap certificate independent of both width and height

For `r=k+1≥6` pitch teeth (width `3r-2=3k+1`), let `b` be the
free-cap marks minus `r` per free row and let `j` count independent
terminal joins. Without fixing the depth or the terminal partition,

```
10b - 7j ≤ 3k - 13    if 0 ≤ j < k;
b ≤ k-1               if j=k.
```

In particular, **the comb is optimal in the pitch-line class for
every `k≥5`**, not just at side 103. If both caps have `j<k`,
their combined bonus is at most `floor((13k-26)/10)`, since their
ranks sum to at most `k`. If one cap has `j=k`, the other has `j=0`
and their combined bonus is at most `k-1+floor((3k-13)/10)`.
Adding the baseline `(3k+1)(k+1)` gives at most the attained comb
score `3k²+5k+floor((3k-13)/10)` in either case.

## What repeats

Use the directed slit letters and local nonnegative bill `B` from
the [fixed-width proof](FINITE_CAP_SLIT_PRICE_103.md). A cap has
`4b=2r+2j-B`. Write `t=r-j` for the number of retained teeth. The
effective bonus is `b-j=(2t-B)/4`. At `t≥2` the goal is
`5B≥4t+32`; at `t=1` it suffices that `B≥6`. This explains why
width alone is not a sufficient state variable.

For a prefix with `t` retained teeth, index the outgoing slit
language by **normalized budget** `z=B-floor(4t/5)`. Keep `t=0,1`
separate; above that use the representative `2+(t-2)%10`. A waiver
leaves the budget offset unchanged. A retention changes it by
`floor(4(t+1)/5)-floor(4t/5)`, determined by the representative.
Ten additional retained teeth translate the raw budget by eight.
The alphabet is unchanged: the complete vertical sequence of marks
and directions is still synchronized, with arbitrary word length.

Direct containment of the raw prefix DFAs is not necessary. For
example, the low-budget floors can recur while larger languages gain
longer words. Instead generate *upper* languages for the normalized
budget slices. Very expensive slices (`z≥5`) get the universal
language. Exceeding a computational limit also only enlarges a
language to the universal one. Neither operation can exclude a tree.

## Induction, including the seam between repetitions

The local triple relation is the left-guard relation for the first
triple and the same interior relation thereafter. Begin at the
all-zero guard word with no teeth and no bill. Independently of the
table generator, `--prove` checks each proposed outgoing DFA. For
each input retained-count representative, either waiver choice, and
each affordable prefix/local budget split, it searches the product
of the input DFA, the local weighted transducer and the output DFA
for a word escaping the latter. It also checks the slice *below*
the proposed minimum, with the empty DFA as target. All budgets
are integers. The upper tail needs no exclusion.

At prefix length **25** this test can use the **very same table as
both input and output** for an additional interior triple, for every
one of its twelve retained-count classes. Thus that table is a valid
upper envelope at all lengths ≥25. This one-step inductive inclusion
is stronger than a comparison between observed widths ten apart.
The alternative transducer, which orients each vertex edge explicitly,
closes at length 24 instead.

Split off the first two triples. The suffix is read from the opposite
guard, reflecting the two mark bits and reversing the direction of a
present slit edge. Check right lengths from four up to the induction
length using the corresponding verified tables. For total retained
count `t≥2`, the first forbidden integer effective bonus is
`floor((3t-16)/10)+1`. This sets the maximum raw total bill to
`2t-4*(floor((3t-16)/10)+1)`; for `t=1` it is 2. Try every
retained-count and affordable bill split and test for a common
accepted word. All such products are empty. For longer suffixes
the stationary table has all twelve representatives already. Adding
ten to a retained count of at least two raises both the raw threshold
and its normalization by eight, so **no untested final budget split
appears**. This covers every `r≥2+4`, including all steps `k→k+10`.

```
python3 -B -m analysis.research_program.slit_width_induction --prove
python3 -B -m analysis.research_program.slit_width_induction --prove --vertices
```

The fragment implementation made 364 direct product inclusion checks
(1,001 terminal rank pairs); the vertex implementation made 324
(924 pairs). The check uses no LP, tolerance, height bound or SAT
timeout. This establishes the all-width **pitch** implication. An
unrestricted all-width result follows on combining it with the
[transported no-pitch certificate](EXACT_SQUARE_FORMULA.md).

## Lean replay and the physical cut

`PitchCut.marked_rank` uses the actual spanning tree and the upper and
lower restrictions of the forced-edge graph of its marks. Cut immediately
above the pitch row and delete the `k+1` distinct tooth spokes. The
forest ledger gives `k+2` components; walking towards any fixed tooth
shows that every component meets some deleted endpoint. The two cap
partitions refine the endpoint partitions of this forest. This gives
the shared rank bound even if the original tree had additional,
unforced edges across the cut. `PitchCut.pitch_score` counts the
physical marks on the two open halves and the pitch row separately.

`SlitProduct.closed_sound` proves the language inclusion test for
arbitrary finite words; the computed product set must be closed and
must contain the initial state. `SlitWidthBound` proves the width
induction, including the sub-floor budget, the normalization change
at retentions and the reflected products for the two guarded ends.
The physical Lean proof now uses a simpler **site-arrow transducer**:
no component partition is stored in a triple. A blank nonisolated
site must send, a marked sink pays two, and each vertex can send at
most once. Dropping the local partition restrictions still gives an
inductive stationary table. Lean generates 387 distinct product requests,
including 78 at the stationary seam. The four local tables have 48, 48,
264 and 264 states. No product inclusion answers are imported.

```
python3 -B -m analysis.research_program.export_slit_lean
(cd lean && LEAN_NUM_THREADS=2 lake build GridGraphs.Tests.CapSiteTableReplay)
```

`CapSite.paddedCapTrace` constructs the two half-words and their exact
bill from **any padded physical cap**. It chooses one root per tree,
preferring terminals then marks, and proves by descent and the forest
edge ledger that its parent arrows cover precisely the physical bonds.
The colored identity uses a direct double count of incidences with
noncentral sites (`CapBill.physical_bill`): each central mark touches
two such sites, each noncentral mark three. A row potential transfers
the central endpoint charges between successive rows, starting at
two per tooth and ending at zero. Both sides read the same physical
arrows, including at the reflected seam.

`PitchPadding` and `PitchPadRank` prove that padding adds only leaves
or isolates and preserves the physical terminal partitions. On the
strict upper half, fold each pitch star onto the tooth's adjacent free
site: diagonal exclusion rules out any off-tooth vertical bond across
that cut. `pitch_upper_interior` then applies `marked_upper_of_traces`
without asking for either trace. Boundary rows and transposed columns
are included in **`PitchCut.pitch_upper_verified`**.

The physical construction and checker soundness use ordinary Lean proofs.
The verified upper's native-evaluation dependencies are precisely two
closed calculations: completeness of the exported site transition rows
for the Lean site laws, and the stationary-language replay.
