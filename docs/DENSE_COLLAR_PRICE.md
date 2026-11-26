# Pricing dense collars against their retained core

Let `n=3k+1≥103`, `m=n-20`. A side arm has `m` slices between the
two `10×10` corners. There are two different comparisons here. The
first prices arbitrary words; the second gives a stronger all-length
step for dense, punctured bars. Neither forces every maximizing square
to belong to the second class.

## Arbitrary words: a rank-charged closed annulus

Keep the six removed layers and the `m`-square. Sweep the four layers
**between them**. Let their original counts be `R`, `I`, and `Z` for
the intervening band, respectively. In the disjoint fixed forests
choose any set `S` of component labels (old collar, core, or both).
Keep the actual known neighboring marks. For a candidate band forest,
tag every incidence of a forced crossing edge at a label in `S`. A
component of the band with `a` incidences pays `max(0,a-1)`. Write
`v` for the total charge. If the whole original is feasible,

```
v ≤ max(0,|S|-1).
```

Indeed the bipartite graph on the touched band components and selected
labels, with one edge per incidence, is a forest. Parallel edges are
not independent. Compute `A=max(scale*Z-fee*v)` by transfer. The
maximization may relax unselected connections, so
`scale*Z ≤ A + fee*max(0,|S|-1)` even with arbitrary deeper marks.

The sweep retains the actual band partition, a touched bit per live
component, and the physical masks. Merging two touched components
pays once; two ports first arriving at the same site also pay once.
An ordinary redundant physical edge is rejected, not just charged.
Fixed diagonal exclusions apply at both interfaces. The closed version
carries the opening cut until the final side meets it; the cheaper
four-piece version relaxes the cut edges. Neither identifies two real
backing trees in order to declare a physical cycle. Runtime in side
length is linear for a fixed band width and a fixed choice of labels.

At price one per three marks, select all inner labels and `h` outer
labels. The inner component count `c` enters the allowance as
`h+c-1`. The *same* `c` is already subtracted in the inner ledger
`3I+r+c=m²+D` (`r` marked runs, `D` marked boundary degree deficiency).
Consequently

```
3M ≤ 3R+A+h-1+m²+D-r .
```

This bound needs no inner partition: flag every core-facing port,
and use `r≥(M-16n+170)/m` from the ten-layer cap. With the actual
partition, price different label subsets and combine with the
[retained-core bounds](RETAINED_CORE_ENVELOPE.md). Finite tests:

| 103 input | No inside partition, closed sweep | With partition |
|---|---:|---:|
| ordinary comb | 3646 | 3646 |
| locked fringe | 3634 | 3611 |
| holes with returns on both sides | 3648 | 3635 |

The entries certify completions of those interface data. They are not
an exhaustive enumeration of all interfaces.

### A projected charge for arbitrary lengths

Let `B₁₀` count straight slices different from the mask at depths
`0,3,6,9`, `O` the number of crossing edges marked at both ends, and
`P` an upper on marked carriers spanning the core from one opposite arm
to the other. For `P` use the largest spaced (distance ≥3) subset of
collinear opposite double contacts **in the same inside component**.
Take the larger axis count: straight through carriers cannot cross.
Then for any certified core run floor `r₀`,

```
3M ≤ n²+4n-1-ceil((B₁₀-8)/3)-max(-P,r₀-O).
```

For one arm, charge `d=outer holes + starts of marked runs + isolated
sites` at physical depths `0..9`. Count runs by adding the number of
marked blocks in each slice and subtracting its marked-to-marked edges
to the preceding slice. Count isolates only after inspecting both
neighbors, including depth ten. The two extra end slices are the
actual adjacent physical slices. The finite potential proves
`B_arm≤3d+2` (48,798 states and 8,385,590 integer inequalities).
It enforces diagonal exclusion and both orientations of the six-edge
rectangular cycle, relaxing longer cycles. The four arms have disjoint
isolates. Marked carriers counted in two arms must traverse the core;
alternatively counting the core runs separately double-counts at most
`O`. Substitute into the full forest ledger, keeping one non-isolated
component on nonempty inputs. This gives the displayed bound. For
example, with `P=o(n)`, more than `(21/10+ε)n` nonpitch slices suffice
for the comb upper at all sufficiently large sizes.

## Dense punctured bars: a rank loss around the four corners

Suppose on each straight arm the depth-nine holes are at least three
sites apart. At each of the eight arm ends the first nine bits are
marked precisely at depths `0,3,6`. No other arm slice is prescribed.
The corners, the retained core, and the connections between different
sides are free. Then the outer **nine** layers satisfy

```
T₉ ≤ 12n-89 .
```

This reduces the side by **18** at no more than the difference of the
two comb scores. In particular at 103 the sum is `1147+2499=3646`.

**Side prices.** Within a straight arm the depth-nine path is already
connected, holes included. Depth eight must be empty: a mark would
require holes at both tangential neighbors. The end bits explicitly
cover the two endpoints. Contract the depth-nine path. There are
eight free sites per slice. A depth-seven mark attaches to the root
via the blank site unless its spoke is omitted at a hole. Retain
the identities of the three physical groups at the first pitch cut,
the root, and the frontier partition. At the last pitch cut measure
`s=6-(number of classes among the six end groups)`, including paths
via the root. The first or last spoke status is irrelevant since
the end bit at depth seven is zero.

| local rank | 0 | 1 | 2 | 3 | 4 | 5 |
|---|---:|---:|---:|---:|---:|---:|
| side maximum excess over `3L`, holes ≥3 apart | −4 | −2 | −1 | 0 | 0 | 0 |
| corner maximum, excluding end slices | 36 | 36 | 37 | 38 | 38 | 39 |
| side upper for `9*(marks-3L)+B`, holes ≥4 apart | −22 | −11 | −3 | 3 | 9 | 12 |

Here `B` counts slices not marked precisely at `0,3,6` in the outer
eight sites, **not** backing holes. These are full-vector recurrences,
not extrapolations of maxima. For the first row the normalized pair
of clean/open prefix vectors repeats at 17 and 18 interior steps,
and for the last row at 50 and 51. A separate unrestricted-end
transfer proves the suffix bounds `marks≤3L+5` and, respectively,
`9*marks+B≤27L+46`. Thus an unweighted prefix below `-11` or weighted
prefix below `-100` cannot improve a reported rank maximum, even with
the best continuation. Forgetting a vanished component preserves
equalities of the three retained initial labels. No intermediate
mark is pinned. In particular, pricing the *number* of dependent
spokes as though each cost a mark would be wrong: `donor_nullity`
finds positive relative drift at gap three even for price `1/3`.

**Corner prices.** Free sweep of the two adjacent end slices and their
corner, with a bit on each component that has seen one of the six
terminal groups. Joining two flagged components increments the rank.
Ignore the depth-nine corner mark (it is not counted); retain the
blank reentrant corner vertex for the forced-square test. The end
slices have already been counted in the arms.

**Gluing is what removes the last marks.** Contract each common pitch
cut on its three groups before gluing. There are only 24 seam vertices
on eight cuts. The sum of the eight terminal ranks is at most **23**:
replace each local forest by its tree identifications on terminals;
a redundant identification in their union would be a cycle in the
original forest. Extra contacts through the interior or corners may
only tighten this. Each corner price is ≤`36+2s/3`; each side excess
is ≤`2s/3-2`. Adding and rounding gives an overhead of at most 151 over
`12(n-20)`. Simply adding unrelated elbow maxima does not give this.

**Linear debit and the remaining gap.** If holes are at least four
apart, the weighted row and the same rank argument give the stronger
bound `9T₉+B ≤ 9*(12n-89)+15` (corner price times nine ≤`324+6s`;
weighted side excess ≤`6s-15`). If `G` is the physically achievable
rim gain on the smaller `(n-18)`-square, the resulting upper on the
original is

```
U(n-18) + 12n-89 - G + min(0,floor((15-B)/9)).
```

At gap three use the unweighted bound. With `C(k)` the comb at
`n=3k+1`, one has `C(k)-C(k-6)≥12n-89`. Thus the unweighted case
alone prevents a **first** counterexample with the stated cuts; it
does not assume an unconditional smaller comb upper. In the weighted
case `B+9G ≥ (1/10+ε)n` suffices even with the *known unrestricted*
smaller upper at all sufficiently large sides. Without prescribed
end cuts the free-end weighted recurrence still gives `9*marks+B≤27L+46`
per straight interval, provided the eight-site reduction is valid
(in particular depth eight blank at the two ends). Use the free
corner cap 42 instead of the rank argument; this changes only the
additive constant in that linear criterion. At 103 the free-ended
test is `B+9G≥329`; for example, wholly nonpitch arms have `B=332`
and need no gain at all. No assertion is made that all arms satisfy
either that test or the pitch-end condition.

**Moving a pitch cut.** The eight cuts need not be at fixed locations.
Move each one inward along its arm to any pitch slice, keeping two
distinct ordered cuts per arm. Require depth eight blank on the
straight slices absorbed by the corners. The hole-spacing condition
is needed only *between* the chosen cuts. For a corner with shifts
`h,v`, `collar_bend dense-ranks h v` computes its six prices
`K(h,v,s)` without assuming the absorbed slices repeat. The sweep
adds `h+v` slices to the corner and excludes its two pitch slices from
the count. For the unchanged total baseline `12(n-20)`, use corner
entries `K(h,v,s)-3(h+v)` in the eight-piece rank maximization.
This follows by removing exactly those slices from the four side
lengths. The seam rank budget remains 23. Any choice with maximum
at most 151 gives the same induction step, even if the original
eight end slices were not pitch. This is a test on cut locations,
not an assertion that such locations exist.

For `0≤h,v≤3` the complete six-entry corner table is exactly the
unshifted table plus `3(h+v)` at **every rank**. This was checked
on the ten unordered pairs (reflection exchanges `h,v`). Thus each
of the eight ends may independently move zero through three slices
with *no* loss in the reduction. The weighted bound likewise applies
with `B` counted only on the surviving sides: extra corner marks are
exactly offset by the shorter side baseline. Larger offsets require
their own bound; the unbacked corner sweep did not yield a normalized
period-one certificate.

**Changing the cut word instead of its position.** At the nominal
eight cuts, allow any three marks among depths `0..7` spaced at least
three apart, with depth eight blank. The four possibilities are
`036`, `037`, `047`, `147` (digits are physical depths). With the same
three-apart depth-nine hole condition the bound is still `12n-89`;
there is no requirement that the depth-nine end sites are marked.
Compute the six rank prices for each of the ten unordered pairs of cut
words, separately for a side and for a corner. The first side column
starts with the forced-edge groups of its actual word, with its
backing spoke present or absent according to the depth-nine bit.
If absent, the hole-spacing counter starts at zero. The closing
column makes the same choice subject to that counter. The previous
suffix pruning bound applies unchanged (the final slice still
contains exactly three marks). The cyclic maximization remembers the
shared word at each join and total rank at most 23. Its overhead is
151. Dropping both end spokes regardless of the spacing counter gives
152 instead; that weaker relaxation would miss the exclusion at 103.
This four-word test is at nominal cuts; the shifted result above
was checked with the single `036` word.

## Two physical uses of an arbitrary rim word

At depth `d` let `b` be the original rim count. Optimize this same
ring twice: once against the unchanged exterior only (`e_o`), once
against the actual inside only (`e_i`). Both include the rim, so
subtract `e_o+e_i-b` from the sum of the two domain uppers. For depth
nine these are `16n-170` and `U(n-18)`. The outside port sequence
splits a corner into two **equal-bit** tokens, so both exterior edges
are priced. Enumerate the two ways to leave at least one of the two
arms of each reentrant corner blank. Then the noncrossing path/ring
transfer applies to the *actual* exterior partition, and backtracking
gives an actual forest. Neither refill assumes it can coexist with the
other on the original board.

On the 103 complementary-return test, `b=311` and both separately
attained 323. Together this gives 3642 with the unconditional cap.
On the double-return test the two exact maxima stayed at **311**.
The universal cap then gives 3666, but the rank-priced dense-arm
bound still gives **3646**, or **3640** with its measured 63 bad
slices. The example completed to a tree with 3566 actual full sites;
it is not a superior tree. In the repeated double-return construction
there are at least `12 ceil((n-60)/9)` bad slices, enough to pay the
smaller-square linear gap at every `n≥103` in this family.

## Reproduction

```
for f in dense_contact_price dense_backing_arc dense_pitch_dominance collar_bend; do
  rustc -O analysis/research_program/$f.rs -o target/$f
done
target/dense_contact_price 2 3 0
target/dense_backing_arc 3 1 0
target/dense_backing_arc 4 9 1 0 2
target/dense_pitch_dominance 3 1
target/dense_pitch_dominance 4 1 weighted
target/collar_bend dense-ranks
target/collar_bend nine-bases
python3 -B -m analysis.research_program.dense_joint_collar
python3 -B -m analysis.research_program.dense_collar_check
python3 -B -m analysis.research_program.dense_cut_words --replay
python3 -B -m analysis.research_program.dense_bridge_price --closed
(cd lean && lake env lean GridGraphs/Geometry/DenseCollarPrice.lean)
```

The exhaustive small comparison tests both optimum refills and the
closed weighted sweep on 12,288 physical candidate masks. Lean checks
the summed rank and reduction arithmetic, not the graph sweeps.
The unrestricted task remains to cover the missing configurations or
produce a better construction; checking larger individual boards
does not establish that coverage.
