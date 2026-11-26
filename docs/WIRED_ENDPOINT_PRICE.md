# An arbitrary-height tariff for a wired pitch cap

For any periodic wired cap of width `W=3r` in the
[run-join conventions](CAP_RUN_JOINS.md), let `b` be its bonus over
`W/3` marks per free row. At **every width and height**,

```
10 b ≤ 3 r .
```

This is the comb rate, `b/W ≤ 1/10`, attained at width 30. Use the
full-bar normalization of [the run-join proof](CAP_RUN_JOINS.md);
a smaller bonus discarded there does not weaken the upper. Periods
shorter than a test window may be unrolled.

**Exact bill.** Remove the blank row and full bar. Add the virtual
pitch row as actual marked teeth at `x=0 mod 3` on the other end.
Call this phase central. Let `t` count the bottom teeth, `t₀` the
central ones, `U` the isolates, and `X` the other tree components
apart from the distinct terminal trees and isolates. In the augmented
prefix debit:

* one for each off-center bottom tooth;
* at central sites, one for every horizontal run endpoint, and two
  for the start of a vertical run (singletons vertical), except starts
  on the virtual pitch row;
* one for a blank **noncentral** site joining two marked neighbors;
* one per isolate, plus one more if central, and two per `X` component.

The total `B` satisfies **`4b = 2r-B`**. To see this, color columns
`2,-1,-1`. The infinite-lattice neighborhood of any straight run has
weight equal to the sum of its two endpoint colors, including a
singleton twice. At the two ends put back the clipped neighbors,
giving total `2r+3t₀-t`. There are `r+t+E` runs (here `E` counts
nonterminal runs), `r+t+X` nonisolated tree components, and every
other nonisolated component is unicyclic. The number of overlap
corrections is `E-X`, including any self-contact of a run around the
cylinder. A correction is `2` except at a noncentral join where it is
`-1`. Combining this identity with `3b=2r-t-E-X-U` gives the stated
bill. Equivalently, `E-b` is **exactly** `t₀+X` plus the number of
central nonterminal run endpoints, noncentral joins and central
isolates. These defects are separately nonnegative.

**Five consecutive triples.** Keep a one-column halo on either side.
Sweep down from the virtual row. The state contains the current row,
the preceding bits above its central blank cells, and the forced-component
partition of the row with the top wire. Tags remember a mark or access
to the halo/top. Charge a completed nonterminal marked tree only if
it never touched a halo. Such trees are wholly contained in the billed
region; in overlapping windows their prices are bounded by assigning
each global `X` cost to one of its marks. At the bottom require all
present teeth to have separate classes distinct from the wire. No
constraint is placed on height: shortest paths explore the finite
state graph up to the nonnegative budget. A state-limit exit is not
a certificate.

Two triples cost at least one and three cost at least two. If five
cost at most three, both their `2+3` and `3+2` decompositions attain
these lower bounds. Before sweeping five triples discard row transitions
absent from any successful projected small-window path with its
budget. All locally feasible five-window completions below four units
then have bill three, bottom row empty, and the row above contains
all 15 marks or all except the leftmost or rightmost. This is an
implication with free vertical end cuts, not a guessed period.
Summing over every starting triple counts each debit at most five
times, so without a 14-bar `5B ≥ 4r`. Substitute in the exact bill.
More generally, if `l` starting positions have one of the three
exceptional bottom signatures, `20b ≤ 6r+l`.

```
rustc -O analysis/research_program/pitch_endpoint_tariff.rs -o target/pitch_endpoint_tariff
python3 -B -m analysis.research_program.pitch_endpoint_windows
python3 -B -m analysis.research_program.vertical_cap_tariff
```

**Why even long partial bars cannot improve the rate.** Assign each
extra tree's two units to one of its marks. This gives nonnegative
integer bills per triple. If their cyclic mean is strictly below
`4/5`, start just after the last maximum of the partial sums of
`5 bill - 4` over one period. Every nonempty prefix of the infinite
repetition has strictly negative sum (choose the maximum among the
starts, including the empty prefix). In particular the first triple
is free, the first two cost at most one, and the first three cost
exactly two. At lengths `3+5j` the bill is at most `2+4j`, and
eventually strictly less. Before the first strict drop, a five-triple
block costs four; the stopping block costs at most three. In either
block the first two cost exactly one and the first three exactly two,
by the prefix bounds and the two small-window lower bounds. Hence
after every continuing block its last two cost two, as do the last
two triples of the initial three.

Slide a seven-triple window by five, keeping those last two triples
plus their two halo columns as the overlap. A continuing window has
budget six, a stopping one five. `wired_cap_rate.py` gives the
complete list of local subwindow budgets from the preceding paragraph.
The finite vertical sweep emits a nondeterministic automaton, retaining
accumulated price as well as the physical state; backward distances
discard states unable to terminate in budget. Each letter on the
overlap specifies all eight marks in one row and the directions of
the forced horizontal edges across its three inter-triple slits.
These directions can be chosen **once on the whole cap**: direct
each terminal tree toward its terminal, any other tree toward a root,
and a floating unicyclic component toward and around its cycle.
Inside each window contract the unobserved edges. Each resulting
tree fragment can have at most one prescribed sink or outgoing slit
edge, since its internal tree edges already use all but one outgoing
slot. This necessary test is maintained across the entire height.
Marks alone on the overlap admit a spurious stopping word.

Project the initial automaton onto the possible right-overlap words,
then apply the continuing automaton as a letter-to-letter relation.
Each time test intersection with the left language of the stopping
automaton. The four minimized reachable languages have respectively
`56,95,111,111` states. **All four intersections are empty** and the
last language is contained in an earlier one, checked by product
search, not inferred from the state counts. Images preserve inclusion,
so a stop is impossible after any number of continuing blocks. This
contradicts strict negative drift and proves `5B≥4r`. Width is handled
by language inclusion and height by finite-state reachability; neither
is bounded in the theorem.

```
rustc -O analysis/research_program/pitch_endpoint_tariff.rs -o target/pitch_endpoint_tariff
python3 -B -m analysis.research_program.wired_cap_rate
```

For a **free-ended finite rectangle** of width `3r` made of complete
pitch triples, separate translated copies by three empty columns,
with the same pitch continued across the guard on the virtual row.
No free marks of different copies share a neighbor, and each old
component can attach to the common top root at most once. For `h`
free rows the score is thus at most `(3r+3)(h/3+1/10)`. Removing
incomplete triples at the ends changes the price by `O(h+1)`, the
per-piece error allowed in the multiscale cut argument.

**A cap with actual terminal joins.** Let `j` be the number of
independent joins of the `r` pitch terminals in a free-ended cap.
Equivalently it is `r` minus their number of tree classes, counting
an isolated contact as a class. There is a second arbitrary-height
price

```
20b ≤ 6r + 15j.
```

For the periodic accounting use a prefix without full rows; for the
finite rectangular transfer use separated copies and the empty end
padding, which ensures this automatically. More generally retain one
terminal sink per terminal tree, preferring a bottom tooth if present.
Waive the redundant top sinks, charging one unit per waiver. If a
terminal lies on a floating unicyclic component all its top sinks are
waived. The number of nonisolated tree components becomes
`r+t-j+X`. The same weighted and ordinary neighborhood counts now give
`4b=2r+2j-B`; a through vertical run contributes its two central
endpoints only once in the actual bill. This identity also works with
arbitrary joins by taking the last prefix row blank, i.e. `t=0`.

The language proof now charges `B+j`. Two and three triples still
cost at least one and two. For each window allow all subsets of
waived top sinks consistent with its budget, keeping the other top
teeth wired. A true component which has a waived terminal still
leads to its retained terminal or out of the window; a completed
extra tree confined to the billed columns may still be charged.
The overlap now also names which top sinks were waived. An immediate
stop after the initial three is excluded with the full eight-triple
window (budget five). Start the continuation from these actual first
eight with budget six. At the next two tests the right languages have
109 and 128 states, both stop intersections are empty, and the second
language is contained in the first. Thus `5(B+j)≥4r`, as required.
The coefficient of `j` in the resulting mark price is `3/4`;
the sharper `7/10` tradeoff would not follow by rounding.

```
python3 -B -m analysis.research_program.wired_cap_rate --rank
```
