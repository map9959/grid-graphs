# Exact side 103 via arbitrary-height cap prices

The [uniform slit induction](UNIFORM_PITCH_CAP_PRICE.md) subsequently
extends the pitch tariff to all `k≥5`.

**\(P(103,103)=3646\).** At a pitch cut with 35 teeth, let \(h\) be the
number of free rows in one cap, \(b\) its free marks minus \(35h\),
and \(j\) the number of independent joins of its teeth. The finite-width,
all-height result is

* \(j=0:\ b\le8\);
* \(1\le j\le33:\ 10b-7j\le89\);
* \(j=34:\ b\le33\).

There is **no** restriction on the row words, the location of the cut,
the other cap, or any other pitch lines in this cap. In particular
the stronger middle bound 89 suffices for the requested 90.

## Why this settles the square

The [free-count ledger](FREE_FACE_LEDGER_103.md) excludes a no-pitch
3647 maximizer. If there is a pitch line, take that line once, with its
two actual cap forests. Their independent join counts \(p,q\) satisfy
\(p+q\le34\): the incidence graph of their terminal partitions, one
edge per tooth, is a forest. Total marks are \(3605+b_1+b_2\).
If both ranks are below 34, even the bound 89 at both ends (also valid
at rank zero) gives \(10(b_1+b_2)\le178+7(34)=416\).
If one rank is 34 the opposite rank is zero, giving \(33+8=41\).
Thus the total is at most 3646. This requires only **one** pitch cut.
The comb attains the bound: replay gives `(3646,10607,2,10608,3646)`
(designated marks, forced edges, forced components, tree edges,
actual full-degree vertices). It realizes cap pairs `(j,b)=(34,33)`
and `(0,8)`.

## One nonnegative integer bill for the whole cap

Here are the accounting conventions, also used in the [periodic
bill](WIRED_ENDPOINT_PRICE.md). Add one empty guard column on each
side, regard the width \(3r=105\) as periodic, and add one empty row
at the far end. Retain the pitch row as an actual row. The guards
across the wrap are both blank; all padding adds only leaves or
isolates. Orient each terminal tree to a chosen terminal, one per
tree. Call the others *waived*; there are exactly \(j\). Orient each
other nonisolated tree to any marked root.

Tile the width by triples centered on the teeth. Let \(U,U_0\) count
isolates and central isolates, \(V\) count blank noncentral sites with
two marked neighbors, and \(X\) count nonterminal nonisolated trees.
Count both central endpoints of each marked run, twice for a central
singleton. For a vertical run put both units at its start, and exempt
the \(2r\) units on the virtual pitch row. For horizontal runs count
each central endpoint in its own column. To these endpoint units add
\(U+U_0+V+2X\). The result \(B\) obeys

\[
4b=2r+2j-B .
\]

For a direct derivation let \(R\) count marked runs and \(A\) their
central endpoints before exemption. Diagonal exclusion makes the
runs straight. The forced-edge count on the padded rectangle gives
\(3b=3r+j-U-X-R\). Color columns \(2,-1,-1\) with 2 at the centers.
The unclipped closed neighborhood of a run has total color equal to
the sum of its endpoint colors. Clipping the top costs \(2r\); there
is no mark on the bottom row. The number of overlaps of run
neighborhoods is \(R-(r-j)-X\), since contracting the runs and their
joins gives a forest. An overlap contributes 2 except for the \(V\)
noncentral overlaps, which contribute −1. The sum of colors on the
union of neighborhoods is \(U-3U_0\). Hence
\(3A-2R-2r=U-3U_0+2(R-r+j-X)-3V\).
Eliminating \(R\) gives the identity above, including the charge for
trees meeting neither terminal nor any other cap.

## Read a triple at arbitrary height

`finite_cap_language.py` reads one free row per transition. Five mark
bits (three body sites and one halo on each side) determine diagonal
exclusions; one row of memory handles vertical neighbors. Each slit
letter records the two adjacent mark bits and, if a horizontal bond
is forced, its direction. **The whole vertical word** must agree at
a shared slit, not just its last row or a histogram.

Keep the forced-component partition inside the three body columns,
rejecting a redundant internal edge. In a physical oriented tree a
connected fragment contains either its root or exactly one outgoing
slit bond. A retained contact or an outgoing bond uses this slot;
two slots in one fragment are impossible. A fragment containing the
waived contact must reach an outgoing slit. At retirement charge two
for a nonisolated fragment with neither slot. On a physical input
this charges each nonterminal tree once, even when it crosses many
slits: charge its root fragment. Isolates are already charged
geometrically. The blank far row is settled at acceptance, including
its isolates. The automaton can loop any number of times; there is
no height horizon.

`cap_vertex_arrows.py` provides a second transition construction:
enumerate the individual edge directions, allow at most one outgoing
edge per vertex, and charge a nonsending marked vertex two units.
Blank nonisolates cannot be roots, and the first transition fixes the
direction of the terminal spoke according to its waiver. Both versions
are necessary tests. Neither needs the converse that every accepted
global word is a physical cap.

## Width induction and exact exclusion

`ranked_slit_prices.py` builds necessary languages by triple count,
guard (open or physical end), exact number of waived teeth and
integer bill budget. For an empty prefix the open slit allows any
word; a physical guard allows only zeros. Extend a prefix by one
triple, trying both waiver choices and every budget split. Synchronize
the left word, project the right word, trim, determinize and minimize.
Lower bounds on disjoint subintervals add, using the least expensive
waiver split. If the language at that bound is empty, increment it.
All floors start from zero: there are no imported window lower bounds.

The state limits only replace a costly computation by the **universal
language**; they can never produce an empty-language certificate.
At full width test a budget \(70+2j-4b_*\), where \(b_*\) is the
first violating integer bonus. At a split, try all rank and budget
splits. An actual left and right word would agree after reflecting
the right half (swap the mark bits and reverse the direction of a
present bond). A disjoint lower bound or empty product intersection
excludes the budget. Halves of length up to 18 suffice; larger
intervals in the additive tests use only disjoint lower bounds.

`slit_inclusion_check.py` independently checks the necessary-language
inclusions used for the final exclusions. It searches for a word
escaping a claimed output DFA in the product of the input DFA,
the weighted triple transducer and the output DFA. It uses ordinary
shortest paths, **not** the determinization or minimization used to
find the languages. It discharges interval floors by induction on
length before using them and checks the reflected final intersections.
All prices and comparisons are integers.

```
python3 -B -m analysis.research_program.ranked_slit_prices 3000 18 --tight --check
python3 -B -m analysis.research_program.ranked_slit_prices 4000 18 --tight --vertices --check
python3 -B -m analysis.research_program.finite_cap_slit_audit
python3 -B -m analysis.research_program.free_face_ledger
(cd lean && lake env lean GridGraphs/Geometry/PitchSkeletonPrice.lean)
```

The first two runs excluded all 35 ranks with respectively 4,114 and
3,848 direct inclusion checks. In particular the zero-join branch
excludes \(B\le34\) at a 17+18 split. The physical audit reads the
two slit tapes from actual whole-forest parents. It checks the bill
identity and the accepted per-triple costs on all 192 eligible
width-four/depth-three masks and on the two extremal cap types of the
103-square tree (including a depth-100 wired cap).

There is also a shorter independent height reduction at high join
counts. `cap_birth_compression.py` deletes a final row if it starts no
new marked run. In three consecutive nonbirth rows `B,C,D` following
`A`, the masks satisfy `D ⊆ C ⊆ B ⊆ A`. Marks in `B` are spaced by
at least three, or the common marks in `A,B` force a cycle. Drop `B`.
An unsupported bond has its marked owner in `A\B`; its blank endpoint
in `C` is now a leaf (no downward mark in `D`, and a lateral mark
there would be diagonal to the owner in `A`). Thus terminal rank
cannot increase, bonus cannot decrease, and the extra marked-run
count `E` cannot increase. Repetition gives depth at most `3E`.
The finite-end edge count gives `E≤68+j-3b-2` if depth is at
least two. Consequently any violation at ranks 30–33 would compress
into depth at most 12. The completed depth-12 frontier gave weighted
class scores 4537 and 4534 (one class versus multiple), excluding it.
The slit-word proof above does not depend on this reduction.

**Scope.** The triple transducer and bill identity do not depend on
width, but this final interval proof uses \(r=35\). A uniform width
proof in the nonconnected case would follow from \(5B\ge4(r-j)+32\);
this is the general target \(10b-7j\le3k-13\), not an inference
from this one width. The general residue-one formula remains open.
