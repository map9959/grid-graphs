# Delaying the last right-front advance: six sharp residue-two progressions

For `b` in `{38,44,50,62,68,74}`, `n=b+42t`, `t>=0`, let `k=(n−2)/3`.
Then

    P(n,n) = 3k²+7k+floor((23−2k)/14).

For `b=56` this construction gives **one less** than that upper bound
for every `t`; it does not settle this class. The upper half in every
case is the [unrestricted period-three dual](UNRESTRICTED_PERIOD_THREE_UPPER.md).
The lower half is a computer-assisted construction, not a Lean theorem.

## Prefix and frontier

Write `n=6F+2`, `k=2F`. Make the `F` advancing rows of the two-front
zipper, advancing both tips every time **except** on the last update,
when only the left tip advances. The tips then stand at `3F` and
`3F+4`. Use the upper-left repair all the way to column `3F`:
unmark `(0,1)`, mark `(1,0)`, mark `(a+2,3a)` for `0<=a<=F`,
and unmark `(a+2,3a+2)` for `0<=a<F`. The repair gains one mark.
All coordinates start at zero.

The [repaired-prefix rod argument](REPAIRED_ZIPPER_PROGRESSION.md)
has an important difference here: there is **no extra connection**
between exterior rails. Specifically, up through row `F+4` its
`B,W_a,L_a,R_a` decomposition uses `m=F`, with `0<=a<=F` on the
left and `0<=a<F` on the right. The wedge end rows still use
`2+min(a,k−1−a)−[a<F]`. Unlike the odd-`k` case, `W_F` ends at
`F+1`, not `F+2`. The only contacts between different rods are the
top bar with `L_0`, the top bar with `W_a` for `1<=a<k−1`, and
`W_(k−1)` with `R_0`. Each is a single shared unmarked vertex. A star
of rods plus a separate pair and disjoint rods is acyclic. The checked
symbolic interval and contact queries cover every `t`, not just the
physical examples.

The second regular row therefore has the **canonical** partition: each
rail and its neighbors are in one frontier class, separate from the
other rails, and the intervening gap site is a singleton. Extra
regular waiting rows preserve this partition (only rail columns
carry forced vertical edges). This applies whenever the first two
regular rows are counted as waiting rows or as part of the first band.

## Middle and cap

After the top three rows and `F` advancing rows, use `e` waiting rows,
`B` complete bands and `h` partial-band rows before the final five-row
cap, where `7B+h=n−8−F−e`. Tip at the cap: `M=3(F−B)`.

| `b` | `e` | `B` at `t=0` | `h` | `M` at `t=0` | score minus upper |
|---|---:|---:|---:|---:|---:|
|38|1|3|2|9|0|
|44|0|4|1|9|0|
|50|0|4|6|12|0|
|56|2|5|2|12|−1|
|62|0|6|2|12|0|
|68|0|7|0|12|0|
|74|0|7|5|15|0|

Per increment in `t`, `F` increases by seven, `B` by five and `M`
by six. All full-band transitions except the last take a canonical
frontier after two regular rows to the next such frontier. For the last
one, `delayed_right.terminal(h)` instead processes its remaining five
rows, **exactly** `h` partial rows (no tip shift), and the five cap
rows. The transfer contracts the current partition, rejects cycle
closures, and checks that all classes on the empty penultimate row are
singletons. This works even for `h=0` or `1`: it does not presume that
two regular rows precede the cap.

As in the [complete-band proof](RESIDUE_TWO_ZIPPER.md), the terminal
check needs just width 23, starting tip 12 and final tip 9. Every
actual `M>=9` and `n−M>=14`, with both margins congruent to the test
modulo three. Insert whole pitches between unchanged outer rails,
away from the moving tips. Every such rail has its own component and
leaves; before the bottom bar is added it supplies a new independent
tip and isolates in the empty row. Thus padding cannot invalidate
the cap check. The same margin argument applies to all preceding bands
(their left tips are at least `M+3`, their right margin at least
`n−3F=3F+2`).

## Cardinality and reproduction

Before the repair, the top contributes `(n−2)+1+(k+1)`. Each advancing
row has `k` marks: at advancing step `a` each exterior side has `a+1`,
and the middle contributes `k−2(a+1)` (zero on the last step).
Each waiting row has `k+1`, a complete band `7(k+1)+1`, and the final
partial band `h(k+1)+[h>=3]`. The cap contributes `3k+3+n`. Add one
for the repair. Substituting the table parameters yields the last column
identically in `t`; `repaired_prefix_symbolic` checks the polynomial
identity and the upper-bound floor separately.

```
python3 -B -m analysis.research_program.delayed_right 44 86
PYTHONPATH=target/z3-python python3 -B -m analysis.research_program.repaired_prefix_symbolic 44
```

For the other progressions substitute the indicated base (and its
successor for the physical test). On sides 44 and 86 the verifier
reconstructs the canonical partition at each full-band input, rejects
any forced cycle, completes a spanning tree, and checks 685 and 2545
full-degree vertices, respectively.
