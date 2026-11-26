# Alternating bands settle `n=56+42t`

For all integers `t>=0`, put `k=18+14t`, `n=3k+2`. Then
`P(n,n)=3k²+7k−1−2t`. The upper half is the
[period-three upper theorem](UNRESTRICTED_PERIOD_THREE_UPPER.md);
its correction is `floor((23−2k)/14)=−1−2t`. This is a computer-assisted
construction proof, not a Lean theorem.

The size-56 physical matching search produced a partial forest. Adding
twelve independently checked boundary marks gave `forest_56.txt`.
Transposing that grid exposes the following regular construction.
It uses a different middle from the previously saved 1096-site family;
the boundary additions need not preserve every mark of that family.

## Prefix

Set `F=9+7t`, so `n=6F+2` and `k=2F`. The exact row generator is
`alternating_zipper.rows`. In the prefix through the second regular
row (`H=F+3`), the marked rods are:

* Top bar `B` on columns 3 through `n−1`; left boundary rail from row 0.
* In column `3a+2`, `0<=a<=k−2`, a central rod from row 2 through
  `2+min(a,k−2−a)`.
* Left columns `3a`, `1<=a<F`, start at `3+a`; right columns
  `n−1−3a`, `0<=a<=F`, start at `2+a`. The outer rails end at `H`.

Each straight rod forces a path with leaves. Different rods meet only
when there are marked sites within Manhattan distance two. There are
exactly three kinds of contacts: `B` meets the right boundary once
through `(1,n−1)`; `B` meets each central rod except the first once
through its row-1 site; the first central rod meets the left boundary
through `(2,1)`. This list describes an acyclic gluing, and no two
outer rails are joined. `alternating_prefix_symbolic.py` verifies the
row/rod identity and both inclusions of the contact list by linear
integer arithmetic for arbitrary `t`. At `H` the frontier is canonical:
each rail and its side neighbors form one class, and the uncovered
gap site is a singleton. Indeed the only edges between identical regular
rows are vertical edges at the rail sites.

## Alternating bands and wide cap

Write `A(L)={0,3,...,L} ∪ {L+4,L+7,...,n−1}`, initially `L=3(F−1)`.
After the advancing rows there are `B=5+5t` full seven-row bands,
five partial-band rows and five cap rows. A full band moves the tip
three columns **right, left, right, left, ...**. Counting from its
second regular row, the last five band rows and the next two regular
rows take the canonical partition back to the canonical partition
at the new tip. This is checked for both directions on width 26 with
tip 12. The final partial band puts in the center mark once; immediately
before the cap, only the two tip rail classes are joined.

The five cap rows keep the regular left rails through `L` in their
first three rows. The additional marked columns there are respectively
`{L+2,n−1}`, `[L+5,n−3] ∪ {n−1}`, and `{L+3,n−1}`. Then mark `{0}`
and finally all columns except 1. The local transfer rejects any edge
closing a cycle. It checks that the **only** penultimate identification
is columns 0 and 1, and that the bottom pattern joins the components
without a cycle.

For completeness, padding the representative with whole pitches is valid
for the cap despite its long horizontal bar. On the left, extra stationary
rails have separate classes throughout the first three cap rows, then
leave independent tips on the penultimate row. The extra bottom-bar
vertices attach each such tip at most once. On the right, insert a pitch
in the interior of the horizontal cap bar, between unchanged right rails
(away from the tip and the right boundary). The new regular input rail
is independent; it ends before the first cap row, leaving one downward
tooth. The extended cap bar meets this tooth once, and otherwise just
lengthens its path and adds leaves. Its lower leaves do not reach the
bottom bar through the unmarked penultimate sites. The old connectivity
is preserved, with only singleton classes added to the penultimate row.
For full bands padding on either side simply inserts independent rails.
The tip is either `3(F−1)` or `3F`, so both margins are at least those
of the width-26 test and differ from them by multiples of three.

## Count and replay

The first two rows have `n−2` and 1 marks. The `F` advancing rows
contribute `Fk+1` (the first has `k+1`, the others `k`). Each full band
contributes `7(k+1)+1` in either direction; the partial band contributes
`5(k+1)+1`. The five cap rows together have `2n+1` marks, independent
of which tip position the alternation ends at. Substitution gives the
upper stated above; the polynomial identity is also checked in the script.

```
python3 -B -m analysis.research_program.alternating_zipper 56 98
PYTHONPATH=target/z3-python python3 -B -m analysis.research_program.alternating_prefix_symbolic
```
