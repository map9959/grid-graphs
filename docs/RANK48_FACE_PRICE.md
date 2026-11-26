# Side 103: charging the defects within an exceptional row

At `F=48` the only remaining no-pitch 3647 branch has `C=1,j=0,X=5`.
The original exceptional-row relaxation gives an exact dual upper of
3647.328480608370, **not an exclusion**. Retaining the same face
partition and pricing the actual horizontal defects instead gives
**3644.676194517393**. These are conditional dual bounds on a putative
candidate, not claimed physical optima.

For any length, assign empty stubs to V when reading horizontal rows,
as in the [line–face proof](RANK44_FACE_PRICE.md). On each horizontal
edge with `m` missing predicted slots charge `m` if realized,
`max(0,m-1)` otherwise. This is its contribution to the first slack:
one missing slot may pay for the failed edge, not two. On a row with
H junctions, charge one for each vacant V with no inward hit from
either adjacent H and one for each internal gap between H runs unless
it is a single vacant V with two hits. The former cannot be a mandatory
vacancy of a no-V column; the latter is exactly an undoubled horizontal
gap. On a row without H charge vacancies minus one (no pitch guarantees
at least one). These three sums use disjoint contributions within the
three ledger slacks, so their total over horizontal rows is at most `X`.
The same reasoning applies on the transposed board. This need not bound
the *sum* of the two orientation budgets by `X`.

`priced` carries the previous junction letter, its left hit and
whether a gap has opened after an H. It charges the old vacancy when
its right hit is known, and the gap when the next H closes it.
The terminal transition settles the last vacancy. The audited bound
is imposed on the resulting line flows, still matched to the four-bit
words of the faces.

```
python3 -B -m analysis.research_program.rank44_faces --off 48 --components 1 --replay
python3 -B -m analysis.research_program.rank44_faces --off 48 --components 1 --weighted --replay --ranges
python3 -B -m analysis.research_program.rank48_word_audit
```

The integer upper numerators on scale `10^12` are `3647328480608370`
and `3644676194517393`. The independent audit compared whole-word
charges on all 65,535 non-pitch binary words of length 16 and checked
the debit against the full ledger on 1,816 no-pitch side-ten boards
in both orientations. At fixed `C=1,j=0`, each additional off-skeleton
mark raises both `F` right-hand sides and the slack budget by one;
the weighted dual increases by just `95238211417` numerator units.
It remains strictly below 3647 through `F=72` inclusive.

Together with the earlier branches this requires `F≥49` for any
remaining no-pitch 3647 candidate. Pitch candidates are unaffected.
