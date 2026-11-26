# Side 103: no-pitch net gain with all counts free

If a no-pitch maximizer attained 3647, its ledger would give
`M=3605+F-C-X`, hence `F-C-X=42`. The weighted row and face chart,
without fixing `F,C,j,X` or the score, has the exact certified upper
`10^12 M ≤ 3645265629022938`. Its net-gain upper is
**40.265629022938**, strictly less than 42. Thus a 3647 tree, if
there is one, must have a pitch line. The input to this implication
is a putative above-comb maximum; the numerical bound is not an
unconditional bound on arbitrary lower-scoring forests or on pitch
forests.

## Eliminate the branch parameters before summing the inequalities

Use the full four-corner partition alphabet. Four is the maximum
number of labels visible on one face, **not** a board-wide component
bound. For the same reason the local three-join catalogue contains
all possible face states regardless of the global join rank. Even
alternating corner labels are allowed. Keep the local face/patch
marginals, shared edge words, star measurements and weighted line
transitions of the [weighted defect model](RANK48_FACE_PRICE.md).
In eightfold symmetry averages the physical board gives these
frequencies simultaneously (rotate its actual labels and oriented
forest together).

Write `S` for the star count of junction sinks, `E` for exits; the
physical values are `S=C-j≥1`, `E=j`. Remove *both* rows on the fixed
off-skeleton count (the cap and equality), and remove the fixed sink
and exit equalities. Replace the two branch budgets as follows:

| Measurement | Free-count row | Physical justification |
|---|---|---|
| Sum `R` of local face joins | `R-E ≤ 0` | Independent joins charged inside individual faces use at most the actual rank `j`. |
| Weighted line defect `D` | `D+M+S+E-F ≤ 3605` | The weighted defect sum in each orientation is at most `X`; `X=3605+F-S-E-M`. |

Include `S≥1`. The relaxation maximizes marks, equivalently net gain
up to the constant 3605. It retains the existing no-pitch star/line
conditions. The saved proof **does not need the no-cheap-cut rows**,
a guessed rank interval, the earlier individual branch duals, or an
extra planar/noncrossing constraint.

## Integer replay

```
PYTHONHASHSEED=103 python3 -B -m analysis.research_program.free_face_ledger
python3 -B -m analysis.research_program.free_face_audit
(cd lean && lake env lean GridGraphs/Geometry/PitchSkeletonPrice.lean)
```

The first command reconstructs 38,362 variables and 8,060 rows,
reads `analysis/research_program/free_face_ledger_103_dual.json`,
and sums the rows with integer multipliers on scale `10^12`.
Every inequality sign is checked. Each non-forbidden physical
variable is a local count or averaged count bounded by `103²`
(the line-flow variables count transitions; the auxiliary complete-line
lower bounds can be chosen minimally). Charging all positive column
residuals costs 1,591,350 numerator units, **already included** in
the upper above. Replay requires no optimizer. Regenerate with
`OPENBLAS_NUM_THREADS=1 PYTHONPATH=target/lp-python` and `--save`.

The second command independently orients three physical forests and
reads their whole-board rotated star, patch, rank-face and transition
frequencies. It checks every row, the objective and star counts,
and both budgets; this is a mapping test, not an enumeration argument.

| `M` | `F` | `C` | Local rank / actual `j` | Horizontal, vertical debit / `X` | Violated rows |
|---:|---:|---:|---:|---:|---:|
|3582|2201|1108|1106 / 1106|9, 1076 / 1116|0|
|3536|1130|617|613 / 614|9, 569 / 582|0|
|3610|141|82|80 / 80|45, 7 / 54|0|

The Lean lemma `freeFaceGain` checks the integer implication from the
ledger and the replayed scalar bound. The chart, dual and physical
mapping checks are in Python. This result closes the no-pitch case
at 103, not the pitch case or the arbitrary-side residue-one formula.
