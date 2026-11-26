# Exact square optimum for sides divisible by three

For every integer `k >= 1`, `P(3k,3k) = 3k² + 3k − 2`.
The lower half is formalized in `lean/GridGraphs/Results/DiagonalFormula.lean`
(`matchingDiagonalConstructions_residueZero` and `matchingDiagonalConstructions_residueZeroFinite`).
The upper half is computer-assisted, with exact rational certificates.

For sides `n=21+3j`, use the physical star/patch relations and the
[boundary-type argument](UNRESTRICTED_PERIOD_THREE_UPPER.md) with residue
zero instead of two. Reflection now uses the residue of 21; as before it
is constant throughout this progression. Every star and patch fine type
occurs at the base size. The eight-image averaged charges dominate the
objective on all 3549 local atom/type orbits. Normalization counts give
`166+45j+3j² = n²/3+n−2`. This bounds arbitrary feasible forests.

Reproduce with:

```sh
python3 -B -m analysis.research_program.square_dual_physical --residue 0
python3 -B -m analysis.research_program.repeating_patch_dual 2 --three --residue 0 --replay
python3 -B -c 'from analysis.research_program.square_dual_physical import inspect; [inspect(n,0) for n in (12,15,18)]'
python3 -B -m analysis.research_program.patch_square --replay 6
python3 -B -m analysis.research_program.patch_square --replay 9
```

The smaller sides do **not** rely on extrapolating the polynomial.
At 12, 15 and 18 the same physical stencil applied directly gives
58, 88 and 124. At 6 and 9 the separate finite rational certificates
give upper bounds strictly below 17 and 35, respectively. At 3 the
known exact value is 4. These exhaust the omitted positive multiples.
