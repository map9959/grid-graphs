# Side 103: four skeleton components and the 46-mark floor

For a 3647 no-pitch candidate, `C+X=F-42` and `0≤j<C`.
At `F=46`, `C=1,2,3,4` therefore give one, two, three and four
branches respectively. The branch chart fixes 46 off-skeleton marks,
`C-j` junction sinks and `j` exits, with a line-exception budget of
`4-C`. It matches both sides' measurements of each four-mark edge
word as in the [line–face price](RANK44_FACE_PRICE.md).

The exact conditional upper bounds (including positive residuals) are:

| `C` | `X` | `j=0` | `j=1` | `j=2` | `j=3` |
|---:|---:|---:|---:|---:|---:|
|1|3|3646.190502874201| | | |
|2|2|3645.238099893114|3645.523812558273| | |
|3|1|3644.083339296983|3644.535717455989|3644.857145198805| |
|4|0|3639.850101799192|3640.566673015451|3641.266687551126|3641.933434311821|

Every entry is below 3647. Together with the previous floors this
implies that every remaining no-pitch 3647 candidate has `F≥47`.
The physical lower and unrestricted upper at 103 remain 3646 and 3647.

With four skeleton components all 15 partitions of the four face
corners are available, including the four-singleton partition. The
independent graph audit gives 11,990 rank-zero, 1,652 rank-one and
128 rank-two face states at join cap three. The cap-two and cap-three
catalogues coincide, even before the dominance filter; the **global** rank budget and the number of
exits still distinguish those branches. A rank-three join spread
over multiple faces is not excluded by the local catalogue.

Replay without HiGHS:

```
python3 -B -m analysis.research_program.rank44_faces --off 46 --replay --ranges
python3 -B -m analysis.research_program.rank45_audit --components 4
(cd lean && lake env lean GridGraphs/Geometry/PitchSkeletonPrice.lean)
```

For a fixed `(C,j)` with positive exception budget, increasing `F`
by one changes only three right-hand sides: the cap and equality on `F`,
and the line-exception budget. Thus each saved dual gives an affine
upper numerator with slope equal to the sum of those three multipliers;
no numerical reoptimization or rounding of a solution is involved.
There is also a translation on the `X=0` boundary: for `C≥4,j≥2`
increase `F,C,j` together, preserving `C-j`. Here the changing right
sides are the two `F` rows, the exit equality and the rank cap.
Four corners cannot distinguish a fifth component locally, and raising
the join cap beyond three adds no states. Neither translation changes
any dual residual or its allowance.

**This closes the entire `X=0` boundary at side 103**, even for
`F>46`. For `C≥4` and fixed `j=0,1`, each unit increase of `F,C`
decreases the upper numerator by 700000120251 and 699999998165,
respectively. For `2≤j≤C-2`, start at `(4,2)` and take `C-j-2`
steps increasing `C` alone and `j-2` steps increasing both `C,j`
(increment `F` at every step). The two numerator slopes are
`-699998257685` and `+460335`. For `j=C-1`, start at `(4,3)` and
use only simultaneous steps, slope `+107044`. All numerators are on
scale `10^12`; even `103²-46` positive steps cannot reach 3647.
For `C<4` the zero-slack cases are already in the earlier floors.
The conclusion is about the physical ledger slack, not a bound on
arbitrary forests with no restriction on slack.

With positive slack, the fixed-`(C,j)` translations exclude `C=1`
through `F=47`, both `C=2` branches through `F=48`, and all three
`C=3` branches through `F=49`. Thus **at `F=47` only `C=4,X=1`**
remains for the no-pitch test (four choices of `j`).
