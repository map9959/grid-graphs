# Side 103: weighted line–face bounds at F=49

For a no-pitch 3647 candidate `F=42+C+X`, where `C` counts skeleton
components and `X` is the slack after mandatory vacancies. Using the
[weighted defect count](RANK48_FACE_PRICE.md), the remaining branches
give the following integer-replayed conditional upper bounds:

| `C` | `X` | `j=0` | `j=1` | `j=2` | `j=3` | `j=4` |
|---:|---:|---:|---:|---:|---:|---:|
|2|5|3644.390479085790|3644.680959316540| | | |
|5|2|3641.357170190014|3642.071430752553|3642.780006590227|3643.480004528816|3644.138111394938|

All entries include the positive reduced-cost allowance; none uses a
floating-point comparison for exclusion. For fixed `C=2` the two
certificates continue to exclude through `F=76` and `73` respectively.

## Transport in three parameters

Keep the variables and coefficient matrix of a `C=5` weighted chart,
generated at `X=2` and join count `r`. A putative candidate with
parameters `X,C,j` changes the two `F` right-hand sides, the `C-j` sink
equality, the `j` exit equality, the line budget `X` and (if present)
the face join cap `j`. Substituting `F=42+C+X` therefore gives an
integer numerator `U + p*(X-2) + q*(C-5) + s*(j-r)`. The residual
allowance in `U` is unchanged. For `r=0,1` use only `j=r`. For
`r≥2`, the full four-corner catalogue contains all possible
partitions and all admissible join ranks. Smaller physical palettes
embed by leaving colors unused: the checker compares every required
labelled mask and its rank, including for `C<4`. Shared edges only
read the relative labels of their two ends.

For `C≤4` evaluate the applicable affine bounds directly. For
`5≤C≤35²` cover the legal joins by five sectors: `j=0`, `j=1`,
`2≤j≤C-3`, `j=C-2` and `j=C-1`. Use the corresponding certificate
`r=0,...,4` throughout each sector. For fixed `X` each bound is
affine, so it suffices to check the endpoints of the four segments
and the three vertices of the triangle. The latter are `(5,2)`,
`(1225,2)` and `(1225,1222)`. `trianglePrice` in Lean verifies the
vertex argument. Exact maxima of these bounds across both component
ranges are:

| `X` | Uniform conditional upper |
|---:|---:|
|2|3644.138111859818|
|3|3644.900015393546|
|4|3645.680077365546|
|5|3646.780076305511|

Thus all four slack levels are excluded, without a cap on `F` apart
from the physical board. With the previous zero- and one-slack
certificates, any remaining no-pitch candidate has `X≥6`. At
`F=50` this gives `C≤2`; the fixed-component bounds cover `C=1`
through 72 and `C=2` through at least 73. Therefore `F≥51` is
necessary. At `F=51` only `C=3,X=6` needs testing.

**Follow-up, `F=51`.** The three weighted duals at `C=3,X=6` replay
to numerators `3644200002843374`, `3644496826831962`, `3644776191550088`
for `j=0,1,2`, on scale `10^12`. At fixed `C,j` they exclude through
`F=73,77,74` respectively. Replay with
`python3 -B -m analysis.research_program.rank44_faces --off 51 --components 3 --weighted --replay --ranges`.
Thus `F≥52` is necessary, but there is no argument here for termination
of the floor-by-floor strategy. The size-independent no-pitch target
for the comb conjecture is `F-C-X ≤ k-1+floor((3k-13)/10)`, by
subtracting `(3k+1)(k+1)` from the comb score.

```
python3 -B -m analysis.research_program.rank44_faces --off 49 --components 2 --weighted --replay --ranges
python3 -B -m analysis.research_program.rank49_transport
(cd lean && lake env lean GridGraphs/Geometry/PitchSkeletonPrice.lean)
```

The second command replays the five `C=5` certificates before checking
transport. No restriction on pitch candidates follows from these tests.
