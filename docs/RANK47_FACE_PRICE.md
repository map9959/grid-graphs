# Side 103: the one-slack boundary

At `F=47`, the [previous certificates](RANK46_FACE_PRICE.md) leave
`C=4, X=1`. In the line–face chart, fix `F=47`, sinks `4-j`, exits
`j`, the local join budget `j` and one exceptional row. Integer
dual replay (including every positive reduced-cost residual) gives:

| Actual joins `j` | Conditional upper on the putative 3647 score |
|---:|---:|
|0|3643.583335277439|
|1|3644.083338656079|
|2|3644.535715973101|
|3|3644.857148726391|

The four saved duals also exclude **all side-103 no-pitch candidates
with `X=1`**. For `C≤3` these were cases at `F=44,45,46`. For `C≥4`
use `F=C+43`. Increasing both `C` and `F` keeps the line budget at
one. The face alphabet is unchanged because all four-corner partitions
are allowed; at `j≥2` the local catalogue is independent of `j`
(the global rank cap still changes). Hence the right-hand-side
translations in the previous certificate apply at this new budget.
On scale `10^12`:

* For `j=0,1`, each increment of `C,F` lowers the numerator by
  499999917047 or 499998569384, respectively.
* For `2≤j≤C-2`, start at `(4,2)`. Increase `C` alone relative to
  `j` exactly `C-j-2` times (slope −392857317626), and increase both
  exactly `j-2` times (slope +18036). Even charging the positive
  slope for every one of `103²-47` steps gives 3644535906469333.
* For `j=C-1`, start at `(4,3)` and increase both, slope +162407.
  The corresponding worst numerator is 3644858864069125.

Both worst numerators are below `3647 * 10^12`. Replay:

```
PYTHONHASHSEED=47 python3 -B -m analysis.research_program.rank44_faces \
    --off 47 --components 4 --replay --ranges
```

For fixed `C=4,j`, increasing `F` instead increases the exception budget:
the same signed sums exclude through `F=51,50,50,50`, respectively.
At `F=48`, `C=5,6` are on the one- and zero-slack boundaries;
the earlier fixed-rank ranges exclude `C=2,3`. Thus just `C=1,j=0,X=5`
remains at that floor. No pitch candidate is excluded by this argument.
