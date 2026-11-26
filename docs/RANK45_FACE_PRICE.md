# Side 103: six rank branches at 45 off-skeleton marks

If a no-pitch maximizer attains 3647 with `F=45`, the ledger requires
`C+X=3`, with `X≥0` and `0≤j<C`. The table gives the bounds on this
putative candidate from the [line–face word chart](RANK44_FACE_PRICE.md).
The decimals are exact, including the allowance for dual residuals.

| Skeleton components `C` | Extra slack `X` | Actual joins `j` | Conditional score upper |
|---:|---:|---:|---:|
|1|2|0|3645.523819880360|
|2|1|0|3644.535738791782|
|2|1|1|3644.857144116612|
|3|0|0|3640.550339858879|
|3|0|1|3641.266671283081|
|3|0|2|3641.933384151921|

Each branch fixes `F=45`, junction sinks `C-j`, exits `j`, and permits
at most `3-C` exceptional rows in the horizontal line measurement.
The four-bit edge words are matched between row transitions and their
adjacent faces. A face sees the equivalence relation induced on *its
four actual corners*, not four independently chosen wire connections.
There are 14 possible corner partitions with at most three blocks:
all partitions except four singletons. Rotate or reflect a partition
by transporting the corners and then renumber the blocks in order of
first occurrence. Across a shared edge its endpoint equivalence survives
the renumbering. As before, the model relaxes global consistency, but
every physical labelling supplies a feasible assignment.

The independent audit counts added edges versus the decrease in the
number of connected components, then repeats the dominance test using
sets of connected perimeter pairs. For `C=3,j=2` this gives 11,524
rank-zero, 1,552 rank-one and **104 rank-two** allowed states. All 104
are retained. This tests the extra possibility not present at `F=44`.

```
python3 -B -m analysis.research_program.rank44_faces --off 45 --replay
python3 -B -m analysis.research_program.rank45_audit
(cd lean && lake env lean GridGraphs/Geometry/PitchSkeletonPrice.lean)
```

Replay loads `analysis/research_program/rank45_dual_{C}_{j}.json` for
each branch, checks the signs and the integer-scaled objective bound,
and asserts it is strictly below 3647. To regenerate, use `--save`
instead of `--replay` with `PYTHONPATH=target/lp-python` and one BLAS
thread. No fractional witness or SAT timeout is used as an exclusion.

Together with the two earlier floors this proves `F≥46` for any
remaining **no-pitch** 3647 candidate. The unrestricted upper remains
3647 and the actual tree lower bound remains 3646.
