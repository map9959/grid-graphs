# Why the residue-two constructions repeat after 42 sides

Put `n=3k+2`. The [unrestricted upper](UNRESTRICTED_PERIOD_THREE_UPPER.md)
is `U(k)=3k²+7k+floor((23−2k)/14)` for `k>=6`. For integer `k` this
is simply `3k²+7k−floor((k−5)/7)`: the odd numerator does not create
fourteen distinct rounding phases. Its floor correction
drops by exactly one when `k` increases by seven. Thus the rounding
phase is `k mod 7`, not fourteen independent numerical corrections.
There is also a geometric parity: `k` even gives `n=6F+2`, while `k`
odd gives `n=6F+5`. In advancing toward the middle in steps of three
columns, the fronts have different stopping configurations. The pair
`(k mod 7, k mod 2)` repeats at `k+14`, i.e. `n+42`.

Each cell gives the **proved starting side** `b` of a tail `n=b+42t`,
`t>=0`. Thirteen tails attain `U(k)`; the exceptional one attains `U(k)-1`.

| `k mod 7` | Even `k` | Odd `k` |
|---:|---|---|
| 0 | 44, delayed right front | 23, ordinary zipper |
| 1 | 68, delayed right front | 47, repaired upper left |
| 2 | 50, delayed right front | 71, repaired upper left |
| 3 | 74, delayed right front | 53, repaired upper left |
| 4 | 56, alternating bands | **35, rail, `U(k)-1`** |
| 5 | 38, delayed right front | 59, ordinary zipper |
| 6 | 62, delayed right front | 41, ordinary zipper |

In the ordinary zipper, raising `n` by 42 adds seven advancing rows.
The remaining 35 additional rows fit five whole seven-row bands. The
end of the final band therefore meets the bottom boundary in the same
phase. This accounts for a sufficient construction period, not a
minimal-period theorem for `P`.

* Ordinary zipper: [whole-band ending](RESIDUE_TWO_ZIPPER.md) and
  [partial endings](PARTIAL_BAND_PROGRESSIONS.md).
* [Upper-left repair](REPAIRED_ZIPPER_PROGRESSION.md): preserve one
  extra rail connection until the cap.
* [Delayed right front](DELAYED_RIGHT_ZIPPER.md): preserve separate
  rail components at complete-band inputs.
* [Alternating bands](ALTERNATING_ZIPPER.md): move the tip alternately
  left and right and use a different bottom closure.

For the exceptional cell, the rail count is `U(k)−1`; the exclusions at
35, 77, 119, 161, [203](SIDE_203_STAR.md), [245](TILE_CASES_245.md), [287](EXCEPTIONAL_287.md), [329](EXCEPTIONAL_329.md), [371](EXCEPTIONAL_371.md), [413](EXCEPTIONAL_413.md), [455](EXCEPTIONAL_455.md), [497](EXCEPTIONAL_497.md), [539 and 581](ROADMAP.md#active-checkpoint)
prove equality with `U(k)−1` there, not on the whole progression.
The [coupled-mask proof at 623](EXCEPTIONAL_623.md) gives
`P(623,623)=129967` as well. [Arbitrary-length strip closure](FOLDED_STRIP_ENLARGEMENTS.md)
rules out two-gap equality throughout the remaining tail, leaving the
one-gap case. The [synchronized-front proof](SYNCHRONIZED_FRONT.md)
gives `P(665,665)=148039` and rules out axis 2 on the remaining
progression. The [odd fan and line-speed proof](ODD_FAN_SPEED.md)
eliminates the final axis-1 cases uniformly. The
two cells in the `k mod 7 = 4` row are a useful contrast. Both have
only `1/14` of slack between the rational upper and its integer floor.
The alternating construction *does* attain the floor on the even
tail starting at 56. Rounding alone cannot explain the failures at
35 and 77. On the odd tail an [all-size charge and parity
test](ODD_SINGLE_DEFECT.md) now rules out the pair of half-defects
realized at 56: attaining the floor would require exactly one full defect.
