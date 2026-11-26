# Three rail backgrounds at a V or Y

**Result.** No target-rate construction in this class on either parity.
This tests two nonparallel oblique legs, not two parallel joins. Coordinates
below are (row,column) in units of side length. A V enters at the two top
corners and ends at a shared bend at (1,1/2). The left leg has primal
period (6,3), the right (6,-3). L, M, R are independent saturated
backgrounds in the left, middle and right regions. Each arm may have
arbitrary fixed depth, with tangential period six. Interface widths are
arbitrary fixed constants. Bend, corner and end neighborhoods must be
bounded on each renewal subsequence. This is not a universal tree bound.

## Budget

On growth of the side by 12, each leg grows by two periods. L covers the
whole left side and half the bottom; R covers the whole right side and
half the bottom; M covers the top. The necessary budget inequality is

    2*(left(L)+top(M)+right(R)) + bottom(L)+bottom(R)
        + 2*(cost_left(L,M)+cost_right(R,M)) <= 12.

This follows from the exact `h+D` growth ledger. It is an asymptotic
increment on the fixed-parity subsequence, not a prediction for a particular
small square. Each leg consumes its own cost from the **same** residual.
Taking independent arm minima and permitting each leg any normal width
favors the construction. Reversing the right leg's direction would
give a different test.

The 60 eligible layouts are transposes of the saturated (3,6) class.
The left leg uses doubled cylinder coordinates `(c,r)`; the right uses
`(last-c,r)`, also transforming the domino directions. `last=8+6*t`
modulo 12 retains the physical far-side phase. In increasing cylinder
normal order the legs run `L -> M` and `R -> M`, respectively. The arm
normal transfer verifies that no finite depth beats the minima used here.

Of `60^3` triples, 998 per parity have nonnegative residual. The
distributions of shared allowances (per pair of leg periods) are
`0:423, 1:300, 2:195, 3:64, 4:16`. After coordinate transforms there
are 184 distinct source/destination queries across the two parities.
A truncated least-loss test (cap at most 2) suffices: summing even its
lower bounds already excludes all 998 per parity. A returned value over
threshold is not an exact distance. No assembly or target seed follows.

## Interior junction and its position

To put the bend at interior coordinates `(y,x)`, draw lines of the same
two slopes up to the top at columns `x-y/2` and `x+y/2`. A vertical
stem of length `1-y` must now separate L and R below the junction: one
cannot place distinct backgrounds on either side without paying for a join.
The allowed triangle of positions satisfies `0<=y<=1`,
`y/2<=x<=1-y/2`. The top-side fractions are `x-y/2, y, 1-x-y/2`
for L,M,R. The bottom fractions are `x,1-x` for L,R. The left and
right sides are unchanged. Each oblique cost has coefficient `2*y`
and the vertical `L -> R` cost has coefficient `2*(1-y)`.

For fixed backgrounds, all these coefficients are affine in (x,y).
It suffices to exclude the three vertices of this triangle. The V is
the vertex (1,1/2). At y=0 the comparison is with a vertical cylinder:
in the limits x=0 and x=1 the arm allowances admit eight ordered pairs
each, all needing a **zero-loss** stem. At x=1/2 there are four, also
needing zero. Exact zero-loss row transfer (`stem_zero`) found no such
path. It enumerates every cyclic row matching, carrying normal occupancy,
previous primal midpoint bits and phase mod six; interior degrees must be
one or four everywhere at zero loss. An incoming-background cut can be
padded to phase zero. All four homogeneous controls at the midpoint
are reached at zero cost. The y=0 endpoint calculations keep the limiting
left/right arm costs from the interior geometry, not those of a different
ansatz in which a vanishing-width region is deleted altogether.

Consequently moving the junction within that triangle cannot pay for
the two legs and the stem. This conclusion assumes that the background
phases are fixed in physical coordinates along a renewing subsequence.
Translations of a join by whole periods cannot reduce its cylinder minimum.

## Reproduce

    cargo build --offline --release --bin arm_depth --bin oblique_cost
    python3 -B -m analysis.research_program.bent_rails
