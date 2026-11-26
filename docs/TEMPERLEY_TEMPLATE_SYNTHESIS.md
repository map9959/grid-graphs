# Target-directed Temperley template synthesis

This is a finite grammar test, not an impossibility theorem for arbitrary trees.

Use a doubled square of side `2*base-1+6t`, root at the top left. Leave `a`
rows above and `2*base-1-a` rows below the growing array, and likewise `b`
columns to the left. The array has `t*t` six-square tiles. The running
diagonal is one tile, each strict triangle one periodic background. There
are four independent corner rectangles and four independent repeated arm
rectangles. All tiles, including individual domino directions, are unknown.
A direction variable names a site **in a template piece**, never a specific
copy. Opposite-facing directions at neighboring sites must agree, including
across joins; no arrow can leave the board or enter the missing root.

For each original vertex, a Boolean score bit is equivalent to the absence
of any incident midpoint pointing toward a face. Identical score signatures
are counted with multiplicities. Thus both matching and score use fixed
template variables. For `t>=3` in the plain grammar local signatures have
quadratic multiplicities: corner contacts occur constantly, each arm and
each diagonal seam grows linearly, and homogeneous triangle interiors have
triangular counts. Feasibility constraints and first/second score differences
are computed from several translated arrays; the code checks vanishing
third differences signature by signature. A failed necessary test at those
indices alone rules out a template meeting the constraints at those indices.

The quadratic coefficient of a target-achieving square family requires both
triangles to saturate the toroidal area bound. Each then has one of the 24
period-three rail tilings on a doubled six-square torus (see
`TEMPERLEY_DIAGONAL.md`). The solver can explicitly branch on this implied
restriction. Four sectors, two-phase staggering, thicker diagonal bands
and end adapters are experimental options, not included in the exhaustive
plain census below.

## Results

* `base=5`, primary diagonal, root top left, all 36 splits `1<=a<=b<=8`
  (the other half are transposes): solver UNSAT for simultaneous target
  reference score and target growth. Specifically for n=14,17,20 the
  requirements are initial score >=76, first gain >=34, and second
  difference >=6. This test could exclude a family that starts below
  target and eventually catches up; the slope-only test avoids that.
* All 36 splits were rerun with `loss=200`, which removes the initial
  score constraint altogether: **36 UNSAT, 0 unknown** at 15 seconds per
  instance. Thus within the plain base-five grammar, when the area term
  is saturated, the increment at k=4 is at most 33, not 34. The control
  below attains 33. This is a sharp growth obstruction for this grammar.
* `base=2`, primary diagonal, all three splits up to transpose: with full
  area coefficient, the maximum first gain at `k=3` is 26 instead of the
  required 28. For each split, gain >=27 was UNSAT and >=26 SAT.
  Thus no bounded starting advantage can save this version asymptotically.
* Positive end-to-end control:

      python3 -B -m analysis.research_program.temperley_synthesis \
        --a 1 --b 1 --loss 200 --slope-loss 1 --seconds 20
      base=5 split=1,1 vars=1349 clauses=6089 status=sat
      replayed tree scores: [68, 101, 140, 185, 236]

  The replay reads direction variables, verifies every domino partner and
  checks the primal tree independently. The last score is outside the
  indices used to form the constraints. This example misses one unit per
  growth step; it does not meet the target.

Run the default census with `run(5,a,b,seconds,0)` from
`analysis.research_program.temperley_synthesis`; `loss=200` removes the
initial-score requirement at base 5 while keeping the growth constraints.
`unknown` is inconclusive. UNSAT here means solver-reported, not a
separately checked proof trace.

## Two-phase experiment: alternate both arms and diagonal

`--stagger --offset 0` and `--stagger --offset 1` use independent templates
for each parity. Sites in the two triangular backgrounds depend on both
tile indices mod 2. Each diagonal and each arm alternates between two
arbitrary matchings. The period is now six primal grid units per side.
The necessary first gain at base five is 74 (k=4) or 86 (k=5), and the
second difference is 24. The initial score need not be constrained.

Full area forces each triangle to use one of the 96 saturated 12-square
backgrounds. Over one period an arm is a balanced rectangle. Its two end
profiles cancel in checkerboard balance, and its physical border is closed.
Thus its inner profile must contain equally many black and white ports.
Each background abuts two perpendicular arms, leaving 36 of 96 choices.

`alternating_invoice.py` fixes a pair of such backgrounds, giving 1296
cases. Let S0,S1,S2 denote same-parity scores. With second difference 24,
the first gain is 24 plus `3*S1-2*S0-S2`. The code groups the latter
expression's score bits by their tile signatures. Pure-background bits
are evaluated exactly. Every other nonzero bit has coefficient +1 and
belongs to precisely one of the four arms or the diagonal. Maximize these
five groups independently, dropping corner joins: this can only overstate
the gain. Unknown local feasibility answers retain the previous upper
bound, never an exclusion. The per-pair maximum is an upper bound even
when the five locally optimal pieces cannot be assembled simultaneously.

Observed bounds (solver-assisted, no independent UNSAT trace):

| base-five split | k | pairs checked | two-step upper | required |
|---|---:|---:|---:|---:|
| (1,1) | 5 | 1296 | 84 | 86 |
| (4,4) | 5 | 1296 | 84 | 86 |
| (2,5) | 5 | 1296 | 84 | 86 |
| (4,4) | 4 | 1296 | 72 | 74 |

Run `python3 -B -m analysis.research_program.alternating_invoice 4 4 1`
(last argument is offset). The original coupled solver also found a
relaxed k=4 split-(1,1) template with replayed scores 67,139,235,355,499,
gains 72,96,120,144, exactly two short per step. The area and growth
tests on all three base-two splits up to transpose returned UNSAT on
both parities. These results neither exclude arbitrary wider boundary
regions nor establish a target-scoring seed. A timed-out coupled solve
does not supersede the regional upper bound.

## Freely retiled neighbors of the diagonal

The regional checker now accepts `band=1`: `i=j-1`, `i=j`, and `i=j+1`
each have two separate, unknown six-square tiles. Thus there are **six**
free diagonal tiles, not three copies of one alternating tile. On the two
strict outer triangles the backgrounds are still independent saturated
12-square patterns. Inside the three-tile band all matching variables
remain distinct and the joins are enforced. Matching constraints at the
ends involving corners/arms can be dropped in the upper relaxation.

At centered base-five split `(4,4)` there are 66 distinct score bits with
unit weight touching this band, and 18 per arm, on both parities. The
background-only term is evaluated with its actual signed weights for the
selected layout pair. For each pair the program asks whether the diagonal
can cover the remaining target after giving it the benefit of the full
independent arm allowances. Returning `threshold-1` after UNSAT is an
**upper bound**, not an attained maximum. A timeout returns the full
unconstrained count of diagonal bits, so it cannot cause a false exclusion.

For `k=6`, a complete pass over 1,296 background pairs bounded the gain
by 97 against a required 98, before imposing the end joins or testing a
seed. For `k=7`, retrying the local threshold with a second solver tactic
when needed gave 1,296 UNSAT, no remaining pairs, and upper 109 versus
required 110. These two exclusions were obtained **without** the optional
analytic cut-flux bound added later. Reproduce the regional test with:

    python3 -B -m analysis.research_program.alternating_invoice 4 4 0 1 1
    python3 -B -m analysis.research_program.alternating_invoice 4 4 1 2 1

The extra unit of diagonal width changes the evaluation index: these band
tests use `t=5+offset`, `k=6+offset`. They do not test variable-width
transition regions or nonperiodic backgrounds.

As an independent geometry check for extensions of the band, the doubled
cylinder can instead be read by normal slices `d=r-c`, with `c mod 12`
along each slice. Each site on slice d matches either to the preceding
slice or to the next; its two possible forward neighbors have column c
or c-1. Thus there are only 4,096 incoming occupancy masks and 103,682
legal occupancy transitions. Occupancy alone does not score the band:
one must retain the vertical matches and the previous odd-slice midpoint
labels. `python3 -B -m analysis.research_program.diagonal_cylinder` replays
1,152 slice transitions from the 96 saturated backgrounds and recovers
12 preserved centers per 6-square primal period for every one. This check
does not independently certify the regional solver's numerical bounds.

One exact way to bound variable-width interfaces without carrying an entire
previous score mask is a *cut flux*. On an infinite periodic primal tiling
or its torus, take any set S of vertices and let F denote the full-degree
vertices. For each directed tree edge `p->q` ending in F let
`delta=1[q in S]-1[p in S]`. Define

    flux = sum delta on F->F plus 2 sum delta on U->F
    terminals = sum_{p in S intersect F} (2 - degree_F(p))
    waste = number of U->U arrows whose source lies in S.

Then `6|S intersect F| = 2|S| + flux - terminals - 2*waste`.
Indeed, 3 times the number of F in S counts incoming arrows, which equals
the number of arrows out of S's vertices ending in F plus the total
unweighted cut flux on such arrows. The F->U arrows out of S's F vertices
number `(terminals + F->F cut flux)/2`, by the FF degree sum. Substitution
gives the identity. Terminal and waste terms are nonnegative because FF
cannot turn or branch. The flux need not vanish in an open band; dropping
it would give an incorrect interface bound. `diagonal_cylinder.py` checks
the signed identity on periodic normal strips and their available local
domino-flip controls. This identity by itself does not pay the full
boundary of a finite rooted square.
