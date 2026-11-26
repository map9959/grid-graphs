# A forest constraint missed by the square-patch relaxation

With `X` selected, this three-by-four pattern forces the entire
ten-edge perimeter. Neither three-by-three subpatch contains a cycle:

```
XX.X
....
X.XX
```

Let A and B be the exact masks on its left and right squares, and C
the common two-column overlap pattern. In a distribution over forests,
A and B are disjoint events contained in C. Hence `Pr(A)+Pr(B)<=Pr(C)`.
Matching overlap marginals alone does not give disjointness. The
side-13 example in `analysis/research_program/strip_forest_cut.py`
embeds this configuration off center, orients the cycle cyclically and
the incident branches toward it, then averages over the square's eight
symmetries. Its marginals satisfy all 2261 old rows exactly and violate
the displayed inequality by 1/8. This proves strict strengthening of the
relaxation, not strict improvement in the maximum of its objective.

The `--short` model adds translates and reflections of this inequality.
The full model keeps a distribution over legal forests in each
three-row strip: it tracks connectivity on the last column while adding
edges, rejecting any transition that closes a cycle. Node conservation
gives a unit flow on this layered graph. Each arc flow is at most one;
three-column marginal constraints identify its masks with the old patch
variables. Every actual forest supplies such flows after symmetrization.

```
python3 -B -m analysis.research_program.strip_forest_cut --witness
python3 -B -m analysis.research_program.strip_forest_cut 13 --short --replay
```

The second command, with no LP solver, gives `34000113177/500000000 < 69`.
Thus `P(13,13)=68` using the residue-one construction. The old unpooled
relaxation already rounded to 68 here. This finite result does not yield
a repeating upper certificate.

## Exact optimum of the strengthened period-three relaxation

In the depth-two pooled model, sum the physical 3×4 inequalities by the
coarse types of the two adjacent patch origins and the ordered middle
columns. The fine type of each patch determines the neighboring coarse
type, including at a boundary. Thus these zero-RHS charges, like the
patch-overlap charges, are independent of side within the progression.
There are 49 distinct additional rows after symmetry and deduplication.

For `n=19+3j` (`j>=0`), the exact optimum of **this LP** is
`141+45j+6 binom(j,2) = n²/3+4n/3−14/3`. A dual bounds it above,
and 111 nonzero polynomial variables witness the reverse inequality.
The primal replay verifies every equality coefficient by coefficient;
every required nonnegative polynomial has nonnegative initial value,
first forward difference and second forward difference. Unlisted
variables are zero. The only size-dependent rows are the original
normalizations, whose multiplicities are products of axis-type counts.

```
python3 -B -m analysis.research_program.repeating_patch_dual 2 --three --residue 1 --strip --replay
python3 -B -m analysis.research_program.strip_period_primal --replay
```

The relaxation therefore exceeds the constructed tree count by exactly
`k−3` for every `k>=6`. A different dual of these same rows cannot
close the gap. The primal is fractional and pooled: it is not a tree
or a claim about the optimum of the unpooled strip relaxation.

## Side-19 full-strip lift is impossible for the saved primal

Consider the patches at zero-based origins `(0,2)` and `(0,3)`.
Their common two columns must have the same probability of the event
`10/10/10` when projected from either side. The saved optimal primal
assigns probabilities `1/4` and `0`, respectively. Both origins are
singleton fine position types (depth five), so redistributing mass
within bulk types cannot repair the violation. Thus even a distribution
on the top three rows, without any acyclicity requirement, cannot realize
these marginals. The exact separating inequality is `Pr_left(E) ≤ Pr_right(E)`.

`--lift` refines the pooling of *patch-to-patch agreements* from depth
two to three, keeping the strip exclusions and other rows. Near layers
0,1,2 are now distinct: for the separator, the first patch origin is
pinned at `(0,2)` and the displacement fixes the second at `(0,3)`.
The original fine patch types (depth five) determine all incident
depth-three keys, even at a bulk-to-boundary transition. Thus the
same counting argument applies. The refined repeating dual is unchanged
in value. A different fractional primal matches it throughout `n>=43`
in residue one; finite rational recovery also gives 141 at side 19.

```
python3 -B -m analysis.research_program.strip_lift_witness
python3 -B -m analysis.research_program.repeating_patch_dual 2 --three --residue 1 --lift --replay
python3 -B -m analysis.research_program.strip_period_primal --lift --replay
```

## Separating the replacement at 19 improves the repeating upper

`side19_lift_primal.json` is the recovered finite score-141 replacement.
At origins `(1,3)` and `(1,4)` (zero based), the all-zero six-bit event
on the common columns has left probability `1/2` and right probability
`0`. The replay checks all 1232 rows before extracting these probabilities.
Both origins are pinned by fine patch type, so this also precludes a
lift that redistributes mass within types. No full-strip distribution,
even one allowing cycles, can have different probabilities of the same event.

Add just the equality of those two probabilities to the depth-three
agreement model. This row is independent of side: throughout the progression
the row and both columns are inside the five explicit near layers for patch
types, and reflection fixes the corresponding far distances. Thus it is
a physical necessary condition with zero RHS at every size. The rational
dual gives `P(n,n) <= floor(n²/3+4n/3−16/3)` for `n=3k+1 >=19`, or
`3k²+6k−4`. This reduces the integer gap to `k−4`. A different feasible
polynomial primal matches the *real* upper in this LP for `n>=28`: its
Newton coefficients in `(n−19)/3` are `(421/3,45,6)`. It is not a tree.

```
python3 -B -m analysis.research_program.strip_lift_witness --replacement
python3 -B -m analysis.research_program.repeating_patch_dual 2 --three --residue 1 --pinned --replay
python3 -B -m analysis.research_program.pinned_face pinned --replay
```

## Side-28 pinned optimum fails three strip-projection tests

At `n=28` the saved pinned primal scores `880/3`. Take adjacent patches
at columns 3 and 4; their common columns are 4 and 5. In top strip 0,
the all-zero event on those six cells has mass `1/3` from the left
patch and `0` from the right. Both origins are singleton fine types.
Hence there is not even a distribution over arbitrary top-strip bit
strings with these marginals, let alone one supported on forests.

Two larger discrepancies remain visible without fixing any individual
bulk marginal. Sum the same projection over strips starting at rows `i`
with `4 <= i < n-6`, split by `(i-4) mod 3 = 0,1`. These are unions of
whole depth-five position types. Each sum compares `11/2` on the left to
`0` on the right at side 28 (six strips per sum). Since each physical
strip must agree separately, the summed equalities are necessary even
if probabilities differ at every physical position.

In mode `r28`, append those three zero-RHS rows to the pinned relaxation.
The depth-five types determine inclusion and the neighboring column,
including the fixed near/far layers, for every `n=19+3j`. Their residuals
on the former optimal polynomial are `1/3, j+5/2, j+5/2`.
Replay the extraction and the repeating rows without a solver:

```
python3 -B -m analysis.research_program.strip_lift_28
```

Solver-free replay of the resulting dual:

```
python3 -B -m analysis.research_program.repeating_patch_dual 2 --three --residue 1 --r28 --replay
```

The certificate gives `n²/3+4n/3−2783/504` throughout the progression.
It lowers the real bound by `95/504` but not the integer bound:
it equals `3k²+6k−4+73/504`. No matching fractional optimum for this
strengthened model is asserted.

## Side 28: score 293 is feasible only in the pooled test

`side28_score --replay` verifies a primal with score `147745/504` on
all 1236 r28 rows. Mixing it with the empty selected set in proportion
`147672/147745` gives exactly 293. The shared six bits `00/00/11`
between patch origins `(1,3)` and `(1,4)` then have probabilities
`9669/29549` and `104894/147745`. These singleton fine positions cannot
be redistributed: there is no full-strip extension.

Removing position pooling entirely while retaining the square symmetry
gives an unrestricted side-28 upper of `14470834161/50000000 < 290`,
including the rational dual residual allowance. Integrality and the
construction therefore leave just `288 <= P(28,28) <= 289`.

```
python3 -B -m analysis.research_program.side28_score --replay
python3 -B -m analysis.research_program.patch_square --replay 28
```

## Exact optimum at side 28: the larger value is attained

`P(28,28)=289`. The integer search found the explicit marked grid in
`analysis/research_program/forest_28.txt`. Independent union-find replay
adds all 780 distinct edges incident to its 289 selected sites without
closing any cycle. Its four components can be joined by three additional
grid edges. The verifier constructs that tree and compares its full-degree
vertex set to the witness site by site.

```
python3 -B -m analysis.research_program.verify_forest_28
python3 -B -m analysis.research_program.patch_square --replay 28
```

Together with the rational upper strictly below 290 this settles the
finite square and refutes the proposed residue-one identity for all k:
`3*9²+5*9=288`, one below the actual maximum. It does not invalidate the
old lower construction or determine the other residue-one optima.
