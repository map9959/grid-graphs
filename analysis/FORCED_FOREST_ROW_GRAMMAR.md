# Exact Forced-Forest Row Grammar

`forced_forest_row_grammar.py` is a proof-discovery tool for finite square
instances. It is an exact computation for each requested `n`; its output is
not a theorem, a proof of the diagonal formula, or evidence covering sizes
that were not computed.

For a binary forced set `F`, the graph has every grid edge with at least one
endpoint in `F`. The grammar enumerates `F` one row at a time and maximizes the
cost `|F|`.

## State semantics

A state is `(forced_mask, partition)` after processing a row.

* `forced_mask` records membership in `F` on the active row.
* `partition[c]` records which component of the processed forced graph contains
  column `c` of the active row.
* Labels are canonical in first-column occurrence order, so equivalent
  frontier connectivity has one representation.
* Every active-row vertex is represented, including an isolated non-forced
  vertex: a forced vertex in the next row can add a vertical edge to it.
* A component that no longer intersects the active row is retired and dropped.
  Retired components need not be connected to each other; disconnected forests
  are valid.

A transition restores the summarized old connectivity, adds all vertical edges
touching `F`, adds all horizontal edges in the new row touching `F`, and rejects
the transition if any added edge joins vertices already in one component. The
new partition is then restricted to the new row and canonicalized.

Run a finite search with:

```bash
python3 analysis/forced_forest_row_grammar.py 6 --witness
```

The unit tests compare the grammar with direct enumeration of all forced sets
through `n=4`, check reconstructed witnesses, and compare modest feasible sizes
with the empirical exact `P(n,n)` values in `data/diagonal.csv`.

## Diagonal CEGAR result

`forced_forest_diagonal_cegar.py` enumerates every reachable transition through
width 7 and assigns row charge

```text
q = n+3-3|F_row|.
```

Thus `sum q >= 2` is exactly `3|F| <= n^2+3n-2`; at widths divisible by three
the sharper requested target is `sum q >= 4`. Run the committed experiment:

```bash
python3 analysis/forced_forest_diagonal_cegar.py \
  --output analysis/forced_forest_diagonal_cegar.json
```

Widths 3--6 are discovery widths and width 7 is held out. Component-profile,
ordered-profile, and canonical ownership-word potentials all satisfy the exact
equality corridors on the discovery widths, with integer potentials, but all
fail when width 7 is added. The strongest counterexample is not merely a lossy
component summary: it joins transitions at an identical concrete
`(forced_mask, partition)` frontier occurring three rows apart. Its projected
cycle has exact weight `-4`. Therefore no potential depending only on the
current exact frontier, boundary mode, and row phase modulo three can certify
even these finite equality sources.

The minimal one-block startup debt also fails at width 7. It separates rows 2
and 5, but the exact equality corridor repeats another identical frontier after
rows 3 and 6, with identical three-row forced-mask history `125,1,1`. Removing
the intervening charge-six production gives another exact projected cycle of
weight `-4`; the JSON contains all of its concrete transitions.

The next and final principled refinement banks that first positive production:

```text
reserve = "terminal" at the bottom boundary,
          min(rows processed, 6) otherwise.
```

This is a bounded width-independent history coordinate with seven active
values. Combined with the pooled component summary, it passes every complete
transition at discovery widths 3--6 and held-out widths 7 and 8. The structural
feature contains row phase, boundary mode, forced count and run count, endpoint
contacts, component count and boundary connection, and the sorted multiset of
canonical component profiles `(active size, interval count, forced contacts,
left contact, right contact, straight orientation)`. It does not retain the raw
mask, canonical partition word, width, or rows remaining. The component-profile
multiset can still grow with width.

Across widths 3--8 the universal and residue-zero systems each have 12,233
pooled feature states and 279,130 strongest constraints. Both have integer
potentials and terminal minima `6,4,7,6,4,2`; hence the phase-zero minima exceed
the stronger endpoint target 4. Deterministic constraint and potential hashes
are recorded in the JSON. This is a concrete bounded-history candidate on
finite complete sources, not a uniform proof for uncomputed widths.

## Additive formula compression

`forced_forest_additive_potential.py` tests whether the exact shortest pooled
potential can be written in the Lean-oriented form

```text
Phi(s) = C[phase,boundary,reserve] + sum_i a_i statistic_i(s),
Phi(out)-Phi(in) <= n+3-3|F_row|.
```

The additive statistics are forced count and runs, endpoint contacts, component
count, sums of active size, interval count, forced contacts and boundary
contacts, and the four straight-orientation multiplicities. The first hinge
basis adds the per-component positive parts for repeated intervals, repeated
forced contacts, and passive span. Exact row reduction gives an immediate
three-state obstruction: at one fixed phase/boundary/reserve category, the
all-unforced width-4 lookup values for one, two, and three passive components
are `9,12,12`, whose second difference is `-3` while every basis statistic has
second difference zero.

This justifies one final hinge `max(component_count-2,0)`. It removes that
obstruction but gives a four-state interaction blocker. With multipliers
`1,-1,-1,1`, all piecewise constants, additive terms, and hinges sum exactly to
zero, while the corresponding lookup potentials satisfy

```text
12 - 9 - 12 + 12 = 3.
```

The four states differ in component count `2,2,3,3` and interval count
`2,3,3,4`. Thus the missing coordinate is an interaction between component
count and repeated-interval excess, not another additive per-component term.
The exact feature vectors and rational multipliers are in
`forced_forest_additive_potential.json`. This blocks exact linear compression
of the canonical shortest lookup potential in the attempted bases. It does not
prove that no other feasible potential exists in those bases, so no algebraic
certificate or theorem is claimed.

The minimal requested interaction was then tested as the equivalent positive
indicator that component surplus and repeated-interval excess are both present,
split by straight orientation. It does not make the canonical shortest lookup
linear. More importantly, direct projection
against all transition and terminal halfspaces did not produce coefficients
whose rationalization survived exact replay. The final indicator basis has 33
terms and 56,576 deduplicated halfspaces. Its recorded rational proposal has an
exact negative minimum slack, so it is rejected.

No exact nonnegative Farkas combination was recovered from the numerical dual
diagnostic. Consequently the direct algebraic feasibility question is marked
**unresolved**, not infeasible. The numerical failure is not a theorem and is
not presented as evidence against the existence of some other feasible
coefficient vector.

Reproduce it with:

```bash
python3 analysis/forced_forest_additive_potential.py \
  --output analysis/forced_forest_additive_potential.json
```
