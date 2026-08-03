# Proof-oriented run/rank prototype

This prototype records algebraic identities and exact finite certificate
semantics. It does not prove the final counting theorem, and a valid frontier
certificate says nothing about transitions omitted from its declared finite
scope.

## Generic identities

Let `U` be any subset of the vertices of an `m x n` grid. Let `Rr` and `Rc`
be the numbers of maximal nonempty U-runs in rows and columns, and put
`R = Rr + Rc`. Let the dual multigraph contain all
`F = (m-1)(n-1)+1` faces, including `OUT`, and one dual edge for each primal
U-U edge. Loops and parallel boundary edges are retained. Write `E` for its
edge count, `C` for its component count, `rho` for graphic rank, and `beta` for
cycle rank. Then

```text
E          = 2|U| - R
rho        = F - C
beta       = E - rho = E - F + C
rho + beta = E
R + beta   = 2|U| - F + C
C - 1      = R + beta - (2|U| - F + 1)
3|U|-2rho  = 2R + 2beta - |U|.
```

The first identity sums `k-r` adjacencies over every line containing `k` U
vertices in `r` runs. The remaining identities are the standard graphic-matroid
rank and nullity formulas, including isolated dual vertices.

For `m=n=17` and `|U|=178`, `F=257` and
`2|U|-F+1=100`. Thus, with `delta=C-1`, every 178-U pattern satisfies exactly

```text
delta = R + beta - 100.
```

In particular, dual connectivity is equivalent to `delta=0`, not merely to an
edge-count bound. `proof_oriented_identities.py pattern FILE --n17-178` checks
the specialization for a supplied pattern; `check_pattern_identities` checks
all displayed generic identities.

## Certificate semantics

Schema `grid-graphs.frontier-inequality.v1` contains a finite list of states,
exact reduced rational potentials `[numerator, denominator]`, and a finite list
of transitions. Every transition has integer `dU`, `dRank`, and `charge`. The
checker accepts exactly when every listed transition satisfies, using
`fractions.Fraction` arithmetic,

```text
3*dU - 2*dRank >= Phi(out) - Phi(in) + charge.
```

State and transition identifiers must be unique and all references must
resolve. Negative U/rank increments and noncanonical rationals are rejected.
The mandatory scope value `enumerated-transitions-only` prevents interpreting
the checker as a coverage proof. `complete_for_source` is metadata; the checker
does not infer or certify source completeness.

`frontier_inequality_demo_certificate.json` gives two genuine `2x2` all-U row
transition deltas. It includes a half-integral potential and one tight
inequality. Verify it with:

```bash
python3 analysis/proof_oriented_identities.py demo
```

## Feeding `tile_grammar`

For an accepted row or band transition, retain its incoming and outgoing
`FrontierState` and the exact emitted row masks. The adapter
`tile_grammar_transition_record` computes

```text
dEdges  = new horizontal U-U edges + new vertical U-U edges
dCycles = outgoing.cycle_excess - incoming.cycle_excess
dRank   = dEdges - dCycles
```

This works because `tile_grammar` increments `cycle_excess` exactly when a dual
edge joins vertices already connected. A state ID used for potential synthesis
should encode the chosen finite quotient, normally row phase, previous U mask,
and canonical frontier partition; cumulative U cost and cycle count belong to
transition deltas unless the proposed quotient needs them. Row-packet charge or
another proposed local charge can be passed unchanged as `charge`.

## Proof boundary

Before using a finite certificate in a theorem, one must separately prove that
its quotient and transition set cover every admissible extension and prove the
initial/terminal potential and total-charge bounds that make the inequalities
telescopic. The complete sources below deliberately establish neither claim
beyond each declared `nxn` operational transition system.

## Complete small source and synthesis

`export_complete_tile_row_source(n, 0)` declares one complete finite source:
the reachable `nxn` row-transition quotient keyed by
`(row_index, previous_u_mask, partition)`. From every reachable nonterminal
quotient state it passes each of the `2^n` masks to
`tile_grammar.advance_row`; a non-`None` result is an accepted transition and a
`None` result is counted as rejected. This is completeness only for this
operational quotient source at that declared `n`, not for larger grids, another
transition alphabet, or a theorem-level class of patterns. The CLI currently
allows complete sources for `2 <= n <= 6`.

The exact `n=3` census is:

```text
reachable states by row: 1, 8, 14, 8
mask attempts:           184
accepted transitions:     84
rejected attempts:        100
total quotient states:     31
```

`synthesize_difference_potentials` treats each transition as the exact
difference constraint

```text
Phi(out) <= Phi(in) + 3*dU - 2*dRank - charge.
```

It runs Bellman-Ford from an implicit zero-distance super-source to detect a
negative cycle, then computes exact `Fraction` shortest distances from the
declared initial state. A negative cycle raises `InfeasiblePotentialError`.
`build_complete_tile_certificate` attaches the reduced rational potentials and
checks every inequality. `reverify_complete_tile_certificate` separately
regenerates the complete declared source and synthesized certificate, requires
exact structural equality, and reruns the independent inequality checker.

Emit and immediately reverify the default source with:

```bash
python3 analysis/proof_oriented_identities.py export-small \
  --n 3 --output /tmp/opencode/grid-graphs-n3-certificate.json
```

For zero charge, the complete synthesis results through `n=6` are:

```text
n  states  transitions  tight  terminal Phi range  rank  implied |U|
2       9           13      8                 4..4     1            2
3      31           84     50                7..10     4            5
4     106          504    162                6..12     9            8
5     369         2966    690               10..13    16           14
6    1264        16381   3058               10..19    25           20
```

Writing the desired connected-grid bound as

```text
B(n) = 3*q(n) - 2*(n-1)^2,
```

the synthesized minimum terminal potentials are exactly `B(n)` through this
range. The closed forms for `q` give `B(n+3)=B(n)+3`; the observed values are
`7,6,10,10` for `n=3,4,5,6`. This period-three scalar recurrence is the target
for a uniform quotient proof, but matching it at finitely many widths is not
such a proof.

At `n=3`, 50 of 84 transitions are tight, split `8,19,23` by destination row.
Every accepted final state is dual-connected and therefore has graphic rank 4,
so telescoping gives

```text
3|U| - 2*4 >= 7,
|U| >= 5.
```

The bounds are positive and sharp inside each finite source, reproducing the
known minima `5,8,14,20` for `n=3,4,5,6`. They remain shortest-path
restatements of complete small dynamic programs, not yet a scalable potential
or evidence that zero charge supplies the required global strip-counting bound.
Each generated certificate also contains `tight_witness_rows`, one
deterministically selected all-tight path from the initial state to a
minimum-potential terminal state; tests independently check its U count and
dual connectivity.
The next synthesis experiment is to choose a state-local charge with
theorem-relevant total charge, rerun the same negative-cycle test, and seek a
finite quotient and terminal-potential bound that are uniform in `n`.
