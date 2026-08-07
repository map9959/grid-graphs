# Silent-hull bounded transition transducer

`certify_silent_hull_symbolic_transition` checks a proposed one-hull
source/action/target row without calling `advance_row`. The source and target
frontiers must have width `3k+2`, valid row-dependent face shape, and one-hull
atom words of the same packet length.

## Cut invariant

After each packet the product retains:

```text
actual ports:   OUT, old boundary, new boundary, optional source carrier
expected ports: OUT, new boundary, optional target carrier
```

The actual DSU is connectivity in the processed row graph. The expected DSU is
connectivity claimed by the decoded target word. Their incidence relation pairs
each emitted actual new face with its claimed target component.

The normalizer rejects an actual component incident with two expected
components: actual connectivity can only merge later, never split. Several
actual components may map to one expected component only while every actual
component reaches a physical cut port and can still merge. A reciprocal
actual/expected pair is forgotten only when neither side reaches the cut. An old
actual component is rejected if it closes without reaching OUT or an emitted
new face, exactly matching sealed-component rejection.

Liveness is closed across the incidence relation before rebuilding the state.
Every retained component is therefore attached to one of four actual or three
expected physical ports. The implementation enforces the width-independent
bounds

```text
live actual components   <= 7,
live expected components <= 7.
```

Silent atoms retain the one active carrier without introducing a local face
occurrence. Counter deltas are local sums, followed by

```text
rank   = new_faces + source_components - target_components,
cycles = horizontal_edges + vertical_edges - rank,
weight = 3*row_U - 2*rank - 1.
```

## Scope

The bounded product proves soundness for every word it accepts. Complete exact
comparisons cover every codec-valid completable edge at `n=5,8`, and every row
of the silent `n=11` control. Malformed interior/terminal face shapes and
irreversible actual-to-target fan-out have dedicated rejection tests.

The remaining theorem is completeness for arbitrary words:

> If `advance_row` accepts an exact row and both exact endpoints have hull width
> at most one, the normalized symbolic product accepts their encodings.

The packet induction is represented directly by the cut invariant above, but
this theorem is not formalized in Lean. More importantly, it does not imply that
an arbitrary action preserves hull width one; that is the separate first-defect
coverage problem.

## Potential obstruction

`residue_two_cut_potential_obstruction.json` proves that a scalar potential on
the bounded cut state cannot certify packets individually. Stable rules 0 and 5
repeat the identical cut state while each dominant packet contributes weight
`-1`, which would require `-1+psi(q)-psi(q)>=0`.

The required object is therefore a weighted frontier-word functional. The
finite `n=5,8` CEGAR experiment records:

```text
atom occurrence sum       exact equality system inconsistent,
adjacent atom bigrams     exactly incompatible with one edge (-3>=0),
finite parser refinement  equality-feasible; inequality feasibility unresolved.
```

These are exact no-go results for the named feature classes, not a universal
impossibility theorem for weighted word potentials.
