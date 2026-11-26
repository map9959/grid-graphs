# Lean proof program for `P(n,n)`

The target is `GridGraphs.ExactSquareFormula`, with `P(n,n)` interpreted as
`maxPreserved n n`. The reference answer, exceptions and mathematical
certificates are in [the exact square formula](EXACT_SQUARE_FORMULA.md).
The task is to certify those arguments, not to infer the formula from more
values.

[`exactSquareFormula_of_remaining_bounds`](../lean/GridGraphs/Results/SquareFormulaAssembly.lean)
is the integration point. It dispatches on `n % 3`, uses the existing
unconditional residue-zero equality and residue-one lower bound, handles the already certified
small sides, and uses the all-width residue-one equality and residue-two lower bound. Its sole remaining input is:

| Input | Physical proof to deliver |
|---|---|
| Exceptional residue-two upper | For every `u≥0`, exclude a feasible mask of size `440+1020u+588u²` on side `35+42u`. The all-width stencil closes the upper bound on the other tail sides. |

The residue-one geometry and width transport can proceed independently:
prove the retained matrix rows for the physical vector, and separately
transport chart coverage, objective and polynomial right sides to every
tail width. A finite replay at sides 58 and 61 is not width transport.
Likewise, a theorem about an arbitrary *feasible vector* is not yet an
upper bound on trees.

**Integration check.** Build each branch's Lean target, inspect its exact
type and `#print axioms`, and pass its theorem to the assembly lemma.
The endpoint is a declaration of type `ExactSquareFormula` with **no**
remaining proof arguments. Closed `native_decide` replays belong in test
modules and must be reported in the axiom audit.

**Certificate footprint.** Prefer uniform proofs and small, independently
checked certificates. Keep solver scratch files and exploratory traces out
of version control. For each new replay, report the bytes a clean checkout
needs, including any required downloads. A generator is sufficient only
if Lean checks its output; rerunning a solver and trusting its answer is
not a proof. If a branch appears to need a large irreducible proof artifact,
report its size and the alternatives before proposing it for inclusion.
