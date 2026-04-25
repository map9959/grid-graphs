# Lean Formalization: Grid Graph Preservation Bounds

A Lean 4 + mathlib project formalizing combinatorial identities and bound
expressions from `docs/DERIVATION.md` for the m×n grid graph.

## Problem

The **grid graph** `G(m, n)` has `m × n` vertices arranged in a rectangular
grid; each vertex is adjacent to the (up to four) vertices immediately above,
below, left, and right of it. A **spanning tree** `T` of `G(m, n)` is a
connected acyclic subgraph that contains every vertex. A vertex `v` is
**full-degree in `T`** if `deg_T(v) = deg_G(v)` — equivalently, every edge of
`G` incident to `v` is retained in `T`.

The problem this project analyzes is:

> Find a spanning tree `T` of `G(m, n)` that maximizes the number of
> full-degree vertices, and/or determine that maximum.

Write `P(m, n)` for that maximum. The Rust DP in `../src/main.rs` computes
`P(m, n)` exactly for moderate `m, n`; the Lean code formalizes algebraic
identities and bound expressions (basic and refined upper bounds, conservative
lower bound) that constrain `P(m, n)`.

In this codebase a "full-degree" vertex is also called "preserved", following
the terminology in `docs/DERIVATION.md`; the two terms are interchangeable.

## Contents

- `GridGraphs/Defs.lean`: Vertex/edge counts, deficiency, and the simple graph
  `gridGraph m n` itself (a real `SimpleGraph (Fin m × Fin n)` with proven
  `symm` and `loopless`).
- `GridGraphs/Bounds.lean`: Algebraic bound expressions `D`, `I`, `ceilDiv3`,
  `basicUB`, `refinedUB`, `lowerB`, and their `sorry`-free properties.
- `GridGraphs/Packing.lean`: Currently empty (placeholder).
- `GridGraphs.lean`: Aggregate import.
- `STATUS.md`: Detailed proof-status ledger.
- `EVIDENCE.md`: Annotated lemma index plus empirical comparison against
  ground-truth `P(m,n)` from the Rust DP for all `1 ≤ m, n ≤ 10`.
- `results-empirical.csv`: Regenerated Rust output backing `EVIDENCE.md`.

## Headline Proven Lemmas (zero `sorry`)

- `deficiency_closed_form`: `deficiency m n = 2 * (m-1) * (n-1)`.
- `D_eq_deficiency`: the algebraic `D` matches the operational `deficiency`.
- `basicUB_4n` / `refinedUB_4n`: closed forms `2n+2` / `2n+1` for the 4×n
  family, matching the Rust regression test `refined_expected_4xn_pattern`.
- `refinedUB_le_basicUB`: the refined bound never exceeds the basic bound.
- `lowerB_le_basicUB`: the conservative lower bound never exceeds the basic
  upper bound (sanity of the bound chain).

See `STATUS.md` for the full list and `EVIDENCE.md` for line-numbered
references plus empirical evidence.

## Deferred (not yet proven in Lean)

The connection of `basicUB` / `refinedUB` / `lowerB` to the operational
maximum `P(m,n)` (the maximum number of full-degree vertices over all
spanning trees of `G(m, n)`) is
**not** in this branch. It requires defining `IsSpanningTree` and a tree-side
degree function on `gridGraph m n`. Empirically, ground-truth `P(m,n)` from
the Rust DP satisfies the bound chain for all `1 ≤ m, n ≤ 9` (verified by
`cargo test --release`).

## Build Instructions

```bash
cd lean
lake update     # fetch mathlib (already pinned in lake-manifest.json)
lake build      # build the project; should print "Build completed successfully"
```

To open in VS Code, open the `lean/` folder with the Lean 4 extension.

## Sorry-free Verification

```bash
grep -rE '^\s*(sorry|admit)\s*$|by sorry|by admit|:= sorry|:= admit' \
  GridGraphs/ GridGraphs.lean
# Expected output: nothing.
```
