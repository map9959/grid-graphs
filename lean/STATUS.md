# Proof Status

This file is the authoritative ledger of what is and isn't formally proven in
the Lean project. Last verified by `lake build` (exit 0) on the current
commit.

A grep over the active `*.lean` sources confirms **zero `sorry` and zero
`admit` tokens in tactic positions** anywhere in the project.

For an annotated walkthrough of every lemma plus an empirical comparison
against ground-truth `P(m,n)` from the Rust DP, see `EVIDENCE.md`.

## Problem

This project analyzes the **full-degree spanning tree problem** on grid
graphs. The grid graph `G(m, n)` has `m × n` vertices in an orthogonal grid,
with edges between vertices that are immediately adjacent horizontally or
vertically. Given a spanning tree `T ⊆ G(m, n)`, a vertex `v` is *full-degree*
(synonymously, *preserved*) if `deg_T(v) = deg_G(v)`. We write `P(m, n)` for
the maximum number of full-degree vertices over all spanning trees of
`G(m, n)`.

The Lean lemmas listed below formalize the algebraic bound *expressions*
`basicUB`, `refinedUB`, `lowerB` and the deficiency identity
`D(m, n) = 2(m-1)(n-1)` that constrain `P(m, n)`. The operational connection
(`P(m, n) ≤ basicUB m n`, an explicit construction reaching `lowerB m n`,
etc.) is in the deferred-work list.

## Proved (sorry-free)

### `GridGraphs/Defs.lean`
- `numEdges_eq`: `numEdges m n = m*(n-1) + n*(m-1)`.
- `succ_mul_succ_sub_one`: `(a+1)*(b+1) - 1 = a*b + a + b`.
- `deficiency_succ_succ`: `deficiency (m+1) (n+1) = 2*m*n`.
- `deficiency_closed_form`: `deficiency m n = 2*(m-1)*(n-1)`.
- `gridGraph`: a real `SimpleGraph (Fin m × Fin n)` with proven `symm` /
  `loopless` fields.

### `GridGraphs/Bounds.lean`
- Definitions of `D`, `I`, `ceilDiv3`, `basicUB`, `refinedUB`, `lowerB` matching
  `docs/DERIVATION.md`.
- `ceilDiv3_mul_ge`, `ceilDiv3_mul_le`, `ceilDiv3_mono`, `ceilDiv3_three_mul`:
  basic algebraic properties of integer ceiling division by 3.
- `D_eq_deficiency`: bridges the algebraic `D` and the operational
  `deficiency` from `Defs.lean`.
- `D_expand`, `D_le_three_mn`: polynomial expansion and a useful upper bound
  for `D` when `m, n ≥ 1`.
- `basicUB_le_mn`, `ceilDiv3_D_le_mn`: range bounds.
- `D_4n`, `basicUB_4n`, `I_4n`, `refinedUB_4n`, `refinedUB_lt_basicUB_4n`:
  closed forms on the `4 × n` family. These match the Rust regression test
  `refined_expected_4xn_pattern`.
- `lowerB_le_basicUB`: `m + n − 1 ≤ basicUB m n` (`m, n ≥ 1`).
- `refinedUB_le_basicUB`: `refinedUB m n ≤ basicUB m n` (`m, n ≥ 1`). Matches
  the Rust assertion in `refined_never_worse_and_valid`.

### `GridGraphs/Forced.lean`
- `forcedEdgeGraph G F`: the graph of all `G`-edges incident to at least one
  vertex of `F`.
- `preservesIncidentEdges G T v`: edge-containment formulation of a vertex being
  full-degree/preserved in `T` relative to `G`.
- `forcedEdgeGraph_le_of_preserves`: if every vertex of `F` preserves all
  incident `G`-edges in `T`, then `forcedEdgeGraph G F ≤ T`.
- `forcedEdgeGraph_isAcyclic_of_preserves`: if `T` is acyclic, then the forced
  graph of any such `F` is acyclic.
- `forcedEdgeGraph_isAcyclic_of_preserves_tree`: same corollary for `T.IsTree`.
- `grid_forcedEdgeGraph_isAcyclic_of_preserves`: grid-graph specialization of
  the acyclicity lemma.

## Not proved (deferred — see notes)

These statements would connect the bound *expressions* in `Bounds.lean` to the
operational quantity `maxPreserved m n` = `P(m, n)`, the maximum number of
full-degree vertices over all spanning trees of `gridGraph m n`. Each
requires building a real spanning-tree predicate and a per-vertex degree
function on the tree:

- Spanning-tree structure: a `Finset (Sym2 (GridVertex m n))` predicate /
  `SimpleGraph.IsSpanningTree` instance for `gridGraph m n`.
- Tree-degree identity: `Σ_v deg_T(v) = 2*(m*n − 1)`.
- Total deficiency in any spanning tree equals `D m n`.
- Per-vertex deficiency cap: `def(v) ≤ deg_G(v) − 1`, i.e. ≤ 3 / 2 / 1 for
  interior / border / corner vertices.
- `preserved_le_basicUB`: for any spanning tree `T`, `numPreserved T ≤ basicUB m n`.
- `preserved_le_refinedUB`: same, with `refinedUB`.
- Cardinality consequence of the forced-edge lemma: `P(m,n)` is bounded above by
  the maximum cardinality of a vertex set whose forced-edge graph is acyclic.
- `lower_bound_construction`: an explicit "double-comb" spanning tree achieving
  `numPreserved ≥ m + n − 1`.
- `verts_partition`: `numCorners + numBorderNonCorner + numInterior = m * n`.

The previous version of this file claimed these were proven; in fact
`Bounds.lean` shipped them with `sorry` against a placeholder
`PreservedCount := 0`. That dishonest scaffolding has been removed.

## Empirical (Rust DP, ground truth)

`cargo test --release` from the repo root runs 5 tests that exhaustively
verify, for `1 ≤ m, n ≤ 9` (and the 4×n family up to `n = 10`), that

```
LB_simple ≤ P(m,n) ≤ refinedUB ≤ basicUB
```

where `P(m,n)` is the exact maximum, computed by the DP in `src/main.rs`.

The full `1 ≤ m, n ≤ 10` table (CSV at `lean/results-empirical.csv`) is
reproduced in `EVIDENCE.md`. All 100 rows respect the bound chain; 19 rows
have `P = refinedUB` (refined bound is tight); the average gap
`basicUB − P` is 2.38.

## Next Steps

1. Define `IsSpanningTree T` and `vertexDegree T v` for a subgraph
   `T : SimpleGraph (GridVertex m n)`.
2. Prove `total_deficiency`: `∑ v, (deg_G v − deg_T v) = D m n` for spanning
   trees `T`. This is the load-bearing identity for both upper bounds.
3. Use `total_deficiency` plus the per-vertex cap to prove
   `preserved_le_basicUB`. Combined with `D_eq_deficiency`,
   `lowerB_le_basicUB`, `refinedUB_le_basicUB` already in this branch, this
   yields the basic sandwich.
4. Construct the double-comb spanning tree as a concrete `Finset` and prove
   it reaches `lowerB`.
