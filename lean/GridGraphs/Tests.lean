import GridGraphs.Defs
import GridGraphs.Bounds
import GridGraphs.ResidueOne

/-!
# Decidable sanity tests linking Lean definitions to Rust DP ground truth

This file is a small regression suite consisting of `example`s that the
kernel checks via `decide` (or `rfl`/`Finset.card` evaluation). It pins the
Lean definitions of `D`, `basicUB`, `refinedUB`, `lowerB`, the vertex-class
counts, and the residue-1 cardinality to specific small-grid values that
match the Rust DP empirical data in `lean/results-empirical.csv`.

A regression in any of the bound expressions or vertex counts will break
these `example`s and therefore break `lake build`.
-/

namespace GridGraphs

/-! ## Vertex-class partition spot checks (matching `verts_partition`) -/

example : numCorners 5 5 + numBorderNonCorner 5 5 + numInterior 5 5 = 5 * 5 := by
  decide

example : numCorners 1 1 + numBorderNonCorner 1 1 + numInterior 1 1 = 1 := by
  decide

example : numCorners 3 4 + numBorderNonCorner 3 4 + numInterior 3 4 = 12 := by
  decide

example : numCorners 7 1 + numBorderNonCorner 7 1 + numInterior 7 1 = 7 := by
  decide

/-! ## Total deficiency `D m n = 2 (m-1)(n-1)` -/

example : D 1 1 = 0 := by decide
example : D 4 5 = 24 := by decide
example : D 10 10 = 162 := by decide
example : D 3 3 = 8 := by decide

/-! ## Basic upper bound -/

example : basicUB 1 10 = 10 := by decide
example : basicUB 4 1 = 4 := by decide
example : basicUB 3 3 = 6 := by decide
example : basicUB 4 5 = 12 := by decide
example : basicUB 4 10 = 22 := by decide
example : basicUB 5 5 = 14 := by decide
example : basicUB 10 10 = 46 := by decide

/-! ## Refined upper bound -/

example : refinedUB 1 10 = 10 := by decide
example : refinedUB 4 1 = 4 := by decide
example : refinedUB 3 3 = 5 := by decide
example : refinedUB 4 5 = 11 := by decide
example : refinedUB 4 10 = 21 := by decide
example : refinedUB 5 5 = 13 := by decide
example : refinedUB 10 10 = 46 := by decide

/-! ## Conservative lower bound `m + n − 1` -/

example : lowerB 5 5 = 9 := by decide
example : lowerB 4 10 = 13 := by decide
example : lowerB 10 10 = 19 := by decide

/-! ## Residue-1 diagonal `U` cardinalities -/

-- For k = 1 (n = 4): |uResidueOne 1| = 6 + 1 + 1 = 8.
example : (uResidueOne 1).card = 8 := by
  rw [uResidueOne_card 1 (by decide)]; decide

-- For k = 2 (n = 7): |uResidueOne 2| = 24 + 2 + 1 = 27.
example : (uResidueOne 2).card = 27 := by
  rw [uResidueOne_card 2 (by decide)]; decide

-- For k = 3 (n = 10): |uResidueOne 3| = 54 + 3 + 1 = 58.
example : (uResidueOne 3).card = 58 := by
  rw [uResidueOne_card 3 (by decide)]; decide

-- The conjectured `q (3k+1)` matches the empirical residue-1 sequence
-- 8, 27, 58, 101, ... = `q 4, q 7, q 10, q 13, ...`.
example : q 4 = 8 := by decide
example : q 7 = 27 := by decide
example : q 10 = 58 := by decide
example : q 13 = 101 := by decide

end GridGraphs
