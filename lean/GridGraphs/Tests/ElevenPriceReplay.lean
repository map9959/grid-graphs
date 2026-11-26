import GridGraphs.Results.SmallDiagonalExact.Eleven.Assembly

/-! Replay the side-eleven integer prices on allowed stars and 3×3 masks. -/
namespace GridGraphs.Eleven

theorem checkedStars : twoStarCheck 11 := by native_decide
theorem checkedPatches : twoPatchCheck 11 := by native_decide
theorem checkedBudget : rhs 11 = 4922020 := by native_decide

end GridGraphs.Eleven
