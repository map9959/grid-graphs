import GridGraphs.Constructions.ResidueTwo.LowerTurnBase23Cover

namespace GridGraphs.ResidueTwoLower.Poly

/-- All three ways to continue are checked in all four directions at
the terminal layer and for an unbounded width parameter. -/
theorem terminal23 : layerOK input23 10 = true := by native_decide

end GridGraphs.ResidueTwoLower.Poly
