import GridGraphs.ResidueZero.Stencil

namespace GridGraphs.ResidueZero

theorem starChecks : starCheck 12 && starCheck 15 && starCheck 18 && starCheck 21 := by
  native_decide

theorem patchChecks : patchCheck 12 && patchCheck 15 && patchCheck 18 && patchCheck 21 := by
  native_decide

end GridGraphs.ResidueZero
