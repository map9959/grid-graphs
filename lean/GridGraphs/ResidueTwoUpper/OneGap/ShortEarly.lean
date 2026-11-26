import GridGraphs.ResidueTwoUpper.OneGap.Short35
import GridGraphs.ResidueTwoUpper.OneGap.Short77
import GridGraphs.ResidueTwoUpper.OneGap.Short119

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short
open ResidueZero BoundarySix.Connected

/-- On the first three exceptional sides all allowable isolate indices
are short. The three owner scans exclude the entire one-gap case. -/
theorem exclude_early (u : Nat) (hu : u≤2)
    (F : Finset (GridVertex (35+42*u) (35+42*u))) (acy : (Bonds F).IsAcyclic)
    (one : (perimeterHoles F).card=1) : F.card≠440+1020*u+588*u^2 := by
  interval_cases u
  · exact exclude35 F acy one
  · exact exclude77 F acy one
  · exact exclude119 F acy one
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short
