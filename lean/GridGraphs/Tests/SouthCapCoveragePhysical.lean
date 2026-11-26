import GridGraphs.Tests.SouthCapCoverageAll
import GridGraphs.ResidueTwoUpper.OneGap.SouthCapPhysicalStar

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
open ResidueZero

/-- Both corner patterns, in every physical halo window. The remaining
catalogue interface is to decode these 36 matched bits as tile masks. -/
theorem all_physical_windows_bits {u k h w r c F v q} (pl : Placement u k h w r c)
    (H : PhysicalHalo u F v q (fanDirection u v))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2) :
    ∃ m∈allowedWords (endTag h r) (endTag w c), ∀ z∈fourVars.zipIdx,
      numericField (windowField pl H) z.1=m.testBit z.2 := by
  have x := tag_range pl.row
  have y := tag_range pl.col
  let i : Fin 7 := ⟨endTag h r-6,by omega⟩
  let j : Fin 7 := ⟨endTag w c-6,by omega⟩
  have I : 6+i.val=endTag h r := by dsimp [i]; omega
  have J : 6+j.val=endTag w c := by dsimp [j]; omega
  have clauses := scored_halo_clauses pl H acy score
  have adm := all_windows_coverage i j H.cornerBit (numericField (windowField pl H))
    (by simpa only [I,J] using clauses)
  simpa only [I,J] using adm

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
