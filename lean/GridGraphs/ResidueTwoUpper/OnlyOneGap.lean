import GridGraphs.ResidueTwoUpper.Opposite0101.Exclusion
import GridGraphs.ResidueTwoUpper.TwoGapFrontierExclusion

namespace GridGraphs.ResidueTwoUpper.Exceptional
open ResidueZero Stencil BoundarySix.Connected

theorem one_gap_of_exceptional_score {u : Nat} (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2) :
    (perimeterHoles F).card=1 := by
  obtain ⟨_,_,_,_,_,_,_,one|two⟩ := Frame.frame_of_score u F acy score
  · exact one.1
  · obtain ⟨M,a,s,t,w⟩ := Opposite0101.adjacent_witness F acy score two.1
    exact (TwoGap.ExitReplay.physical_0011_impossible M a s t w).elim

end GridGraphs.ResidueTwoUpper.Exceptional
