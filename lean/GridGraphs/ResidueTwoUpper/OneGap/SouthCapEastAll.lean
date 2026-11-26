import GridGraphs.ResidueTwoUpper.OneGap.SouthCapEastRange

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan
open ResidueZero L7 BoundarySix.Connected

/-- One finite replay for heights 21 through 43 inclusive. -/
theorem eastBatch_empty : ∀ i : Fin 23, eastBatchCell i=[] := by native_decide

theorem eastRange_empty (h : Nat) (lo : 14≤h) (hi : h≤43) :
    ∃ rounds, matrixRead (eastResult h rounds lo) 0 (width h-2)=[] :=
  eastRange_empty_of_batch eastBatch_empty h lo hi

theorem southEnd_excluded {u F v q} (H : PhysicalHalo u F v q (fanDirection u v))
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (score : F.card=440+1020*u+588*u^2) (big : 57≤q) (fit : q+2≤11+14*u) :
    ¬SouthEnd F v q :=
  southEnd_excluded_of_east_batch eastBatch_empty H acy one score big fit

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan
