import GridGraphs.ResidueTwoUpper.OneGap.SouthCapEastReplay

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan
open ResidueZero L7 BoundarySix.Connected

/-- Twenty-five seam passes followed by the eastern depth-two strip
eliminate the top plaquette at column 12 on the height-15 cap. -/
theorem east15_empty : matrixRead (eastResult 15 25 (by decide)) 0 (width 15-2)=[] := by
  native_decide

theorem east15_excludes {u F v q} (H : PhysicalHalo u F v q (fanDirection u v))
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (score : F.card=440+1020*u+588*u^2) (hk : 59≤11+14*u)
    (line : RootLine F v (11+14*u-1) (11+14*u-15))
    (top : ∀ i, 11+14*u-width 15 ≤ i → i < 11+14*u →
      FanSlab.square F v (firstRow (11+14*u) 15) (1+3*i)=73) : False :=
  east_empty_excludes H acy one score hk (by decide) (by decide) line top 25 east15_empty

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan
