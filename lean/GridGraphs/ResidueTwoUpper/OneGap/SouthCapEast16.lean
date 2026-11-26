import GridGraphs.ResidueTwoUpper.OneGap.SouthCapEastReplay

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan
open ResidueZero L7 BoundarySix.Connected

/-- Thirty seam passes followed by the depth-two eastern strip empty
the top plaquette at column 13 of the height-16 catalogue. -/
theorem east16_empty : matrixRead (eastResult 16 30 (by decide)) 0 (width 16-2)=[] := by
  native_decide

theorem east16_excludes {u F v q} (H : PhysicalHalo u F v q (fanDirection u v))
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (score : F.card=440+1020*u+588*u^2) (hk : 59≤11+14*u)
    (line : RootLine F v (11+14*u-1) (11+14*u-16))
    (top : ∀ i, 11+14*u-width 16 ≤ i → i < 11+14*u →
      FanSlab.square F v (firstRow (11+14*u) 16) (1+3*i)=73) : False :=
  east_empty_excludes H acy one score hk (by decide) (by decide) line top 30 east16_empty

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan
