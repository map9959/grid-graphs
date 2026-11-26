import GridGraphs.ResidueTwoUpper.OneGap.SouthCapEastReplay

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan
open ResidueZero L7 BoundarySix.Connected

/-- After 38 seam passes, the depth-two eastern strip empties the
height-20 catalogue at its top plaquette (row 0, column 16). -/
theorem east20_empty : matrixRead (eastResult 20 38 (by decide)) 0 (width 20-2)=[] := by
  native_decide

theorem east20_excludes {u F v q} (H : PhysicalHalo u F v q (fanDirection u v))
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (score : F.card=440+1020*u+588*u^2) (hk : 59≤11+14*u)
    (line : RootLine F v (11+14*u-1) (11+14*u-20))
    (top : ∀ i, 11+14*u-width 20 ≤ i → i < 11+14*u →
      FanSlab.square F v (firstRow (11+14*u) 20) (1+3*i)=73) : False :=
  east_empty_excludes H acy one score hk (by decide) (by decide) line top 38 east20_empty

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan
