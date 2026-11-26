import GridGraphs.ResidueTwoUpper.OneGap.SouthCapEastReplay

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan
open ResidueZero L7 BoundarySix.Connected

/-- After 36 seam passes, the depth-two eastern strip empties the
height-19 catalogue at its top plaquette (row 0, column 15). -/
theorem east19_empty : matrixRead (eastResult 19 36 (by decide)) 0 (width 19-2)=[] := by
  native_decide

theorem east19_excludes {u F v q} (H : PhysicalHalo u F v q (fanDirection u v))
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (score : F.card=440+1020*u+588*u^2) (hk : 59≤11+14*u)
    (line : RootLine F v (11+14*u-1) (11+14*u-19))
    (top : ∀ i, 11+14*u-width 19 ≤ i → i < 11+14*u →
      FanSlab.square F v (firstRow (11+14*u) 19) (1+3*i)=73) : False :=
  east_empty_excludes H acy one score hk (by decide) (by decide) line top 36 east19_empty

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan
