import GridGraphs.ResidueTwoUpper.OneGap.SouthCapCatalogueDecode
import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStripReplayFlags

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
open ResidueZero L7 BoundarySix.Connected
namespace GridScan

/-- Every concrete replay update preserves the physical cap. The
catalogue premise and the strip trace premises are both discharged. -/
theorem scored_cap_survives_replay {u h F v q} (H : PhysicalHalo u F v q (fanDirection u v))
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (score : F.card=440+1020*u+588*u^2) (hk : 59≤11+14*u)
    (lo : 14≤h) (hi : h≤43)
    (line : RootLine F v (11+14*u-1) (11+14*u-h))
    (top : ∀ i, 11+14*u-width h ≤ i → i < 11+14*u →
      FanSlab.square F v (firstRow (11+14*u) h) (1+3*i)=73)
    (zs : List (Update h)) :
    Admitted h (width h) (replayCap zs (initialDomains h)) (cropTiles F v (11+14*u) h) := by
  have room : width h≤11+14*u := by unfold width; omega
  rw [←prune_replay_eq F v room]
  exact physical_cap_survives H acy one score hk lo hi line top
    (physical_catalogue_admitted H acy score hk hi) zs

end GridScan
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
