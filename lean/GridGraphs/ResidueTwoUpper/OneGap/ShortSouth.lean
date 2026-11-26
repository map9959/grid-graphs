import GridGraphs.ResidueTwoUpper.OneGap.ShortNorthRoot
import GridGraphs.ResidueTwoUpper.OneGap.ShortSchedule
import GridGraphs.ResidueTwoUpper.OneGap.FanSpeedTail

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short
open ResidueZero L7 FanBoot BoundarySix.Connected

/-- Conditional physical reduction of the short branch. The remaining
local input is `DeepAfter`, not merely price/tag transport. -/
theorem short_south {u q : Nat} (hu : 19≤u) (short : q<57)
    {F : Finset (GridVertex (35+42*u) (35+42*u))} {P w} (S : Seed F P w q)
    (acy : (Bonds F).IsAcyclic) (score : F.card=440+1020*u+588*u^2)
    (one : (perimeterHoles F).card=1) (deep : DeepAfter F w 4) :
    SouthEnd F w q := by
  obtain ⟨Q⟩ := flow_of_score u F acy score one
  have front := North.front S acy (by omega)
  have z := follow u q S.room F acy w P S.step S.clean
    (by simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using S.zero)
    Q 4 deep _ (short_seed_schedule u q hu short)
  dsimp only at z
  rw [show 11+14*u-(11+14*u-4)=4 by omega] at z
  exact z (by omega) (by omega) (by omega) (by omega) (by omega) front

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short
