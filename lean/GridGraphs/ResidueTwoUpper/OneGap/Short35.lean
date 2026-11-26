import GridGraphs.ResidueTwoUpper.OneGap.ShortPhysical
import GridGraphs.ResidueTwoUpper.OneGap.Short35Replay

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short
open ResidueZero BoundarySix.Connected

/-- On the first exceptional square every possible odd index is short.
No one-gap forest on this square attains the exceptional score. -/
theorem exclude35 (F : Finset (GridVertex 35 35)) (acy : (Bonds F).IsAcyclic)
    (one : (perimeterHoles F).card=1) : F.card≠440 := by
  intro score
  obtain ⟨P,w,q,S⟩ := seed_from_score 0 F acy (by simpa using score) one
  have odd := S.odd
  have bound := S.room
  let i : Fin 5 := ⟨q/2,by omega⟩
  have check := of_decide_eq_true replay35 i w
  rw [show 2*i.val+1=q by dsimp [i]; omega] at check
  exact reject_sound check (actual_agree F P S.step S.owners) (kept_physical S acy)
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short
