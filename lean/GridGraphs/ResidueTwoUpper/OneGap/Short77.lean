import GridGraphs.ResidueTwoUpper.OneGap.ShortKernelProof

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short
open L7 ResidueZero BoundarySix.Connected

@[noinline] def sites77 (a : Board) :=
  decide (∀ (i : Fin 12) (w : View), pairTest 75 77 (2*i.val+1) w a)
theorem replay77 : sites77 (cached 1 chart) := by native_decide

theorem exclude77 (F : Finset (GridVertex 77 77)) (acy : (Bonds F).IsAcyclic)
    (one : (perimeterHoles F).card=1) : F.card≠2048 := by
  intro score
  obtain ⟨P,w,q,S⟩ := seed_from_score 1 F acy (by norm_num; exact score) one
  have odd := S.odd
  have bound := S.room
  let i : Fin 12 := ⟨q/2,by omega⟩
  have check := of_decide_eq_true replay77 i w
  rw [show 2*i.val+1=q by dsimp [i]; omega] at check
  exact test_excludes 1 q w check S acy
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short
