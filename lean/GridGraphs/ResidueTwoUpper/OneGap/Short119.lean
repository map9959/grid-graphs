import GridGraphs.ResidueTwoUpper.OneGap.ShortGrouped

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short
open L7 ResidueZero BoundarySix.Connected

@[noinline] def sites119 (a : Board) :=
  decide (∀ (i : Fin 4) (w : View), groupTest 117 119 (10*i.val+1) (min 37 (10*i.val+9)) w a)
theorem replay119 : sites119 (cached 2 chart) := by
  native_decide

/-- Four interval unions cover all 19 indices on the third exceptional side. -/
theorem exclude119 (F : Finset (GridVertex 119 119)) (acy : (Bonds F).IsAcyclic)
    (one : (perimeterHoles F).card=1) : F.card≠4832 := by
  intro score
  obtain ⟨P,w,q,S⟩ := seed_from_score 2 F acy (by norm_num; exact score) one
  have odd := S.odd; have bound := S.room
  let i : Fin 4 := ⟨q/10,by omega⟩
  exact group_excludes 2 q _ _ w (of_decide_eq_true replay119 i w) S acy
    (by dsimp [i]; omega) (by dsimp [i]; omega)
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short
