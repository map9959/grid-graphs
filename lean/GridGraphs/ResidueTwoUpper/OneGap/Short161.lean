import GridGraphs.ResidueTwoUpper.OneGap.ShortGrouped

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short
open L7 ResidueZero BoundarySix.Connected

@[noinline] def sites161 (a : Board) :=
  decide (∀ (i : Fin 6) (w : View), groupTest 159 161 (10*i.val+1) (min 51 (10*i.val+9)) w a)

/-- Soundness of the proposed side-161 replay. The six-interval replay
does not pass, so this is not an unconditional exclusion. -/
theorem exclude161_of_replay (ok : sites161 (cached 3 chart))
    (F : Finset (GridVertex 161 161)) (acy : (Bonds F).IsAcyclic)
    (one : (perimeterHoles F).card=1) : F.card≠8792 := by
  intro score
  obtain ⟨P,w,q,S⟩ := seed_from_score 3 F acy (by norm_num; exact score) one
  have odd := S.odd; have bound := S.room
  let i : Fin 6 := ⟨q/10,by omega⟩
  exact group_excludes 3 q _ _ w (of_decide_eq_true ok i w) S acy
    (by dsimp [i]; omega) (by dsimp [i]; omega)
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.Short
