import GridGraphs.FiniteOne.Cuts43

namespace GridGraphs.FiniteOne
open ResidueZero Cuts43

private def tLL := decode 43 (include_str "Data/s43LL.v32")
private def tLH := decode 43 (include_str "Data/s43LH.v32")
private def tH := decode 43 (include_str "Data/s43H.v32")
private def passes (T : Prices) (cs : List Cut) :=
  decide (pricedBudget T 43 (charges 43 cs)+allowance cs < (T.unit:Int)*661)
private theorem llCheck : passes tLL ll := by native_decide
private theorem lhCheck : passes tLH lh := by native_decide
private theorem hiCheck : passes tH hi := by native_decide

theorem exact43 : maxPreserved 43 43=660 := by
  apply Nat.le_antisymm _ (squareScore_lower_residue_one 14)
  obtain ⟨F,m,sc⟩ := (squareMaskScore_iff_le (n:=43) (by decide)).mpr (le_refl (maxPreserved 43 43))
  rw [←sc]
  have acy := mem_acyclicForcedSets.mp m
  by_cases a : occ F (6,9)≤7
  · by_cases b : occ F (9,15)≤7
    · apply cut_bound (by decide) tLL F acy ll _ (of_decide_eq_true llCheck)
      intro c hc; simp only [ll,List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl|rfl <;> unfold Cut.holds <;> dsimp only <;> omega
    · apply cut_bound (by decide) tLH F acy lh _ (of_decide_eq_true lhCheck)
      intro c hc; simp only [lh,List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl|rfl <;> unfold Cut.holds <;> dsimp only <;> omega
  · apply cut_bound (by decide) tH F acy hi _ (of_decide_eq_true hiCheck)
    intro c hc; simp only [hi,List.mem_singleton] at hc
    subst c; unfold Cut.holds; dsimp only; omega
end GridGraphs.FiniteOne
