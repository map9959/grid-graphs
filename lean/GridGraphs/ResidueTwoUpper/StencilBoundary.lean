import GridGraphs.ResidueTwoUpper.StencilUpper

/-! The same unrestricted prices also apply before the periodic transport
base. These are direct local stencil replays, not searches for trees. -/
namespace GridGraphs.ResidueTwoUpper.Stencil
open GridGraphs.ResidueZero hiding scale

private theorem earlyStars : twoStarCheck 14 && twoStarCheck 17 := by native_decide
private theorem earlyPatches : twoPatchCheck 14 && twoPatchCheck 17 := by native_decide

private theorem early_upper (n m : Nat) (hn : 12≤n) (s : twoStarCheck n) (p : twoPatchCheck n)
    (budget : rhs n < scale*((m:Int)+1)) : maxPreserved n n ≤ m := by
  obtain ⟨F,hF,num⟩ := (squareMaskScore_iff_le (n:=n) (by omega)).mpr (le_refl (maxPreserved n n))
  have h := physical_budget hn F (mem_acyclicForcedSets.mp hF)
    (fun _ _ _ _ hp hf hn ho ok => fromStar s hp hf hn ho ok)
    (fun _ _ hp hm ok => fromPatch p hp hm ok)
  have bound := lt_of_le_of_lt h budget
  have le : (F.card:Int)<(m:Int)+1 := lt_of_mul_lt_mul_left bound (by decide : 0 ≤ scale)
  omega

theorem fourteen_exact : maxPreserved 14 14=77 := by
  have s := earlyStars; have p := earlyPatches; simp only [Bool.and_eq_true] at s p
  exact le_antisymm (early_upper 14 77 (by decide) s.1 p.1 (by native_decide))
    seventySeven_le_maxPreserved_fourteen_fourteen

theorem seventeen_exact : maxPreserved 17 17=110 := by
  have s := earlyStars; have p := earlyPatches; simp only [Bool.and_eq_true] at s p
  exact le_antisymm (early_upper 17 110 (by decide) s.2 p.2 (by native_decide))
    oneHundredTen_le_maxPreserved_seventeen_seventeen

end GridGraphs.ResidueTwoUpper.Stencil
