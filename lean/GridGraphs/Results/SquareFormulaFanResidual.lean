import GridGraphs.Results.SquareFormulaAssembly
import GridGraphs.ResidueTwoUpper.OnlyOneGap
import GridGraphs.ResidueTwoUpper.OneGap.ShortEarly
import GridGraphs.ResidueTwoUpper.OneGap.ScoredFanFailure

namespace GridGraphs
open ResidueZero ResidueTwoUpper.Exceptional ResidueTwoUpper.Exceptional.OneGap
open FanBoot.SouthCap BoundarySix.Connected

/-- The remaining premise is about specific local failures, not the
whole-square maximum or a hypothetical cap solver. All physical
quantities refer to the same board, orientation and seed. -/
theorem exactSquareFormula_of_no_fan_failure
    (exclude : ∀ (u : Nat), 3≤u → ∀ (F : Finset (Site u)), (Bonds F).IsAcyclic →
      F.card=440+1020*u+588*u^2 → (perimeterHoles F).card=1 →
      ∀ P w q, Short.Seed F P w q → ¬FanFailure F w q) : ExactSquareFormula := by
  apply exactSquareFormula_of_remaining_bounds
  intro u
  rintro ⟨F,hF,score⟩
  have acy := mem_acyclicForcedSets.mp hF
  have one := one_gap_of_exceptional_score F acy score
  by_cases early : u≤2
  · exact Short.exclude_early u early F acy one score
  obtain ⟨P,w,q,S,fail⟩ := failure_from_score (by omega) acy score one
  exact exclude u (by omega) F acy score one P w q S fail

/-- Only the listed same-board fan indices can still obstruct the
physical spanning-tree formula. -/
theorem exactSquareFormula_of_pending_fans
    (exclude : ∀ u q, (u,q)∈pendingFanIndices → ∀ (F : Finset (Site u)), (Bonds F).IsAcyclic →
      F.card=440+1020*u+588*u^2 → (perimeterHoles F).card=1 →
      ∀ P w, Short.Seed F P w q → ¬FanFailure F w q) : ExactSquareFormula := by
  apply exactSquareFormula_of_no_fan_failure
  intro u _ F acy score one P w q S fail
  exact exclude u q (fanFailure_index fail) F acy score one P w S fail

open PitchCut ResidueTwoLower in
/-- Only side 161 remains. -/
theorem square_exact_outside_pending_sides {n : Nat} (hn : 0<n)
    (outside : n≠161) :
    maxPreserved n n=squareScore n := by
  by_cases small : n≤5
  · exact exactSquareFormula_through_five hn small
  let k := n/3
  have rem : n=3*k ∨ n=3*k+1 ∨ n=3*k+2 := by dsimp [k]; omega
  rcases rem with h|h|h <;> rw [h]
  · rw [squareScore_three_mul]; exact ResidueZero.maxPreserved_three_mul (by omega)
  · exact maxPreserved_residue_one k
  · by_cases eight : k=2
    · rw [eight]; exact ResidueTwoUpper.Eight.maximum_eq
    apply Nat.le_antisymm _ (squareScore_lower_residue_two k)
    apply ResidueTwoUpper.Stencil.upper_of_remaining_at maxPreserved_eleven_upper k (by omega)
    rintro u side ⟨F,mem,score⟩
    have acy := mem_acyclicForcedSets.mp mem
    have one := one_gap_of_exceptional_score F acy score
    by_cases early : u≤2
    · exact Short.exclude_early u early F acy one score
    have large : 4≤u := by omega
    obtain ⟨P,w,q,_,fail⟩ := failure_from_score (by omega) acy score one
    exact no_fan_failure_large large fail

theorem maxPreserved_square_of_ge_162 {n : Nat} (hn : 162≤n) :
    maxPreserved n n=squareScore n :=
  square_exact_outside_pending_sides (by omega) (by omega)

theorem maxPreserved_203_exact : maxPreserved 203 203 = squareScore 203 :=
  maxPreserved_square_of_ge_162 (by decide)

theorem maxPreserved_square_of_ge_204 {n : Nat} (hn : 204≤n) :
    maxPreserved n n=squareScore n := maxPreserved_square_of_ge_162 (by omega)

theorem maxPreserved_245_exact : maxPreserved 245 245 = squareScore 245 :=
  maxPreserved_square_of_ge_204 (by decide)

theorem maxPreserved_square_of_ge_246 {n : Nat} (hn : 246≤n) :
    maxPreserved n n=squareScore n := maxPreserved_square_of_ge_204 (by omega)

theorem maxPreserved_287_exact : maxPreserved 287 287 = squareScore 287 :=
  maxPreserved_square_of_ge_246 (by decide)

theorem maxPreserved_square_of_ge_288 {n : Nat} (hn : 288≤n) :
    maxPreserved n n=squareScore n := maxPreserved_square_of_ge_246 (by omega)

theorem maxPreserved_329_exact : maxPreserved 329 329 = squareScore 329 :=
  maxPreserved_square_of_ge_288 (by decide)

theorem maxPreserved_square_of_ge_330 {n : Nat} (hn : 330≤n) :
    maxPreserved n n=squareScore n := maxPreserved_square_of_ge_288 (by omega)

theorem maxPreserved_371_exact : maxPreserved 371 371 = squareScore 371 :=
  maxPreserved_square_of_ge_330 (by decide)

theorem maxPreserved_square_of_ge_372 {n : Nat} (hn : 372≤n) :
    maxPreserved n n=squareScore n := maxPreserved_square_of_ge_330 (by omega)

theorem maxPreserved_413_exact : maxPreserved 413 413 = squareScore 413 :=
  maxPreserved_square_of_ge_372 (by decide)

theorem maxPreserved_square_of_ge_414 {n : Nat} (hn : 414≤n) :
    maxPreserved n n=squareScore n := maxPreserved_square_of_ge_372 (by omega)

theorem maxPreserved_455_exact : maxPreserved 455 455 = squareScore 455 :=
  maxPreserved_square_of_ge_414 (by decide)

theorem maxPreserved_square_of_ge_456 {n : Nat} (hn : 456≤n) :
    maxPreserved n n=squareScore n := maxPreserved_square_of_ge_414 (by omega)

theorem maxPreserved_497_exact : maxPreserved 497 497 = squareScore 497 :=
  maxPreserved_square_of_ge_456 (by decide)

theorem maxPreserved_square_of_ge_498 {n : Nat} (hn : 498≤n) :
    maxPreserved n n=squareScore n := maxPreserved_square_of_ge_456 (by omega)

theorem maxPreserved_539_exact : maxPreserved 539 539 = squareScore 539 :=
  maxPreserved_square_of_ge_498 (by decide)

theorem maxPreserved_square_of_ge_540 {n : Nat} (hn : 540≤n) :
    maxPreserved n n=squareScore n := maxPreserved_square_of_ge_498 (by omega)

theorem maxPreserved_square_of_ge_582 {n : Nat} (hn : 582≤n) :
    maxPreserved n n=squareScore n := maxPreserved_square_of_ge_540 (by omega)

theorem exactSquareFormula_iff_161 : ExactSquareFormula ↔ maxPreserved 161 161=squareScore 161 := by
  refine ⟨fun all => all _ (by decide),?_⟩
  intro at161 n hn
  by_cases h : n=161
  · exact h ▸ at161
  · exact square_exact_outside_pending_sides hn h

theorem exactSquareFormula_iff_two_sides : ExactSquareFormula ↔
    ∀ u : Nat, 3≤u → u≤4 → maxPreserved (35+42*u) (35+42*u)=squareScore (35+42*u) := by
  refine ⟨fun all u _ _ => all _ (by omega),?_⟩
  intro finite n hn
  by_cases atSide : ∃ u : Nat, 3≤u ∧ u≤4 ∧ n=35+42*u
  · obtain ⟨u,lo,hi,rfl⟩ := atSide
    exact finite u lo hi
  · exact square_exact_outside_pending_sides hn (fun eq => atSide ⟨3,by decide,by decide,eq⟩)

theorem exactSquareFormula_iff_three_sides : ExactSquareFormula ↔
    ∀ u : Nat, 3≤u → u≤5 → maxPreserved (35+42*u) (35+42*u)=squareScore (35+42*u) := by
  exact ⟨fun all u _ _ => all _ (by omega),
    fun h => exactSquareFormula_iff_two_sides.mpr (fun u lo hi => h u lo (by omega))⟩

theorem exactSquareFormula_iff_four_sides : ExactSquareFormula ↔
    ∀ u : Nat, 3≤u → u≤6 → maxPreserved (35+42*u) (35+42*u)=squareScore (35+42*u) := by
  exact ⟨fun all u _ _ => all _ (by omega),
    fun h => exactSquareFormula_iff_three_sides.mpr (fun u lo hi => h u lo (by omega))⟩

theorem exactSquareFormula_iff_five_sides : ExactSquareFormula ↔
    ∀ u : Nat, 3≤u → u≤7 → maxPreserved (35+42*u) (35+42*u)=squareScore (35+42*u) := by
  exact ⟨fun all u _ _ => all _ (by omega),
    fun h => exactSquareFormula_iff_four_sides.mpr (fun u lo hi => h u lo (by omega))⟩

theorem exactSquareFormula_iff_six_sides : ExactSquareFormula ↔
    ∀ u : Nat, 3≤u → u≤8 → maxPreserved (35+42*u) (35+42*u)=squareScore (35+42*u) := by
  exact ⟨fun all u _ _ => all _ (by omega),
    fun h => exactSquareFormula_iff_five_sides.mpr (fun u lo hi => h u lo (by omega))⟩

theorem exactSquareFormula_iff_seven_sides : ExactSquareFormula ↔
    ∀ u : Nat, 3≤u → u≤9 → maxPreserved (35+42*u) (35+42*u)=squareScore (35+42*u) := by
  exact ⟨fun all u _ _ => all _ (by omega),
    fun h => exactSquareFormula_iff_six_sides.mpr (fun u lo hi => h u lo (by omega))⟩

theorem exactSquareFormula_iff_eight_sides : ExactSquareFormula ↔
    ∀ u : Nat, 3≤u → u≤10 → maxPreserved (35+42*u) (35+42*u)=squareScore (35+42*u) := by
  exact ⟨fun all u _ _ => all _ (by omega),
    fun h => exactSquareFormula_iff_seven_sides.mpr (fun u lo hi => h u lo (by omega))⟩

theorem exactSquareFormula_iff_nine_sides : ExactSquareFormula ↔
    ∀ u : Nat, 3≤u → u≤11 → maxPreserved (35+42*u) (35+42*u)=squareScore (35+42*u) := by
  exact ⟨fun all u _ _ => all _ (by omega),
    fun h => exactSquareFormula_iff_eight_sides.mpr (fun u lo hi => h u lo (by omega))⟩

theorem exactSquareFormula_iff_ten_sides : ExactSquareFormula ↔
    ∀ u : Nat, 3≤u → u≤12 → maxPreserved (35+42*u) (35+42*u)=squareScore (35+42*u) := by
  exact ⟨fun all u _ _ => all _ (by omega),
    fun h => exactSquareFormula_iff_nine_sides.mpr (fun u lo hi => h u lo (by omega))⟩

theorem exactSquareFormula_iff_eleven_sides : ExactSquareFormula ↔
    ∀ u : Nat, 3≤u → u≤13 → maxPreserved (35+42*u) (35+42*u)=squareScore (35+42*u) := by
  refine ⟨fun all u _ _ => all _ (by omega),?_⟩
  intro finite n hn
  by_cases atSide : ∃ u : Nat, 3≤u ∧ u≤13 ∧ n=35+42*u
  · obtain ⟨u,lo,hi,rfl⟩ := atSide
    exact finite u lo hi
  · exact square_exact_outside_pending_sides hn (fun eq => atSide ⟨3,by decide,by decide,eq⟩)

end GridGraphs
