import GridGraphs.Results.ExactSquareFormula
import GridGraphs.Constructions.CombCoverage

namespace GridGraphs.CombWord
open Finset

def ones (m : Nat) := ((List.range 4).filter m.testBit).length

private theorem ones_sum (m : Nat) : ones m =
    (if m.testBit 0 then 1 else 0) + (if m.testBit 1 then 1 else 0) +
    (if m.testBit 2 then 1 else 0) + (if m.testBit 3 then 1 else 0) := by
  change ([0,1,2,3].filter m.testBit).length = _
  cases h₀ : m.testBit 0 <;> cases h₁ : m.testBit 1 <;> cases h₂ : m.testBit 2 <;>
    cases h₃ : m.testBit 3 <;> simp [h₀,h₁,h₂,h₃]

private theorem sum_ones (w : List Nat) :
    ∑ x ∈ range w.length, ones w[x]! = marks w := by
  induction w with
  | nil => rfl
  | cons m ms ih =>
    rw [List.length_cons, sum_range_succ']
    simpa [marks, ones, Nat.add_comm] using congrArg (· + ones m) ih

private theorem sum_pitch (k R : Nat) :
    ∑ x ∈ range (3*k+1), (if x%3=0 then R else 0) = (k+1)*R := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 3*(k+1)+1=3*k+1+1+1+1 by omega,sum_range_succ,sum_range_succ,sum_range_succ,ih]
    rw [if_neg (show (3*k+1)%3≠0 by omega), if_neg (show (3*k+1+1)%3≠0 by omega),
      if_pos (show (3*k+1+1+1)%3=0 by omega)]
    ring

private noncomputable def rowSum (R : Nat) (w : List Nat) (x : Nat) : Nat := by
  classical
  exact ∑ y ∈ range (R+8), if Mark R w y x then 1 else 0

private theorem column_count (R : Nat) (w : List Nat) (x : Nat) :
    rowSum R w x = 2+(if x%3=0 then R else 0)+ones w[x]! := by
  classical
  let f := fun y => if Mark R w y x then 1 else 0
  change ∑ y ∈ range (R+8), f y = _
  rw [show R+8=2+R+6 by omega, sum_range_add, sum_range_add]
  have a : ∑ y ∈ range 2, f y = 1 := by
    simp only [sum_range_succ, sum_range_zero]
    simp (disch := omega) [f,Mark]
  have b : ∑ y ∈ range R, f (2+y) = (if x%3=0 then R else 0) := by
    calc
      _ = ∑ _y ∈ range R, (if x%3=0 then 1 else 0) := by
        apply sum_congr rfl
        intro y hy
        have h := mem_range.mp hy
        have iff : Mark R w (2+y) x ↔ x%3=0 := by unfold Mark; omega
        simp [f,iff]
      _ = _ := by split_ifs <;> simp_all
  rw [a,b,ones_sum]
  simp only [sum_range_succ,sum_range_zero,Nat.zero_add]
  dsimp [f,Mark]
  simp only [Nat.add_comm 2 R, Nat.add_assoc]
  simp (disch := omega) only [show ∀ t : Nat, R+t=R+7 ↔ t=7 by omega,
    show ∀ t : Nat, R+t≤R+1 ↔ t≤1 by omega,
    show ∀ t : Nat, R+2≤R+t ↔ 2≤t by omega,
    show ∀ t : Nat, R+t≤R+5 ↔ t≤5 by omega]
  norm_num [Nat.add_sub_add_left]
  omega

theorem markedSet_card (k R : Nat) (w : List Nat) (hn : 3*k+1=R+8)
    (hlen : w.length=3*k+1) :
    (markedSet R (3*k+1) w).card = 2*(3*k+1)+R*(k+1)+marks w := by
  classical
  rw [markedSet, Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]
  change (∑ x : Fin (3*k+1), ∑ y : Fin (3*k+1), if Mark R w y.val x.val then 1 else 0) = _
  have cols (x : Fin (3*k+1)) : (∑ y : Fin (3*k+1), if Mark R w y.val x.val then 1 else 0) =
      2+(if x.val%3=0 then R else 0)+ones w[x.val]! := by
    rw [Fin.sum_univ_eq_sum_range (fun y => if Mark R w y x.val then 1 else 0)]
    simpa only [rowSum,← hn] using column_count R w x.val
  simp_rw [cols]
  rw [Fin.sum_univ_eq_sum_range (fun x => 2+(if x%3=0 then R else 0)+ones w[x]!)]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
  rw [sum_pitch, ← hlen, sum_ones]
  rw [hlen]
  ring

end GridGraphs.CombWord

namespace GridGraphs

/-- An actual marked set in the square grid, with acyclic incident edges,
attains the residue-one formula throughout its stable range. -/
theorem squareMaskScore_comb (k : Nat) (hk : 5 ≤ k) :
    SquareMaskScore (3*k+1) (squareScore (3*k+1)) := by
  obtain ⟨w,ok,len,score⟩ := squareScore_comb_word k hk
  let R := 3*k+1-8
  have hn : 3*k+1 = R+8 := by dsimp [R]; omega
  refine ⟨_,CombWord.markedSet_feasible (by dsimp [R]; omega : 0<R) hn len ok,?_⟩
  exact (CombWord.markedSet_card k R w hn len).trans score

theorem squareScore_lower_three_mul_add_one (k : Nat) (hk : 5 ≤ k) :
    squareScore (3*k+1) ≤ maxPreserved (3*k+1) (3*k+1) :=
  (squareMaskScore_iff_le (by omega)).mp (squareMaskScore_comb k hk)

/-- Includes the five exceptional small sides, whose targets precede the
periodic comb range. -/
theorem squareScore_lower_residue_one (k : Nat) :
    squareScore (3*k+1) ≤ maxPreserved (3*k+1) (3*k+1) := by
  by_cases h : 5 ≤ k
  · exact squareScore_lower_three_mul_add_one k h
  · by_cases hz : k=0
    · subst k; exact maxPreserved_one_one.ge
    · have pos : 0<k := by omega
      rw [squareScore_three_mul_add_one k pos, Nat.sub_eq_zero_of_le (by omega : 3*k ≤ 13)]
      exact residueOne_le_maxPreserved k pos

end GridGraphs
