import GridGraphs.Constructions.ResidueTwo.LowerZipper

namespace GridGraphs.ResidueTwoLower

theorem int_band_cover {l ph j b len : Nat} (hl : 1≤l) (md : l%3=0)
    (mx : ph<7) (h : band l ph j (7*(b+1)≤len) false=true) :
    ((((j:ℤ)≤l ∧ (j:ℤ)%3=0) ∨ ((l:ℤ)+4≤j ∧ (j:ℤ)%3=1)) ∧
      ((ph:ℤ)<5 ∨ (len:ℤ)<7*((b:ℤ)+1) ∨ (j:ℤ)<l ∨ (l:ℤ)<j)) ∨
      ((ph:ℤ)=2 ∧ (j:ℤ)=(l:ℤ)+2) ∨
      (7*((b:ℤ)+1) ≤ (len:ℤ) ∧
        (((ph:ℤ)=5 ∧ (j:ℤ)=(l:ℤ)+2) ∨ ((ph:ℤ)=6 ∧ (j:ℤ)=(l:ℤ)-1))) := by
  simp only [band,Bool.false_eq_true,if_false,beq_iff_eq,Bool.and_eq_true,
    decide_eq_true_eq] at h
  split_ifs at h <;> simp [regular,leftRail,rightRail,bne] at h <;> omega

end GridGraphs.ResidueTwoLower
