import GridGraphs.Constructions.ResidueTwo.LowerZipperPieces

namespace GridGraphs.ResidueTwoLower

theorem band_rowCount {k a : Nat} (ha : 1 ≤ a) (bound : a+2 ≤ k)
    (phase : Nat) (whole right : Bool) :
    rowCount (fun j => band (3*a) phase j whole right) (3*k+2) =
      k+1+(if phase=2 then 1 else 0) := by
  let l := 3*a
  have reg : rowCount (regular l) (3*k+2) = k+1 := by rw [regular_prefix]; omega
  have mid : regular l (l+2) = false := by simp [regular,leftRail,rightRail,l]
  by_cases h : phase=2
  · simp only [band,h,beq_self_eq_true,if_true]
    rw [rowCount_wire_add _ (by dsimp [l]; omega) mid,reg]
  · have h' : (phase == 2) = false := by simpa using h
    simp only [band,h',Bool.false_eq_true,↓reduceIte,h,add_zero]
    by_cases v : (whole && decide (phase ≥ 5)) = true
    · simp only [v,if_true]
      let del := if right then l+4 else l
      let ins := if phase == 5 then l+2 else if right then l+5 else l-1
      have marked : regular l del = true := by
        cases right <;> simp [regular,leftRail,rightRail,del,l] <;> omega
      have fresh : regular l ins = false := by
        dsimp [ins]; split <;> cases right <;> simp [regular,leftRail,rightRail,l] <;> omega
      have bd : del<3*k+2 := by cases right <;> simp [del,l] <;> omega
      have bi : ins<3*k+2 := by dsimp [ins]; split <;> cases right <;> simp [l] <;> omega
      change rowCount (fun j => (regular l j && j != del) || j == ins) _ = _
      rw [rowCount_wire_add _ bi (by simp [fresh]),rowCount_wire_remove _ bd marked,reg]
    · simpa [v] using reg

/-- Count the geometric band schedule, even when the final band is truncated
before either of the two moving-tip rows. -/
theorem band_sum {k len : Nat} (a : Nat → Nat) (right : Nat → Bool)
    (bounds : ∀ i < len, 1 ≤ a i ∧ a i+2 ≤ k) :
    (∑ i ∈ Finset.range len, rowCount
      (fun j => band (3*a i) (i%7) j (7*(i/7+1) ≤ len) (right i)) (3*k+2)) =
      len*(k+1)+(len+4)/7 := by
  calc
    _ = ∑ i ∈ Finset.range len, (k+1+(if i%7=2 then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      obtain ⟨h,b⟩ := bounds i (Finset.mem_range.mp hi)
      exact band_rowCount h b _ _ _
    _ = _ := by
      clear bounds
      induction len with
      | zero => simp
      | succ len ih =>
        rw [Finset.sum_range_succ,ih,Nat.succ_mul]
        split <;> omega

end GridGraphs.ResidueTwoLower
