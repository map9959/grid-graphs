import GridGraphs.Constructions.ResidueTwo.LowerZipperPieces

namespace GridGraphs.ResidueTwoLower

private theorem shortRails (a w : Nat) (ha : 2 ≤ a) :
    rowCount (fun j => leftRail (3*a-6) j || rightRail (3*a+4) j) w =
      min ((w+2)/3) (a-1) + ((w+1)/3-(a+1)) := by
  induction w with
  | zero => simp [rowCount]
  | succ w ih =>
    rw [rowCount_succ,ih]
    simp only [leftRail,rightRail,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq]
    split <;> omega

theorem rowCount_interval (lo hi w : Nat) :
    rowCount (fun j => lo ≤ j && j < hi) w = min w hi-min w lo := by
  induction w with
  | zero => simp [rowCount]
  | succ w ih =>
    rw [rowCount_succ,ih]
    simp only [Bool.and_eq_true,decide_eq_true_eq]
    split <;> omega

theorem cap_counts {a k : Nat} (ha : 2 ≤ a) (hk : a+2 ≤ k) :
    let c := fun r => rowCount (cap (3*a) r) (3*k+2)
    c 0 = k ∧ c 1 = k+3 ∧ c 2 = k ∧ c 3 = 0 ∧ c 4 = 3*k+2 := by
  dsimp only
  let s := fun j => leftRail (3*a-6) j || rightRail (3*a+4) j
  have base : rowCount s (3*k+2) = k-1 := by rw [shortRails _ _ ha]; omega
  have null (j : Nat) (lo : 3*a-4 ≤ j) (hi : j < 3*a+4) : s j=false := by
    simp [s,leftRail,rightRail]; omega
  refine ⟨?_,?_,?_,?_,?_⟩
  · change rowCount (fun j => s j || j == 3*a+2) _ = _
    rw [rowCount_wire_add _ (by omega) (null _ (by omega) (by omega)),base]; omega
  · change rowCount (fun j => s j || (decide (3*a-4 ≤ j) && decide (j<3*a))) _ = _
    rw [rowCount_or,base,rowCount_interval]
    · omega
    · intro j hj h
      simp
      intro lo
      by_contra! hi
      rw [null j (by omega) (by omega)] at h
      contradiction
  · change rowCount (fun j => s j || j == 3*a+1) _ = _
    rw [rowCount_wire_add _ (by omega) (null _ (by omega) (by omega)),base]; omega
  · simp [cap,rowCount]
  · simp [cap,rowCount]

end GridGraphs.ResidueTwoLower
