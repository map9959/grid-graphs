import Mathlib

namespace GridGraphs.ToothVacancyPrice

/-- A dirty row covers only the clipped radius-two neighborhood about it. -/
theorem fiveRowCover (n : ℕ) (dirty : Finset ℕ)
    (near : ℕ → Finset ℕ) (size : ∀ i ∈ dirty, (near i).card ≤ 5)
    (covers : Finset.range n ⊆ dirty.biUnion near) :
    n ≤ 5 * dirty.card := by
  calc n = (Finset.range n).card := by simp
       _ ≤ (dirty.biUnion near).card := Finset.card_le_card covers
       _ ≤ ∑ i ∈ dirty, (near i).card := Finset.card_biUnion_le
       _ ≤ ∑ _i ∈ dirty, 5 := Finset.sum_le_sum size
       _ = _ := by simp [Nat.mul_comm]

/-- Window restriction once the physical longitudinal repair has been priced. -/
theorem mixedBlock (L holes breaks off deep : ℤ)
    (repair : holes-breaks ≤ off) (columnPrice : deep ≤ 2*(holes-breaks))
    (noPitch : L-4 ≤ deep+off) : L-4 ≤ 3*off := by omega

end GridGraphs.ToothVacancyPrice
