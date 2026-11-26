import Mathlib

namespace GridGraphs.RepairDefectBudget

/-- One common guarded hole can rule out every pair of end depths.
If there is no such hole, one entire end family must be obstructed. -/
theorem localize {α β : Type*} (g : Prop) (north : α → Prop) (south : β → Prop) :
    (∀ a b, g ∨ north a ∨ south b) ↔ g ∨ (∀ a, north a) ∨ (∀ b, south b) := by
  classical
  constructor
  · intro h
    by_cases hg : g
    · exact Or.inl hg
    by_cases hn : ∀ a, north a
    · exact Or.inr (Or.inl hn)
    push Not at hn
    obtain ⟨a,ha⟩ := hn
    exact Or.inr (Or.inr (fun b => ((h a b).resolve_left hg).resolve_left ha))
  · rintro (hg | hn | hs) a b
    · exact Or.inl hg
    · exact Or.inr (Or.inl (hn a))
    · exact Or.inr (Or.inr (hs b))

theorem notFour (debit : Fin 4 → ℚ)
    (budget : ∑ i, debit i ≤ 7/6) : ∃ i, debit i < 1/3 := by
  by_contra! h
  have lb := Finset.sum_le_sum (s := Finset.univ) (fun i _ => h i)
  norm_num at lb
  linarith

/-- For arbitrary k, thirty times the deep-chart slack above comb+1,
after cancelling the common quadratic. This is the amount a uniform
charging argument must beat, not a constant reference-side budget. -/
theorem combGap (k : ℤ) :
    160*k-35-30*(5*k+(3*k-13)/10+1) =
    k-26+3*((3*k-13)%10) := by omega

end GridGraphs.RepairDefectBudget
