import Mathlib

namespace GridGraphs.BlockedRimExchange

open Module

/-- Port-identification spaces: if the old local wiring and the exterior
do not close a cycle, the new cycle space costs at most the number of
independent old classes merged by the replacement. -/
theorem portNullity {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (old new ext : Submodule K V)
    (compatible : Disjoint old ext) :
    finrank K old + finrank K ↥(new ⊓ ext) ≤ finrank K ↥(old ⊔ new) := by
  have hd : Disjoint old (new ⊓ ext) := compatible.mono_right inf_le_right
  have h := Submodule.finrank_sup_add_finrank_inf_eq old (new ⊓ ext)
  rw [hd.eq_bot, finrank_bot, add_zero] at h
  rw [← h]
  exact Submodule.finrank_mono (sup_le_sup_left inf_le_left old)

theorem blockedCrop (original small improved upper removed posts allDebt heavyDebt : ℤ)
    (crop : original = removed + small)
    (surgery : small + posts - allDebt - heavyDebt ≤ improved)
    (budget : improved ≤ upper) :
    original ≤ removed + upper - posts + allDebt + heavyDebt := by omega

theorem paysAllLengths (removed delta e : ℤ)
    (pattern : removed-delta = 18-e) (rounding : 1≤e) :
    removed-23 ≤ delta-6 := by omega

end GridGraphs.BlockedRimExchange
