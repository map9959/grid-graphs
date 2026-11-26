import Mathlib

namespace GridGraphs.CoupledMaskSupport

/-- Strip paths are specified only on `foot`; their values elsewhere
are immaterial. A path includes its own compatible forest partition. -/
structure Strip (I A : Type) where
  foot : Set I
  paths : Set (I → A)

def realizes {I A : Type} (x : I → A) (s : Strip I A) : Prop :=
  ∃ p ∈ s.paths, ∀ i ∈ s.foot, p i = x i

def prune {I A : Type} (D : I → Set A) (s : Strip I A) (i : I) : Set A :=
  {a ∈ D i | i ∈ s.foot → ∃ p ∈ s.paths, p i = a ∧ ∀ j ∈ s.foot, p j ∈ D j}

theorem preserve {I A : Type} (x : I → A) (D : I → Set A) (s : Strip I A)
    (hD : ∀ i, x i ∈ D i) (hs : realizes x s) :
    ∀ i, x i ∈ prune D s i := by
  obtain ⟨p,hp,h⟩ := hs
  intro i
  exact ⟨hD i, fun hi => ⟨p,hp,h i hi,fun j hj => (h j hj) ▸ hD j⟩⟩

theorem passes {I A : Type} (x : I → A) (L : List (Strip I A)) (D : I → Set A)
    (hD : ∀ i, x i ∈ D i) (hs : ∀ s ∈ L, realizes x s) :
    ∀ i, x i ∈ L.foldl prune D i := by
  induction L generalizing D with
  | nil => exact hD
  | cons s L ih =>
    exact ih (prune D s) (preserve x D s hD (hs s (by simp)))
      (fun t ht => hs t (by simp [ht]))

/-- Arithmetic interface; the strip exclusions and rail tree are
verified computationally, not postulated as Lean axioms. -/
theorem endpoint623 (score : Nat)
    (rail : 129967 ≤ score) (upper : score ≤ 3*207^2+7*207-(207-5)/7)
    (excluded : score ≠ 129968) : score = 129967 := by
  norm_num at upper
  omega

end GridGraphs.CoupledMaskSupport
