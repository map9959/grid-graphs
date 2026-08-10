import Mathlib.GroupTheory.Perm.Cycle.Basic

/-!
# Finite permutation cuts

An orbit of a finite permutation that enters a finite set must leave it again.
This elementary cut-balance fact will identify the two orientations of every
bridge in the contour permutation of an embedded tree.
-/

namespace GridGraphs

open Finset

/-- If `enter` crosses from outside `S` to inside and `leave` is the unique
point crossing from inside to outside, then both points lie in the same orbit
of a finite permutation. -/
theorem Equiv.Perm.sameCycle_of_unique_leave
    {α : Type*} [Fintype α] [DecidableEq α]
    (f : Equiv.Perm α) (S : Finset α) {enter leave : α}
    (henterOut : enter ∉ S) (henterIn : f enter ∈ S)
    (hleaveUnique : ∀ x, x ∈ S → f x ∉ S → x = leave) :
    f.SameCycle enter leave := by
  classical
  let C : Finset α := Finset.univ.filter fun x => f.SameCycle enter x
  have henterC : enter ∈ C := by
    simp [C, Equiv.Perm.SameCycle.refl]
  have hC_apply (x : α) : x ∈ C ↔ f x ∈ C := by
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Equiv.Perm.sameCycle_apply_right.symm
  have hexit : ∃ x ∈ C, x ∈ S ∧ f x ∉ S := by
    by_contra hnone
    push_neg at hnone
    let A := C ∩ S
    have hmap : A.image f ⊆ A := by
      intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨x, hxA, rfl⟩ := hy
      have hxC : x ∈ C := (Finset.mem_inter.mp hxA).1
      have hxS : x ∈ S := (Finset.mem_inter.mp hxA).2
      have hfxS : f x ∈ S := hnone x hxC hxS
      exact Finset.mem_inter.mpr ⟨(hC_apply x).mp hxC, hfxS⟩
    have hcard : (A.image f).card = A.card :=
      Finset.card_image_iff.mpr (fun _ _ _ _ h => f.injective h)
    have hmapEq : A.image f = A :=
      Finset.eq_of_subset_of_card_le hmap (by omega)
    have hfenterC : f enter ∈ C := (hC_apply enter).mp henterC
    have hfenterA : f enter ∈ A := Finset.mem_inter.mpr ⟨hfenterC, henterIn⟩
    rw [← hmapEq, Finset.mem_image] at hfenterA
    obtain ⟨x, hxA, hx⟩ := hfenterA
    have hxeq : x = enter := f.injective hx
    subst x
    exact henterOut (Finset.mem_inter.mp hxA).2
  obtain ⟨x, hxC, hxS, hfxS⟩ := hexit
  have hxleave := hleaveUnique x hxS hfxS
  subst x
  exact (Finset.mem_filter.mp hxC).2

end GridGraphs
