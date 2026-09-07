import GridGraphs.Accounting.CarrierLayers.FourCarrier.PathCount

/-! # The perimeter with one open side removed

The path includes all four corners. Its holes are ordinary, unweighted holes.
The side involutions below are used only for this path, not for the fixed
next-ring boundary injection.
-/

namespace GridGraphs.CarrierLayers.FourCarrier

open Finset SimpleGraph

attribute [local instance] Classical.propDecidable

private def topPath {n : Nat} (hn : 2 ≤ n) (i : Fin (3 * n - 2)) : GridVertex n n :=
  if h : i.val < n then (⟨i.val, h⟩, ⟨0, by omega⟩)
  else if h' : i.val < 2 * n - 1 then
    (⟨n - 1, by omega⟩, ⟨i.val - n + 1, by omega⟩)
  else (⟨3 * n - 3 - i.val, by have := i.isLt; omega⟩, ⟨n - 1, by omega⟩)

private theorem topPath_injective {n : Nat} (hn : 2 ≤ n) :
    Function.Injective (topPath hn) := by
  intro i j he
  have hr := congrArg (fun v : GridVertex n n => v.1.val) he
  have hc := congrArg (fun v : GridVertex n n => v.2.val) he
  unfold topPath at hr hc
  split_ifs at hr hc <;> dsimp at hr hc <;> apply Fin.ext <;> omega

private theorem topPath_adj {n : Nat} (hn : 2 ≤ n)
    (i j : Fin (3 * n - 2)) (hij : i.val + 1 = j.val) :
    (gridGraph n n).Adj (topPath hn i) (topPath hn j) := by
  have hi := i.isLt
  have hj := j.isLt
  unfold topPath
  split_ifs <;> simp [gridGraph, adjacent, Fin.ext_iff] <;> omega

private theorem topPath_range {n : Nat} (hn : 2 ≤ n) (v : GridVertex n n) :
    (∃ i, topPath hn i = v) ↔ IsGridBoundary v ∧ ¬ OnOpenSide 0 v := by
  constructor
  · rintro ⟨i, rfl⟩
    unfold topPath
    split_ifs <;> unfold IsGridBoundary OnOpenSide OnSide <;> dsimp <;> omega
  · intro hv
    have hgeom := hv
    unfold IsGridBoundary OnOpenSide OnSide at hgeom
    dsimp at hgeom
    by_cases hc : v.2.val = 0
    · refine ⟨⟨v.1.val, by omega⟩, ?_⟩
      simp only [topPath, v.1.isLt, dite_true]
      exact Prod.ext rfl (Fin.ext (by simpa using hc.symm))
    by_cases hr : v.1.val = n - 1
    · refine ⟨⟨n + v.2.val - 1, by omega⟩, ?_⟩
      have h1 : ¬ n + v.2.val - 1 < n := by omega
      have h2 : n + v.2.val - 1 < 2 * n - 1 := by omega
      simp only [topPath, h1, dite_false, h2, dite_true]
      apply Prod.ext <;> apply Fin.ext <;> dsimp <;> omega
    · refine ⟨⟨3 * n - 3 - v.1.val, by omega⟩, ?_⟩
      have h1 : ¬ 3 * n - 3 - v.1.val < n := by omega
      have h2 : ¬ 3 * n - 3 - v.1.val < 2 * n - 1 := by omega
      simp only [topPath, h1, dite_false, h2]
      apply Prod.ext <;> apply Fin.ext <;> dsimp <;> omega

private def sideInvolution {n : Nat} (s : Fin 4) (v : GridVertex n n) : GridVertex n n :=
  if s.val = 0 then v else if s.val = 1 then (v.1.rev, v.2)
  else if s.val = 2 then (v.2, v.1) else (v.2.rev, v.1.rev)

private theorem sideInvolution_involutive {n : Nat} (s : Fin 4) :
    Function.Involutive (sideInvolution (n := n) s) := by
  intro v
  fin_cases s <;> simp [sideInvolution]

private theorem sideInvolution_adj {n : Nat} (s : Fin 4) (v w : GridVertex n n)
    (h : (gridGraph n n).Adj v w) :
    (gridGraph n n).Adj (sideInvolution s v) (sideInvolution s w) := by
  fin_cases s <;>
    simp [sideInvolution, gridGraph, adjacent, Fin.ext_iff, Fin.val_rev] at * <;> omega

private theorem sideInvolution_offside {n : Nat} (hn : 2 ≤ n)
    (s : Fin 4) (v : GridVertex n n) :
    (IsGridBoundary (sideInvolution s v) ∧ ¬ OnOpenSide s (sideInvolution s v)) ↔
      IsGridBoundary v ∧ ¬ OnOpenSide 0 v := by
  fin_cases s <;>
    simp [sideInvolution, IsGridBoundary, OnOpenSide, OnSide, Fin.val_rev] <;> omega

/-- Ordinary holes on the complementary perimeter path bound the number of
pure carriers. Corners are included, and no acyclicity assumption is needed. -/
theorem pure_carriers_le_offside_holes_add_one {n : Nat} (hn : 2 ≤ n)
    (F : Finset (GridVertex n n)) (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp,
      ¬ OnOpenSide s v.val) :
    (pureBoundaryCarriers F).card ≤
      ((univ \ F).filter (fun v => IsGridBoundary v ∧ ¬ OnOpenSide s v)).card + 1 := by
  classical
  let e := sideInvolution s ∘ topPath hn
  have hinj : Function.Injective e :=
    (sideInvolution_involutive s).injective.comp (topPath_injective hn)
  have hrange (v : GridVertex n n) :
      (∃ i, e i = v) ↔ IsGridBoundary v ∧ ¬ OnOpenSide s v := by
    constructor
    · rintro ⟨i, rfl⟩
      exact (sideInvolution_offside hn s _).mpr ((topPath_range hn _).mp ⟨i, rfl⟩)
    · intro hv
      have htop := (sideInvolution_offside hn s (sideInvolution s v)).mp
        (by simpa only [sideInvolution_involutive s v] using hv)
      obtain ⟨i, hi⟩ := (topPath_range hn _).mpr htop
      exact ⟨i, by dsimp [e]; rw [hi, sideInvolution_involutive s v]⟩
  have hcount := components_le_path_holes_add_one (gridGraph n n) F
    (pureBoundaryCarriers F) e hinj
    (fun i j hij => sideInvolution_adj s _ _ (topPath_adj hn i j hij)) (by
      intro C hC
      obtain ⟨v, hv⟩ := C.nonempty_supp
      obtain ⟨i, hi⟩ := (hrange v.val).mpr
        ⟨(mem_filter.mp hC).2 v hv, hmissing C hC v hv⟩
      refine ⟨i, hi ▸ v.property, ?_⟩
      simpa only [hi] using hv)
  have he : (univ.image e) \ F =
      (univ \ F).filter (fun v => IsGridBoundary v ∧ ¬ OnOpenSide s v) := by
    ext v
    simp only [mem_sdiff, mem_image, mem_univ, true_and, mem_filter]
    rw [hrange]
    tauto
  rwa [he] at hcount

end GridGraphs.CarrierLayers.FourCarrier
