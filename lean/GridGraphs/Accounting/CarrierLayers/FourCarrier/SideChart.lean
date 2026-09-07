import GridGraphs.Accounting.CarrierLayers.FourCarrier.SaturatedPhase

/-! # Local coordinates for a missing side

The first coordinate runs along the missing side and the second runs inward.
This chart transports grid edges and local cycles only. It makes no claim
about the next-ring boundary map.
-/

namespace GridGraphs.CarrierLayers.FourCarrier

open Finset SimpleGraph

/-- Map the local left side to the chosen actual side. -/
def sideChart {n : Nat} (s : Fin 4) (v : GridVertex n n) : GridVertex n n :=
  if s.val = 0 then (v.2, v.1)
  else if s.val = 1 then (v.2.rev, v.1)
  else if s.val = 2 then v else (v.1, v.2.rev)

theorem sideChart_injective {n : Nat} (s : Fin 4) :
    Function.Injective (sideChart (n := n) s) := by
  intro u v he
  fin_cases s <;> simp [sideChart, Prod.ext_iff, Fin.ext_iff] at * <;> omega

theorem sideChart_surjective {n : Nat} (s : Fin 4) :
    Function.Surjective (sideChart (n := n) s) :=
  Finite.surjective_of_injective (sideChart_injective s)

theorem sideChart_adj {n : Nat} (s : Fin 4) (u v : GridVertex n n) :
    (gridGraph n n).Adj (sideChart s u) (sideChart s v) ↔ (gridGraph n n).Adj u v := by
  fin_cases s <;> simp [sideChart, gridGraph, adjacent, Fin.ext_iff] <;> omega

theorem sideChart_boundary {n : Nat} (s : Fin 4) (v : GridVertex n n) :
    IsGridBoundary (sideChart s v) ↔ IsGridBoundary v := by
  fin_cases s <;> simp [sideChart, IsGridBoundary] <;> omega

theorem sideChart_corner {n : Nat} (s : Fin 4) (v : GridVertex n n) :
    BoundarySix.Corner (sideChart s v) ↔ BoundarySix.Corner v := by
  fin_cases s <;> simp [sideChart, BoundarySix.Corner] <;> omega

theorem sideChart_near {n : Nat} (s : Fin 4) (v : GridVertex n n) :
    BoundarySix.Near (sideChart s v) ↔ BoundarySix.Near v := by
  fin_cases s <;> simp [sideChart, BoundarySix.Near] <;> omega

theorem sideChart_openSide {n : Nat} (s : Fin 4) (v : GridVertex n n) :
    OnOpenSide s (sideChart s v) ↔ v.2.val = 0 ∧ 0 < v.1.val ∧ v.1.val + 1 < n := by
  fin_cases s <;> simp [sideChart, OnOpenSide, OnSide] <;> omega

theorem sideChart_position {n : Nat} (s : Fin 4) (v : GridVertex n n) :
    sidePosition s (sideChart s v) = v.1.val := by
  fin_cases s <;> simp [sideChart, sidePosition]

theorem sideChart_acyclic {n : Nat} (s : Fin 4) (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic) :
    (forcedEdgeGraph (gridGraph n n) {v | sideChart s v ∈ F}).IsAcyclic := by
  let f : forcedEdgeGraph (gridGraph n n) {v | sideChart s v ∈ F} →g
      forcedEdgeGraph (gridGraph n n) (↑F : Set _) :=
    { toFun := sideChart s
      map_rel' := fun h => ⟨(sideChart_adj s _ _).mpr h.1, h.2⟩ }
  exact hacyc.comap f (sideChart_injective s)

/-- The actual inward neighbor of a charted root has local depth one. -/
theorem sideChart_root_inward {n : Nat} (hn : 5 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp, ¬ OnOpenSide s v.val)
    (t : Fin n) (ht : 0 < t.val ∧ t.val + 1 < n)
    (hv : sideChart s (t, ⟨0, by omega⟩) ∈ F) :
    sideChart s (t, ⟨1, by omega⟩) ∈ F := by
  obtain ⟨w, hw, hwr, hadj⟩ := missing_side_root_inward hn F hacyc s hmissing
    _ hv ((sideChart_openSide s _).mpr ⟨rfl, ht⟩)
  have he : w = sideChart s (t, ⟨1, by omega⟩) := by
    unfold IsNextRing at hwr
    fin_cases s <;>
      simp [sideChart, gridGraph, adjacent, Fin.ext_iff, Prod.ext_iff] at hadj ⊢ <;> omega
  exact he ▸ hw

end GridGraphs.CarrierLayers.FourCarrier
