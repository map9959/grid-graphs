import GridGraphs.Accounting.BoundaryStratifiedCarrierBound
import GridGraphs.Accounting.CarrierLayers.RadialNearTightBoundary

/-! # Inward witnesses at boundary deficiency five

No orientation of the other corner holes is prescribed here. The coordinate
lemma applies to any top-side hole away from the two corner-neighbor positions.
It proves preservation, not that the resulting induced carrier is a singleton.
-/

namespace GridGraphs.BoundaryFive

open Finset SimpleGraph

/-- A top-side hole away from the corner neighbors forces its twice-inward
vertex when the ambient forced graph has one component. -/
theorem top_hole_forces_deep {n : Nat} (hn : 7 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 5)
    (hc : Fintype.card (forcedEdgeGraph (gridGraph n n)
      (↑F : Set _)).ConnectedComponent = 1)
    (j : Nat) (hjlo : 2 ≤ j) (hjhi : j + 3 ≤ n)
    (hhole : (⟨0, by omega⟩, ⟨j, by omega⟩) ∉ F) :
    (⟨2, by omega⟩, ⟨j, by omega⟩) ∈ F := by
  have hempty := boundaryDeficiencySum_compl_eq_five_next_ring_notMem hn F hacyc hb
  have hw : (⟨1, by omega⟩, ⟨j, by omega⟩) ∉ F :=
    hempty _ (by simp) (by simp; omega) (by simp; omega)
      (by simp; omega) (by simp)
  obtain ⟨v, hv, hadj⟩ := CarrierLayers.preserved_neighbor_of_one_forced_component
    (by omega) F hc _ hw
  have hcoord := hadj
  simp only [gridGraph, adjacent, Fin.ext_iff] at hcoord
  dsimp at hcoord
  have hcases : v = (⟨0, by omega⟩, ⟨j, by omega⟩) ∨
      v = (⟨1, by omega⟩, ⟨j - 1, by omega⟩) ∨
      v = (⟨1, by omega⟩, ⟨j + 1, by omega⟩) ∨
      v = (⟨2, by omega⟩, ⟨j, by omega⟩) := by
    simp only [Prod.ext_iff, Fin.ext_iff]
    omega
  rcases hcases with h | h | h | h
  · exact (hhole (h ▸ hv)).elim
  · subst v
    exact (hempty _ (by simp) (by simp; omega) (by simp; omega)
      (by simp; omega) (by simp) hv).elim
  · subst v
    exact (hempty _ (by simp) (by simp; omega) (by simp)
      (by simp; omega) (by simp) hv).elim
  · exact h ▸ hv

end GridGraphs.BoundaryFive
