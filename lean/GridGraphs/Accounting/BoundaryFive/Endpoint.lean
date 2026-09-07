import GridGraphs.Accounting.BoundaryFive.SingletonBound
import GridGraphs.Accounting.CarrierLayers.GlobalUpperProfiles

/-! # Singleton obstruction at the old endpoint

This excludes an actual nonpure singleton at the old endpoint. It does not
assert singleton existence or an unconditional improved maximum bound.
-/

namespace GridGraphs.BoundaryFive

open Finset SimpleGraph

/-- An old-endpoint set has no singleton nonpure induced carrier. Combined
with generic singleton existence, this would exclude the endpoint itself. -/
theorem old_upper_endpoint_no_nonpure_singleton {k : Nat} (hk : 5 ≤ k)
    (hmod : k % 3 = 2)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hf : 3 * k ^ 2 + 7 * k + (2 * k + 2) / 3 ≤ F.card)
    (Z : ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).ConnectedComponent)
    (hZ : Z ∉ pureBoundaryCarriers F) : Z.supp.toFinset.card ≠ 1 := by
  intro hsize
  obtain ⟨_, hr, _, hb⟩ :=
    CarrierLayers.residueTwo_old_upper_endpoint_profile hk hmod F hacyc hf
  have hbound := card_add_side_le_of_singleton (by omega) F hacyc hb Z hZ hsize
  rw [hr] at hbound
  have hsub : 3 * k + 2 - 4 = 3 * k - 2 := by omega
  have hsub' : 3 * k - 2 + 2 = 3 * k := by omega
  have hexcess : 4 ≤ (2 * k + 2) / 3 := by omega
  rw [hsub] at hbound
  nlinarith

end GridGraphs.BoundaryFive
