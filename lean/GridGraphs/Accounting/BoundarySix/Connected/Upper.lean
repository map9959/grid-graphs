import GridGraphs.Accounting.BoundarySix.Connected.SingletonCapacity

/-! # Complete exclusion of the current boundary-six endpoint -/

namespace GridGraphs.BoundarySix.Connected

open Finset SimpleGraph

/-- No feasible boundary-six set reaches the current k=1 mod 3 endpoint.
There are no connectivity, coverage, ring, corner, or carrier hypotheses. -/
theorem boundary_six_current_endpoint_false {k : Nat} (hk : 5 ≤ k) (hmod : k % 3 = 1)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = 6)
    (hf : 3 * k ^ 2 + 7 * k + (2 * k + 1) / 3 ≤ F.card) : False := by
  obtain ⟨Z, hZ, hsize⟩ := current_endpoint_deep_singleton hk hmod F hacyc hf hb
  exact current_endpoint_singleton_false hk hmod F hacyc hf hb Z hZ hsize

/-- The boundary-six branch saves one at the current residue-one endpoint. -/
theorem boundary_six_card_le {k : Nat} (hk : 5 ≤ k) (hmod : k % 3 = 1)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = 6) :
    F.card ≤ 3 * k ^ 2 + 7 * k + (2 * k) / 3 := by
  by_contra hf
  apply boundary_six_current_endpoint_false hk hmod F hacyc hb
  omega

end GridGraphs.BoundarySix.Connected
