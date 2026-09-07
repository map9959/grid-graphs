import GridGraphs.Accounting.BoundaryFive.Rootless.GapRoot
import GridGraphs.Accounting.BoundaryFive.Rootless.DeepRooting
import GridGraphs.Accounting.BoundaryFive.Rootless.RootedLedger
import GridGraphs.Accounting.BoundaryFive.CornerPacket.Transport

/-!
# Ambient boundary-five two-component endpoint exclusion

The oriented result derives z in U from the actual singleton obstruction,
then uses the full and annulus component budgets with the isolated w. The
deep ledger determines q=k from the exact deep mass, without a separate
induced-component decomposition. The final theorem transports only the gap;
no canonical choices at the other three corners are made.
-/

namespace GridGraphs.BoundaryFive.Rootless

open Finset SimpleGraph

theorem top_gap_boundary_five_two_component_endpoint_false {k : Nat}
    (hk : 5 ≤ k) (hmod : k % 3 = 1)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2)) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = 5)
    (hc : Fintype.card (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).ConnectedComponent = 2)
    (hr : Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).ConnectedComponent = k + 4)
    (hf : F.card = 3 * k ^ 2 + 7 * k + (2 * k + 1) / 3)
    (ha : (⟨0, by omega⟩, ⟨1, by omega⟩) ∉ F)
    (hh : (⟨0, by omega⟩, ⟨2, by omega⟩) ∉ F) : False := by
  have hk7 : 7 ≤ k := by omega
  have hz := top_gap_endpoint_corner_notMem hk7 hmod F hacyc hb hr hf.ge ha hh
  have hdacyc := deepSelected_acyclic F hacyc
  have hex := top_hole_deep_rooted (by omega) F hacyc hb hc hh hz
  have hroot := top_hole_deep_unique_roots (by omega) F hacyc hb hh hz
  have hcorners := top_hole_deep_corners_notMem (by omega) F hacyc hb hh hz
  have hmass := deepSelected_card_add_boundary (by omega) F hacyc hb
  have hledger := rooted_deep_ledger (by omega) (deepSelected F) hdacyc hex hroot hcorners
  have he : 3 * ((2 * k + 1) / 3) = 2 * k + 1 := by omega
  have ho : 4 * (3 * k + 2) - 9 + 1 = 12 * k := by omega
  have hm : 3 * k + 2 - 4 + 2 = 3 * k := by omega
  have hq : Fintype.card ((gridGraph (3 * k + 2 - 4) (3 * k + 2 - 4)).induce
      (↑(deepSelected F) : Set _)).ConnectedComponent = k := by nlinarith
  apply rooted_deep_endpoint_false hk7 hm (deepSelected F) hdacyc hex hroot hcorners hq
  rwa [hq] at hledger

/-- The ACTUAL ambient current endpoint cannot have profile (r,c,b)=(k+4,2,5).
This theorem has no gap-position, deep-root, corner-U, normalization, rod,
packet, or connectivity hypothesis beyond the stated ambient profile. -/
theorem boundary_five_two_component_endpoint_false {k : Nat}
    (hk : 5 ≤ k) (hmod : k % 3 = 1)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2)) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = 5)
    (hc : Fintype.card (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).ConnectedComponent = 2)
    (hr : Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
      (↑F : Set _)).ConnectedComponent = k + 4)
    (hf : F.card = 3 * k ^ 2 + 7 * k + (2 * k + 1) / 3) : False := by
  obtain ⟨F', hcard, hac, hr', hc', hb', ha, hh⟩ :=
    CornerPacket.exists_top_gap_pullback_profile (by omega) F hacyc hb
  exact top_gap_boundary_five_two_component_endpoint_false hk hmod F' hac hb'
    (hc'.trans hc) (hr'.trans hr) (hcard.trans hf) ha hh

end GridGraphs.BoundaryFive.Rootless
