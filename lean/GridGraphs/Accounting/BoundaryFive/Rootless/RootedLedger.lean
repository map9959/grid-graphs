import GridGraphs.Accounting.BoundaryFive.Rootless.CornerRoots

/-! # Exact rooted deep ledger

Each forced component corresponds to its unique boundary F root. With U
corners, the boundary deficiency of F is exactly the number of these roots,
so the forced-component term cancels from the grid ledger.
-/

namespace GridGraphs.BoundaryFive.Rootless

open Finset SimpleGraph

theorem rooted_deep_ledger {m : Nat} (hm : 2 ≤ m)
    (F : Finset (GridVertex m m))
    (hacyc : (forcedEdgeGraph (gridGraph m m) (↑F : Set _)).IsAcyclic)
    (hex : BoundaryRooted (m := m) (↑F : Set _))
    (hroot : UniqueBoundaryRoots (m := m) (↑F : Set _))
    (hcorners : ∀ z, BoundarySix.Corner z → z ∉ F) :
    3 * F.card + Fintype.card ((gridGraph m m).induce (↑F : Set _)).ConnectedComponent = m * m := by
  classical
  let H := forcedEdgeGraph (gridGraph m m) (↑F : Set _)
  let B := F.filter IsGridBoundary
  let f : B → H.ConnectedComponent := fun u => H.connectedComponentMk u.1
  have hi : Function.Injective f := by
    intro u v he
    have hu := mem_filter.mp u.2
    have hv := mem_filter.mp v.2
    exact Subtype.ext (hroot u.1 hu.1 v.1 hv.1 hu.2 hv.2 (ConnectedComponent.eq.mp he))
  have hs : Function.Surjective f := by
    intro C
    obtain ⟨v, hv⟩ := C.nonempty_supp
    obtain ⟨u, hu, hub, hreach⟩ := hex v
    refine ⟨⟨u, mem_filter.mpr ⟨hu, hub⟩⟩, ?_⟩
    have he : H.connectedComponentMk v = H.connectedComponentMk u := ConnectedComponent.eq.mpr hreach
    exact he.symm.trans hv
  have hc : Fintype.card H.ConnectedComponent = B.card := by
    simpa using (Fintype.card_congr (Equiv.ofBijective f ⟨hi, hs⟩)).symm
  have hdef : boundaryDeficiencySum m m F = B.card := by
    rw [boundaryDeficiencySum]
    change (∑ v ∈ F, gridBoundaryDeficiency m m v) = (F.filter IsGridBoundary).card
    rw [card_filter]
    apply sum_congr rfl
    intro v hv
    have hnc : ¬ BoundarySix.Corner v := fun h => hcorners v h hv
    by_cases hb : IsGridBoundary v
    · have hd : (gridGraph m m).degree v = 3 := gridGraph_degree_border hm hm v (by
        simp only [BoundarySix.Corner] at hnc
        simp only [IsGridBoundary] at hb
        tauto)
      simp [gridBoundaryDeficiency, hd, hb]
    · have hd : (gridGraph m m).degree v = 4 := gridGraph_degree_interior hm hm v
        (by dsimp [IsGridBoundary] at hb; tauto) (by dsimp [IsGridBoundary] at hb; tauto)
      simp [gridBoundaryDeficiency, hd, hb]
  have h := grid_component_reduction F hacyc
  change 3 * F.card + Fintype.card ((gridGraph m m).induce (↑F : Set _)).ConnectedComponent +
    Fintype.card H.ConnectedComponent = m * m + boundaryDeficiencySum m m F at h
  rw [hc, hdef] at h
  omega

end GridGraphs.BoundaryFive.Rootless
