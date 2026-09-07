import GridGraphs.Accounting.BoundaryFive.Rootless.DeepCrop
import GridGraphs.Accounting.BoundaryFive.Rootless.Geometry

/-! # Actual deep roots from the two-component profile

Only the exceptional top hole and z in U are used here. The annulus component
budget replaces an explicit outer-tree construction. All components and all
paths are on the full physical vertex types, including isolates.
-/

namespace GridGraphs.BoundaryFive.Rootless

open Finset SimpleGraph

theorem deep_spokes_unique {n : Nat} (hn : 10 ≤ n) (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 5)
    (hh : (⟨0, by omega⟩, ⟨2, by omega⟩) ∉ F)
    (hz : (⟨2, by omega⟩, ⟨2, by omega⟩) ∉ F)
    (x y : GridVertex (n - 4) (n - 4)) (a b : CarrierLayers.Annulus.Vertex n)
    (hxy : (forcedEdgeGraph (gridGraph (n - 4) (n - 4))
      (↑(deepSelected F) : Set _)).Reachable x y)
    (hxa : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).Adj (deepEmbed n x) a.1)
    (hyb : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).Adj (deepEmbed n y) b.1) :
    x = y ∧ a.1 = b.1 := by
  let H := forcedEdgeGraph (gridGraph n n) (↑F : Set _)
  have hiso := exception_isolate (by omega) F hacyc hb hh hz
  have ha : a.1 ≠ (⟨1, by omega⟩, ⟨2, by omega⟩) := by
    intro he
    exact hiso _ (he ▸ hxa.symm)
  have hb' : b.1 ≠ (⟨1, by omega⟩, ⟨2, by omega⟩) := by
    intro he
    exact hiso _ (he ▸ hyb.symm)
  have hba := annulus_reachable_off_exception hn F hacyc hb hh b a hb' ha
  have hcross := forest_cross_edge_unique H hacyc {v | ¬ CarrierLayers.Annulus.Mem v}
    CarrierLayers.Annulus.Mem (by exact Set.disjoint_left.mpr (fun _ hx ha => hx ha))
    (deepEquiv n x) (deepEquiv n y) a b (hxy.map (deepForcedIso F).toHom) hba hxa hyb
  exact ⟨(deepEquiv n).injective (Subtype.ext hcross.1), hcross.2⟩

theorem top_hole_deep_unique_roots {n : Nat} (hn : 10 ≤ n) (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 5)
    (hh : (⟨0, by omega⟩, ⟨2, by omega⟩) ∉ F)
    (hz : (⟨2, by omega⟩, ⟨2, by omega⟩) ∉ F) :
    UniqueBoundaryRoots (m := n - 4) (↑(deepSelected F) : Set _) := by
  intro x hx y hy hxb hyb hxy
  obtain ⟨a, hxa⟩ := deep_boundary_spoke (by omega) F x hx hxb
  obtain ⟨b, hyb'⟩ := deep_boundary_spoke (by omega) F y hy hyb
  exact (deep_spokes_unique hn F hacyc hb hh hz x y a b hxy hxa hyb').1

theorem top_hole_deep_corners_notMem {n : Nat} (hn : 10 ≤ n) (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 5)
    (hh : (⟨0, by omega⟩, ⟨2, by omega⟩) ∉ F)
    (hz : (⟨2, by omega⟩, ⟨2, by omega⟩) ∉ F) :
    ∀ v, BoundarySix.Corner v → v ∉ deepSelected F := by
  intro v hc hv
  obtain ⟨a, b, hne, hxa, hxb⟩ := deep_corner_two_spokes (by omega) F v hv hc
  exact hne (deep_spokes_unique hn F hacyc hb hh hz v v a b (.rfl) hxa hxb).2

/-- Every inner forced component reaches a preserved deep-boundary root:
take the first exit of a full-graph path to an outer corner. This includes
putative inner isolates and does not assume the inner graph is connected. -/
theorem top_hole_deep_rooted {n : Nat} (hn : 10 ≤ n) (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 5)
    (hc : Fintype.card (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).ConnectedComponent = 2)
    (hh : (⟨0, by omega⟩, ⟨2, by omega⟩) ∉ F)
    (hz : (⟨2, by omega⟩, ⟨2, by omega⟩) ∉ F) :
    BoundaryRooted (m := n - 4) (↑(deepSelected F) : Set _) := by
  classical
  let H := forcedEdgeGraph (gridGraph n n) (↑F : Set _)
  let D : Set (GridVertex n n) := {v | ¬ CarrierLayers.Annulus.Mem v}
  let a : GridVertex n n := (⟨0, by omega⟩, ⟨0, by omega⟩)
  let w : GridVertex n n := (⟨1, by omega⟩, ⟨2, by omega⟩)
  have hcard : Nat.card H.ConnectedComponent ≤ 2 := by
    rw [Nat.card_eq_fintype_card]
    exact hc.le
  have hiso : ∀ v, ¬ H.Adj w v := exception_isolate (by omega) F hacyc hb hh hz
  have ha : a ≠ w := by simp [a, w, Prod.ext_iff, Fin.ext_iff]
  have haD : a ∉ D := by simp [D, a, CarrierLayers.Annulus.Mem]
  intro x
  have hx : deepEmbed n x ≠ w := by
    intro he
    have := congrArg (fun v : GridVertex n n => v.1.val) he
    dsimp [deepEmbed, w] at this
    omega
  obtain ⟨p⟩ := reachable_off_isolate H hcard w hiso (deepEmbed n x) a hx ha
  obtain ⟨u, hxu, v, hv, huv⟩ := first_exit H D p (deepEquiv n x).2 haD
  let u' := (deepForcedIso F).symm u
  have he : deepEmbed n u' = u.1 := congrArg Subtype.val ((deepForcedIso F).apply_symm_apply u)
  have hvA : CarrierLayers.Annulus.Mem v := by exact not_not.mp hv
  have hedge : H.Adj (deepEmbed n u') v := by rw [he]; exact huv
  obtain ⟨huF, hub⟩ := deep_crossing_root (by omega) F hacyc hb u' ⟨v, hvA⟩ hedge
  refine ⟨u', huF, hub, ?_⟩
  have hr := hxu.map (deepForcedIso F).symm.toHom
  change (forcedEdgeGraph (gridGraph (n - 4) (n - 4)) (↑(deepSelected F) : Set _)).Reachable
    ((deepForcedIso F).symm ((deepForcedIso F) x)) u' at hr
  simpa only [(deepForcedIso F).symm_apply_apply] using hr

end GridGraphs.BoundaryFive.Rootless
