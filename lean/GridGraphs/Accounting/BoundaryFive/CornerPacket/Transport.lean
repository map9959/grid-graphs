import GridGraphs.Accounting.BoundaryFive.Symmetry

/-! # Transport of the actual boundary-five profile

The component counts are transported by graph isomorphisms. The exact forest
ledger then transports complementary boundary deficiency, without normalizing
any of the remaining holes.
-/

namespace GridGraphs.BoundaryFive.CornerPacket

open Finset SimpleGraph

/-- A square graph isometry preserves size, feasibility, both component counts,
and complementary boundary deficiency for its exact pullback. -/
theorem isometry_pullback_profile {n : Nat}
    (F F' : Finset (GridVertex n n)) (e : gridGraph n n ≃g gridGraph n n)
    (hmem : ∀ v, v ∈ F' ↔ e v ∈ F)
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic) :
    F'.card = F.card ∧
    (forcedEdgeGraph (gridGraph n n) (↑F' : Set _)).IsAcyclic ∧
    Fintype.card ((gridGraph n n).induce (↑F' : Set _)).ConnectedComponent =
      Fintype.card ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent ∧
    Fintype.card (forcedEdgeGraph (gridGraph n n) (↑F' : Set _)).ConnectedComponent =
      Fintype.card (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).ConnectedComponent ∧
    boundaryDeficiencySum n n (univ \ F') = boundaryDeficiencySum n n (univ \ F) := by
  classical
  let ef : forcedEdgeGraph (gridGraph n n) (↑F' : Set _) ≃g
      forcedEdgeGraph (gridGraph n n) (↑F : Set _) :=
    { e.toEquiv with
      map_rel_iff' := by
        intro v w
        change ((gridGraph n n).Adj (e v) (e w) ∧ (e v ∈ F ∨ e w ∈ F)) ↔
          ((gridGraph n n).Adj v w ∧ (v ∈ F' ∨ w ∈ F'))
        rw [e.map_rel_iff, ← hmem, ← hmem] }
  let ei : ((gridGraph n n).induce (↑F' : Set _)) ≃g
      ((gridGraph n n).induce (↑F : Set _)) :=
    { toFun := fun v => ⟨e v.1, (hmem v.1).mp v.2⟩
      invFun := fun v => ⟨e.symm v.1, (hmem _).mpr (by rw [e.apply_symm_apply]; exact v.2)⟩
      left_inv := by intro v; apply Subtype.ext; exact e.symm_apply_apply v.1
      right_inv := by intro v; apply Subtype.ext; exact e.apply_symm_apply v.1
      map_rel_iff' := by intro v w; exact e.map_rel_iff }
  have hcard : F'.card = F.card := by
    simpa using Fintype.card_congr ei.toEquiv
  have hac := hacyc.comap ef.toHom ef.injective
  have hr := Fintype.card_congr ei.connectedComponentEquiv
  have hc := Fintype.card_congr ef.connectedComponentEquiv
  refine ⟨hcard, hac, hr, hc, ?_⟩
  have hL := grid_component_reduction F hacyc
  have hL' := grid_component_reduction F' hac
  have hb := boundaryDeficiencySum_add_compl n n F
  have hb' := boundaryDeficiencySum_add_compl n n F'
  rw [hcard, hr, hc] at hL'
  omega

/-- Gap-only normalization now preserves the original actual profile. -/
theorem exists_top_gap_pullback_profile {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 5) :
    ∃ F' : Finset (GridVertex n n), F'.card = F.card ∧
      (forcedEdgeGraph (gridGraph n n) (↑F' : Set _)).IsAcyclic ∧
      Fintype.card ((gridGraph n n).induce (↑F' : Set _)).ConnectedComponent =
        Fintype.card ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent ∧
      Fintype.card (forcedEdgeGraph (gridGraph n n) (↑F' : Set _)).ConnectedComponent =
        Fintype.card (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).ConnectedComponent ∧
      boundaryDeficiencySum n n (univ \ F') = 5 ∧
      (⟨0, by omega⟩, ⟨1, by omega⟩) ∉ F' ∧
      (⟨0, by omega⟩, ⟨2, by omega⟩) ∉ F' := by
  obtain ⟨F', e, hmem, ha, hh⟩ := exists_top_gap_pullback_isometry hn F hacyc hb
  obtain ⟨hcard, hac, hr, hc, hb'⟩ := isometry_pullback_profile F F' e hmem hacyc
  exact ⟨F', hcard, hac, hr, hc, hb'.trans hb, ha, hh⟩

end GridGraphs.BoundaryFive.CornerPacket
