import GridGraphs.Accounting.CarrierLayers.Annulus.Geometry
import GridGraphs.Accounting.CarrierLengthBound

/-! # Global two-layer cap

No boundary-deficiency or side-coverage hypothesis is used. The component
length bound is imported from the full grid, not inferred from annulus
acyclicity alone.
-/

namespace GridGraphs.CarrierLayers.Annulus

open Finset SimpleGraph

attribute [local instance] Classical.propDecidable

noncomputable def selected {n : Nat} (F : Finset (GridVertex n n)) : Finset (Vertex n) :=
  univ.filter (fun v => v.1 ∈ F)

theorem selected_card {n : Nat} (F : Finset (GridVertex n n)) :
    (selected F).card = (F.filter Mem).card := by
  have he : (selected F).map ⟨Subtype.val, Subtype.val_injective⟩ = F.filter Mem := by
    ext v
    simp only [selected, mem_map, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨hw, w.2⟩
    · rintro ⟨hv, ha⟩
      exact ⟨⟨v, ha⟩, hv, rfl⟩
  simpa only [card_map] using congrArg Finset.card he

theorem selected_card_layers {n : Nat} (hn : 5 ≤ n) (F : Finset (GridVertex n n)) :
    (selected F).card = (F.filter IsGridBoundary).card + (F.filter IsNextRing).card := by
  rw [selected_card]
  have he : F.filter Mem = F.filter IsGridBoundary ∪ F.filter IsNextRing := by
    ext v
    simp only [mem_filter, mem_union, mem_iff_layers hn]
    tauto
  rw [he, card_union_of_disjoint]
  apply Finset.disjoint_left.mpr
  intro v hv hw
  have hb := (mem_filter.mp hv).2
  have hi := (mem_filter.mp hw).2
  dsimp [IsGridBoundary] at hb
  dsimp [IsNextRing] at hi
  omega

theorem selected_isAcyclic {n : Nat} (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic) :
    (forcedEdgeGraph (graph n) (↑(selected F) : Set _)).IsAcyclic := by
  let f : forcedEdgeGraph (graph n) (↑(selected F) : Set _) →g
      forcedEdgeGraph (gridGraph n n) (↑F : Set _) :=
    { toFun := Subtype.val
      map_rel' := by
        intro v w h
        refine ⟨h.1, ?_⟩
        simpa only [selected, mem_filter, mem_univ, true_and, mem_coe] using h.2 }
  exact hacyc.comap f Subtype.val_injective

/-- Exact additive cubic ledger, with both corner corrections. -/
theorem cubic_ledger {n : Nat} (hn : 5 ≤ n) (S : Finset (Vertex n))
    (hacyc : (forcedEdgeGraph (graph n) (↑S : Set _)).IsAcyclic) :
    2 * S.card + Fintype.card ((graph n).induce (↑S : Set _)).ConnectedComponent +
      Fintype.card (forcedEdgeGraph (graph n) (↑S : Set _)).ConnectedComponent +
      (S.filter (fun v => InnerCorner v.1)).card =
    Fintype.card (Vertex n) + (S.filter (fun v => OuterCorner v.1)).card := by
  have hd : (∑ v ∈ S, (graph n).degree v) +
      (S.filter (fun v => OuterCorner v.1)).card =
      3 * S.card + (S.filter (fun v => InnerCorner v.1)).card := by
    have hsum := sum_congr (s₁ := S) rfl (fun v _ => degree_formula hn v)
    simpa only [sum_add_distrib, sum_boole, sum_const, smul_eq_mul, mul_comm,
      Nat.cast_id] using hsum
  have hh := sum_degrees_finset_eq_forced_add_induced (graph n) S
  have hf := forcedEdgeGraph_forest_ledger (graph n) S hacyc
  have hi := induce_finset_forest_ledger (graph n) S hacyc
  omega

theorem selected_length_bound {n : Nat} (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic) :
    (selected F).card ≤ n *
      Fintype.card ((graph n).induce (↑(selected F) : Set _)).ConnectedComponent := by
  let e : ((graph n).induce (↑(selected F) : Set _)) ≃g
      ((gridGraph n n).induce (↑(F.filter Mem) : Set _)) :=
    { toFun := fun v => ⟨v.1.1, mem_filter.mpr
        ⟨(mem_filter.mp v.2).2, v.1.2⟩⟩
      invFun := fun v => ⟨⟨v.1, (mem_filter.mp v.2).2⟩,
        mem_filter.mpr ⟨mem_univ _, (mem_filter.mp v.2).1⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := by intros; rfl }
  have hc := Fintype.card_congr e.connectedComponentEquiv
  have hs : (forcedEdgeGraph (gridGraph n n) (↑(F.filter Mem) : Set _)).IsAcyclic :=
    hacyc.anti (forcedEdgeGraph_mono _ (by
      intro v hv
      exact (mem_filter.mp hv).1))
  rw [selected_card, hc]
  exact forced_card_le_side_mul_components (F.filter Mem) hs

/-- The global cap `B + E <= 4n - 9` in additive form. -/
theorem selected_card_add_nine_le {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic) :
    (selected F).card + 9 ≤ 4 * n := by
  have hl := cubic_ledger (by omega : 5 ≤ n) (selected F) (selected_isAcyclic F hacyc)
  have ha := card_vertex (by omega : 5 ≤ n)
  have ho := outerCorner_card_le_four (selected F)
  have hs := selected_length_bound F hacyc
  have hc : 1 ≤ Fintype.card
      (forcedEdgeGraph (graph n) (↑(selected F) : Set _)).ConnectedComponent := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨(forcedEdgeGraph (graph n) (↑(selected F) : Set _)).connectedComponentMk
      ⟨(⟨0, by omega⟩, ⟨0, by omega⟩), Or.inl (by change 0 < 2; omega)⟩⟩
  by_contra h
  have hr : 4 ≤ Fintype.card
      ((graph n).induce (↑(selected F) : Set _)).ConnectedComponent := by
    by_contra hr
    have hm := Nat.mul_le_mul_left n (show Fintype.card
      ((graph n).induce (↑(selected F) : Set _)).ConnectedComponent ≤ 3 by omega)
    omega
  omega

/-- Paper endpoint, globally and without a small-boundary assumption. -/
theorem boundary_add_nextRing_card_le {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic) :
    (F.filter IsGridBoundary).card + (F.filter IsNextRing).card ≤ 4 * n - 9 := by
  have h := selected_card_add_nine_le hn F hacyc
  rw [selected_card_layers (by omega)] at h
  omega

/-- The two-layer loss is at least five. -/
theorem five_le_loss {n : Nat} (hn : 9 ≤ n) (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic) :
    5 ≤ (4 * n - 4) - (F.filter IsGridBoundary).card -
      (F.filter IsNextRing).card := by
  have h := boundary_add_nextRing_card_le hn F hacyc
  omega

/-- The annulus component budget needed by a future physical-bridge argument.
This statement does not assert that a carrier contact graph is a forest. -/
theorem component_budget {n : Nat} (hn : 9 ≤ n) (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic) :
    Fintype.card ((graph n).induce (↑(selected F) : Set _)).ConnectedComponent +
      Fintype.card (forcedEdgeGraph (graph n) (↑(selected F) : Set _)).ConnectedComponent + 4 ≤
      2 * ((4 * n - 4) - (F.filter IsGridBoundary).card -
        (F.filter IsNextRing).card) := by
  have hl := cubic_ledger (by omega : 5 ≤ n) (selected F) (selected_isAcyclic F hacyc)
  have ha := card_vertex (by omega : 5 ≤ n)
  have ho := outerCorner_card_le_four (selected F)
  have hcap := selected_card_add_nine_le hn F hacyc
  have he := selected_card_layers (by omega : 5 ≤ n) F
  omega

end GridGraphs.CarrierLayers.Annulus
