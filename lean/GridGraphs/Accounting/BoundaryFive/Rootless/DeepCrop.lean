import GridGraphs.Accounting.BoundaryFive.Rootless.AnnulusPeeling

/-! # The actual twice-cropped square and its physical crossing edges -/

namespace GridGraphs.BoundaryFive.Rootless

open Finset SimpleGraph

attribute [local instance] Classical.propDecidable

def deepEmbed (n : Nat) (v : GridVertex (n - 4) (n - 4)) : GridVertex n n :=
  (⟨v.1.val + 2, by have := v.1.isLt; omega⟩,
   ⟨v.2.val + 2, by have := v.2.isLt; omega⟩)

def deepEquiv (n : Nat) : GridVertex (n - 4) (n - 4) ≃
    {v : GridVertex n n // ¬ CarrierLayers.Annulus.Mem v} where
  toFun v := ⟨deepEmbed n v, by
    have := v.1.isLt; have := v.2.isLt
    simp only [deepEmbed, CarrierLayers.Annulus.Mem]
    omega⟩
  invFun v := (⟨v.1.1.val - 2, by have := v.2; dsimp [CarrierLayers.Annulus.Mem] at this; omega⟩,
    ⟨v.1.2.val - 2, by have := v.2; dsimp [CarrierLayers.Annulus.Mem] at this; omega⟩)
  left_inv v := by
    apply Prod.ext <;> apply Fin.ext <;> simp [deepEmbed]
  right_inv v := by
    apply Subtype.ext
    have := v.2
    dsimp [CarrierLayers.Annulus.Mem] at this
    apply Prod.ext <;> apply Fin.ext <;> dsimp [deepEmbed] <;> omega

theorem deepEmbed_adj (n : Nat) (v w : GridVertex (n - 4) (n - 4)) :
    (gridGraph n n).Adj (deepEmbed n v) (deepEmbed n w) ↔
      (gridGraph (n - 4) (n - 4)).Adj v w := by
  simp only [gridGraph, adjacent, deepEmbed, Fin.ext_iff]
  omega

noncomputable def deepSelected {n : Nat} (F : Finset (GridVertex n n)) :
    Finset (GridVertex (n - 4) (n - 4)) := univ.filter (fun v => deepEmbed n v ∈ F)

@[simp] theorem mem_deepSelected {n : Nat} (F : Finset (GridVertex n n))
    (v : GridVertex (n - 4) (n - 4)) : v ∈ deepSelected F ↔ deepEmbed n v ∈ F := by
  classical
  simp [deepSelected]

noncomputable def deepForcedIso {n : Nat} (F : Finset (GridVertex n n)) :
    forcedEdgeGraph (gridGraph (n - 4) (n - 4)) (↑(deepSelected F) : Set _) ≃g
      ((forcedEdgeGraph (gridGraph n n) (↑F : Set _)).induce
        {v | ¬ CarrierLayers.Annulus.Mem v}) :=
  { deepEquiv n with
    map_rel_iff' := by
      intro v w
      change ((gridGraph n n).Adj (deepEmbed n v) (deepEmbed n w) ∧
        (deepEmbed n v ∈ F ∨ deepEmbed n w ∈ F)) ↔ _
      rw [deepEmbed_adj]
      simp only [forcedEdgeGraph, mem_coe, mem_deepSelected] }

theorem deepSelected_acyclic {n : Nat} (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic) :
    (forcedEdgeGraph (gridGraph (n - 4) (n - 4)) (↑(deepSelected F) : Set _)).IsAcyclic := by
  have h := hacyc.comap (Embedding.induce (G := forcedEdgeGraph (gridGraph n n) (↑F : Set _))
    {v | ¬ CarrierLayers.Annulus.Mem v}).toHom Subtype.val_injective
  exact h.comap (deepForcedIso F).toHom (deepForcedIso F).injective

theorem deepSelected_card {n : Nat} (F : Finset (GridVertex n n)) :
    (deepSelected F).card = (F.filter (fun v => ¬ CarrierLayers.Annulus.Mem v)).card := by
  classical
  apply card_bij (fun v _ => deepEmbed n v)
  · intro v hv
    exact mem_filter.mpr ⟨(mem_deepSelected F v).mp hv, (deepEquiv n v).2⟩
  · intro v _ w _ he
    exact (deepEquiv n).injective (Subtype.ext he)
  · intro v hv
    let x := (deepEquiv n).symm ⟨v, (mem_filter.mp hv).2⟩
    have he : deepEmbed n x = v := congrArg Subtype.val ((deepEquiv n).apply_symm_apply _)
    exact ⟨x, (mem_deepSelected F x).mpr (he ▸ (mem_filter.mp hv).1), he⟩

theorem deepSelected_card_add_boundary {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 5) :
    (deepSelected F).card + (4 * n - 9) = F.card := by
  classical
  have hA := (CornerPacket.boundary_five_annulus_occupancy hn F hacyc hb).2.2
  rw [CarrierLayers.Annulus.selected_card] at hA
  have h := card_filter_add_card_filter_not (s := F) (p := CarrierLayers.Annulus.Mem)
  rw [deepSelected_card]
  omega

/-- On every physical crossing, the outer endpoint is next-ring U and the
inner endpoint is a preserved vertex of the deep boundary. -/
theorem deep_crossing_root {n : Nat} (hn : 9 ≤ n) (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 5)
    (v : GridVertex (n - 4) (n - 4)) (a : CarrierLayers.Annulus.Vertex n)
    (he : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).Adj (deepEmbed n v) a.1) :
    v ∈ deepSelected F ∧ IsGridBoundary v := by
  have ha := a.2
  have hadj := he.1
  simp only [gridGraph, adjacent, Fin.ext_iff, deepEmbed] at hadj
  dsimp [CarrierLayers.Annulus.Mem] at ha
  have hv1 := v.1.isLt
  have hv2 := v.2.isLt
  have haring : IsNextRing a.1 := by dsimp [IsNextRing]; omega
  have haU := next_ring_notMem hn F hacyc hb a.1 haring
  refine ⟨(mem_deepSelected F v).mpr (he.2.resolve_right haU), ?_⟩
  dsimp [IsGridBoundary]
  omega

/-- Every deep boundary F vertex has an actual outward forced spoke. -/
theorem deep_boundary_spoke {n : Nat} (hn : 9 ≤ n) (F : Finset (GridVertex n n))
    (v : GridVertex (n - 4) (n - 4)) (hv : v ∈ deepSelected F) (hb : IsGridBoundary v) :
    ∃ a : CarrierLayers.Annulus.Vertex n,
      (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).Adj (deepEmbed n v) a.1 := by
  have hvF := (mem_deepSelected F v).mp hv
  have hv1 := v.1.isLt
  have hv2 := v.2.isLt
  rcases hb with hr | hr | hc | hc
  · refine ⟨⟨(⟨1, by omega⟩, (deepEmbed n v).2), by simp [CarrierLayers.Annulus.Mem]⟩,
      ?_, Or.inl hvF⟩
    simp [gridGraph, adjacent, deepEmbed, hr]
  · refine ⟨⟨(⟨n - 2, by omega⟩, (deepEmbed n v).2), by
      dsimp [CarrierLayers.Annulus.Mem]; omega⟩, ?_, Or.inl hvF⟩
    right
    refine ⟨rfl, Or.inl ?_⟩
    change v.1.val + 2 + 1 = n - 2
    omega
  · refine ⟨⟨((deepEmbed n v).1, ⟨1, by omega⟩), by simp [CarrierLayers.Annulus.Mem]⟩,
      ?_, Or.inl hvF⟩
    simp [gridGraph, adjacent, deepEmbed, hc]
  · refine ⟨⟨((deepEmbed n v).1, ⟨n - 2, by omega⟩), by
      dsimp [CarrierLayers.Annulus.Mem]; omega⟩, ?_, Or.inl hvF⟩
    left
    refine ⟨rfl, Or.inl ?_⟩
    change v.2.val + 2 + 1 = n - 2
    omega

/-- A deep corner F vertex has two DISTINCT outward forced spokes. -/
theorem deep_corner_two_spokes {n : Nat} (hn : 9 ≤ n) (F : Finset (GridVertex n n))
    (v : GridVertex (n - 4) (n - 4)) (hv : v ∈ deepSelected F) (hc : BoundarySix.Corner v) :
    ∃ a b : CarrierLayers.Annulus.Vertex n, a.1 ≠ b.1 ∧
      (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).Adj (deepEmbed n v) a.1 ∧
      (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).Adj (deepEmbed n v) b.1 := by
  classical
  have hvF := (mem_deepSelected F v).mp hv
  have hv1 := v.1.isLt
  have hv2 := v.2.isLt
  let r : Fin n := ⟨if v.1.val = 0 then 1 else n - 2, by split_ifs <;> omega⟩
  let c : Fin n := ⟨if v.2.val = 0 then 1 else n - 2, by split_ifs <;> omega⟩
  have hr : r.val = 1 ∨ r.val = n - 2 := by dsimp [r]; split_ifs <;> simp
  have hcol : c.val = 1 ∨ c.val = n - 2 := by dsimp [c]; split_ifs <;> simp
  let a : CarrierLayers.Annulus.Vertex n := ⟨(r, (deepEmbed n v).2), by
    dsimp [CarrierLayers.Annulus.Mem]; omega⟩
  let b : CarrierLayers.Annulus.Vertex n := ⟨((deepEmbed n v).1, c), by
    dsimp [CarrierLayers.Annulus.Mem]; omega⟩
  refine ⟨a, b, ?_, ⟨?_, Or.inl hvF⟩, ⟨?_, Or.inl hvF⟩⟩
  · intro he
    have h := congrArg (fun x : GridVertex n n => x.1.val) he
    dsimp [a, b, deepEmbed] at h
    omega
  · right
    refine ⟨rfl, ?_⟩
    change v.1.val + 2 + 1 = r.val ∨ r.val + 1 = v.1.val + 2
    dsimp [r]
    dsimp [BoundarySix.Corner] at hc
    split_ifs <;> omega
  · left
    refine ⟨rfl, ?_⟩
    change v.2.val + 2 + 1 = c.val ∨ c.val + 1 = v.2.val + 2
    dsimp [c]
    dsimp [BoundarySix.Corner] at hc
    split_ifs <;> omega

end GridGraphs.BoundaryFive.Rootless
