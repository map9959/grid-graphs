import GridGraphs.Accounting.CarrierLayerBound
import GridGraphs.Geometry.CarrierPacking

namespace GridGraphs.CarrierLayers

open Finset SimpleGraph

/-- The four closed outer sides, without a routing-layer dependency. -/
def OnSide {n : Nat} (s : Fin 4) (v : GridVertex n n) : Prop :=
  (s.val = 0 ∧ v.1.val = 0) ∨ (s.val = 1 ∧ v.1.val + 1 = n) ∨
  (s.val = 2 ∧ v.2.val = 0) ∨ (s.val = 3 ∧ v.2.val + 1 = n)

/-- A side with its two corners removed. -/
def OnOpenSide {n : Nat} (s : Fin 4) (v : GridVertex n n) : Prop :=
  OnSide s v ∧
    ((s.val < 2 ∧ 0 < v.2.val ∧ v.2.val + 1 < n) ∨
     (2 ≤ s.val ∧ 0 < v.1.val ∧ v.1.val + 1 < n))

theorem openSide_boundary {n : Nat} {s : Fin 4} {v : GridVertex n n}
    (h : OnOpenSide s v) : IsGridBoundary v := by
  unfold OnOpenSide OnSide IsGridBoundary at *
  omega

theorem openSide_unique {n : Nat} {s t : Fin 4} {v : GridVertex n n}
    (hs : OnOpenSide s v) (ht : OnSide t v) : s = t := by
  apply Fin.ext
  unfold OnOpenSide OnSide at *
  omega

/-- Interval filling prevents an interior straight carrier from reaching both
opposite boundary sides. Consequently every pure carrier lies on one side. -/
theorem pure_carrier_on_side {n : Nat} (hn : 3 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (C : ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent)
    (hC : C ∈ pureBoundaryCarriers F) :
    ∃ s : Fin 4, ∀ v ∈ C.supp, OnSide s v.val := by
  classical
  have hb := (mem_filter.mp hC).2
  obtain ⟨u, hu⟩ := C.nonempty_supp
  rcases induced_forced_connectedComponent_straight hacyc C with ⟨r, hr⟩ | ⟨c, hc⟩
  · by_cases h0 : r.val = 0
    · exact ⟨0, fun v hv => Or.inl ⟨rfl, by rw [hr v hv]; exact h0⟩⟩
    by_cases hlast : r.val + 1 = n
    · exact ⟨1, fun v hv => Or.inr (Or.inl ⟨rfl, by rw [hr v hv]; exact hlast⟩)⟩
    have hcols : ∀ v ∈ C.supp, v.val.2 = u.val.2 := by
      intro v hv
      by_contra he
      have hbu := hb u hu
      have hbv := hb v hv
      have hru := congrArg Fin.val (hr u hu)
      have hrv := congrArg Fin.val (hr v hv)
      have hne : v.val.2.val ≠ u.val.2.val := fun h => he (Fin.ext h)
      have hbetween : (u.val.2.val ≤ 1 ∧ 1 ≤ v.val.2.val) ∨
          (v.val.2.val ≤ 1 ∧ 1 ≤ u.val.2.val) := by
        unfold IsGridBoundary at hbu hbv
        omega
      obtain ⟨hz, hzC⟩ := induced_forced_connectedComponent_horizontal_interval
        hacyc C hu hv ((hr u hu).trans (hr v hv).symm) ⟨1, by omega⟩ hbetween
      have hbad := hb ⟨_, hz⟩ hzC
      dsimp [IsGridBoundary] at hbad
      omega
    have hbu := hb u hu
    have hru := congrArg Fin.val (hr u hu)
    have hend : u.val.2.val = 0 ∨ u.val.2.val + 1 = n := by
      unfold IsGridBoundary at hbu
      omega
    rcases hend with hend | hend
    · exact ⟨2, fun v hv => Or.inr (Or.inr (Or.inl
        ⟨rfl, by rw [hcols v hv]; exact hend⟩))⟩
    · exact ⟨3, fun v hv => Or.inr (Or.inr (Or.inr
        ⟨rfl, by rw [hcols v hv]; exact hend⟩))⟩
  · by_cases h0 : c.val = 0
    · exact ⟨2, fun v hv => Or.inr (Or.inr (Or.inl
        ⟨rfl, by rw [hc v hv]; exact h0⟩))⟩
    by_cases hlast : c.val + 1 = n
    · exact ⟨3, fun v hv => Or.inr (Or.inr (Or.inr
        ⟨rfl, by rw [hc v hv]; exact hlast⟩))⟩
    have hrows : ∀ v ∈ C.supp, v.val.1 = u.val.1 := by
      intro v hv
      by_contra he
      have hbu := hb u hu
      have hbv := hb v hv
      have hcu := congrArg Fin.val (hc u hu)
      have hcv := congrArg Fin.val (hc v hv)
      have hne : v.val.1.val ≠ u.val.1.val := fun h => he (Fin.ext h)
      have hbetween : (u.val.1.val ≤ 1 ∧ 1 ≤ v.val.1.val) ∨
          (v.val.1.val ≤ 1 ∧ 1 ≤ u.val.1.val) := by
        unfold IsGridBoundary at hbu hbv
        omega
      obtain ⟨hz, hzC⟩ := induced_forced_connectedComponent_vertical_interval
        hacyc C hu hv ((hc u hu).trans (hc v hv).symm) ⟨1, by omega⟩ hbetween
      have hbad := hb ⟨_, hz⟩ hzC
      dsimp [IsGridBoundary] at hbad
      omega
    have hbu := hb u hu
    have hcu := congrArg Fin.val (hc u hu)
    have hend : u.val.1.val = 0 ∨ u.val.1.val + 1 = n := by
      unfold IsGridBoundary at hbu
      omega
    rcases hend with hend | hend
    · exact ⟨0, fun v hv => Or.inl ⟨rfl, by rw [hrows v hv]; exact hend⟩⟩
    · exact ⟨1, fun v hv => Or.inr (Or.inl
        ⟨rfl, by rw [hrows v hv]; exact hend⟩)⟩

/-- At most three pure carriers leave some open outer side uncovered. -/
theorem exists_side_without_pure_carrier {n : Nat} (hn : 3 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hp : (pureBoundaryCarriers F).card ≤ 3) :
    ∃ s : Fin 4, ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp,
      ¬ OnOpenSide s v.val := by
  classical
  let f : pureBoundaryCarriers F → Fin 4 := fun C =>
    (pure_carrier_on_side hn F hacyc C.val C.property).choose
  have hsmall : (univ.image f).card < (univ : Finset (Fin 4)).card := by
    have h := card_image_le (s := univ) (f := f)
    simp only [card_univ, Fintype.card_coe, Fintype.card_fin] at h ⊢
    omega
  obtain ⟨s, _, hs⟩ := exists_mem_notMem_of_card_lt_card hsmall
  refine ⟨s, ?_⟩
  intro C hC v hv hvs
  have he : s = f ⟨C, hC⟩ := openSide_unique hvs
    ((pure_carrier_on_side hn F hacyc C hC).choose_spec v hv)
  exact hs (he ▸ mem_image.mpr ⟨⟨C, hC⟩, mem_univ _, rfl⟩)

end GridGraphs.CarrierLayers
