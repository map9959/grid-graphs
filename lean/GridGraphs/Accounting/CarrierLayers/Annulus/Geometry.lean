import GridGraphs.Geometry.GridLayers
import GridGraphs.Accounting.ComponentReduction

/-! # The two outer layers of a square grid

The degree formula includes both sorts of corners. All component counts on
this vertex type include isolated annulus vertices.
-/

namespace GridGraphs.CarrierLayers.Annulus

open Finset SimpleGraph

attribute [local instance] Classical.propDecidable

def Mem {n : Nat} (v : GridVertex n n) : Prop :=
  v.1.val < 2 ∨ n ≤ v.1.val + 2 ∨ v.2.val < 2 ∨ n ≤ v.2.val + 2

abbrev Vertex (n : Nat) := {v : GridVertex n n // Mem v}

def graph (n : Nat) : SimpleGraph (Vertex n) := (gridGraph n n).induce Mem

def OuterCorner {n : Nat} (v : GridVertex n n) : Prop :=
  (v.1.val = 0 ∨ v.1.val + 1 = n) ∧ (v.2.val = 0 ∨ v.2.val + 1 = n)

def InnerCorner {n : Nat} (v : GridVertex n n) : Prop :=
  (v.1.val = 1 ∨ v.1.val = n - 2) ∧ (v.2.val = 1 ∨ v.2.val = n - 2)

theorem mem_iff_layers {n : Nat} (hn : 5 ≤ n) (v : GridVertex n n) :
    Mem v ↔ IsGridBoundary v ∨ IsNextRing v := by
  have := v.1.isLt
  have := v.2.isLt
  simp only [Mem, IsGridBoundary, IsNextRing]
  omega

theorem card_vertex {n : Nat} (hn : 5 ≤ n) :
    Fintype.card (Vertex n) + 16 = 8 * n := by
  classical
  let e : {v : GridVertex n n // ¬ Mem v} ≃ GridVertex (n - 4) (n - 4) :=
    { toFun := fun v =>
        (⟨v.1.1.val - 2, by have := v.2; dsimp [Mem] at this; omega⟩,
         ⟨v.1.2.val - 2, by have := v.2; dsimp [Mem] at this; omega⟩)
      invFun := fun v => ⟨(⟨v.1.val + 2, by have := v.1.isLt; omega⟩,
        ⟨v.2.val + 2, by have := v.2.isLt; omega⟩), by
          have := v.1.isLt
          have := v.2.isLt
          dsimp [Mem]
          omega⟩
      left_inv := by
        intro v
        have := v.2
        dsimp [Mem] at this
        apply Subtype.ext
        apply Prod.ext <;> apply Fin.ext <;> dsimp <;> omega
      right_inv := by
        intro v
        apply Prod.ext <;> apply Fin.ext <;> dsimp <;> omega }
  have hc := Fintype.card_congr e
  have hp := Fintype.card_subtype_compl (fun v : GridVertex n n => Mem v)
  have hle := Fintype.card_subtype_le (fun v : GridVertex n n => Mem v)
  simp only [GridVertex, Fintype.card_prod, Fintype.card_fin] at hc hp
  simp only [GridVertex, Fintype.card_prod, Fintype.card_fin] at hle
  rw [hc] at hp
  change (n - 4) * (n - 4) = n * n - Fintype.card (Vertex n) at hp
  change Fintype.card (Vertex n) ≤ n * n at hle
  have hp' : Fintype.card (Vertex n) + (n - 4) * (n - 4) = n * n := by omega
  have hs : n - 4 + 4 = n := by omega
  nlinarith

theorem degree_add_outside {n : Nat} (v : Vertex n) :
    (graph n).degree v +
      ((gridGraph n n).neighborFinset v.1 |>.filter (fun w => ¬ Mem w)).card =
      (gridGraph n n).degree v.1 := by
  classical
  have he : ((graph n).neighborFinset v).map
      ⟨Subtype.val, Subtype.val_injective⟩ =
      ((gridGraph n n).neighborFinset v.1).filter Mem := by
    ext w
    simp only [mem_map, mem_neighborFinset, mem_filter]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨hu, u.2⟩
    · rintro ⟨h, hw⟩
      exact ⟨⟨w, hw⟩, h, rfl⟩
  have hc := congrArg Finset.card he
  rw [card_map] at hc
  change ((graph n).neighborFinset v).card + _ = _
  rw [hc]
  exact card_filter_add_card_filter_not _

theorem degree_formula {n : Nat} (hn : 5 ≤ n) (v : Vertex n) :
    (graph n).degree v + (if OuterCorner v.1 then 1 else 0) =
      3 + (if InnerCorner v.1 then 1 else 0) := by
  classical
  have hr := v.1.1.isLt
  have hc := v.1.2.isLt
  have hv := v.2
  have hd := degree_add_outside v
  by_cases hb : IsGridBoundary v.1
  · have he : ((gridGraph n n).neighborFinset v.1).filter (fun w => ¬ Mem w) = ∅ := by
      ext w
      have hwr := w.1.isLt
      have hwc := w.2.isLt
      simp only [mem_filter, mem_neighborFinset, notMem_empty, iff_false]
      rintro ⟨ha, hw⟩
      change adjacent n n v.1 w at ha
      simp only [adjacent, Fin.ext_iff] at ha
      dsimp [IsGridBoundary] at hb
      dsimp [Mem] at hw
      omega
    rw [he, card_empty, Nat.add_zero] at hd
    have hi : ¬ InnerCorner v.1 := by
      dsimp [InnerCorner, IsGridBoundary] at *
      omega
    rw [hd, if_neg hi]
    by_cases ho : OuterCorner v.1
    · rw [if_pos ho, gridGraph_degree_corner (by omega) (by omega) v.1 ho.1 ho.2]
    · rw [if_neg ho, gridGraph_degree_border (by omega) (by omega) v.1]
      dsimp [OuterCorner, IsGridBoundary] at *
      omega
  · have ho : ¬ OuterCorner v.1 := by
      dsimp [OuterCorner, IsGridBoundary] at *
      omega
    have hg : (gridGraph n n).degree v.1 = 4 :=
      gridGraph_degree_interior (by omega) (by omega) v.1
        (by dsimp [IsGridBoundary] at hb; omega)
        (by dsimp [IsGridBoundary] at hb; omega)
    rw [hg] at hd
    rw [if_neg ho]
    by_cases hi : InnerCorner v.1
    · have he : ((gridGraph n n).neighborFinset v.1).filter (fun w => ¬ Mem w) = ∅ := by
        ext w
        simp only [mem_filter, mem_neighborFinset, notMem_empty, iff_false]
        rintro ⟨ha, hw⟩
        change adjacent n n v.1 w at ha
        simp only [adjacent, Fin.ext_iff] at ha
        dsimp [InnerCorner] at hi
        dsimp [Mem] at hw
        omega
      rw [he, card_empty] at hd
      rw [if_pos hi]
      omega
    · have hex : ∃ w : GridVertex n n,
          ((gridGraph n n).neighborFinset v.1).filter (fun w => ¬ Mem w) = {w} := by
        have hcoords :
            (v.1.1.val = 1 ∧ 2 ≤ v.1.2.val ∧ v.1.2.val < n - 2) ∨
            (v.1.1.val = n - 2 ∧ 2 ≤ v.1.2.val ∧ v.1.2.val < n - 2) ∨
            (v.1.2.val = 1 ∧ 2 ≤ v.1.1.val ∧ v.1.1.val < n - 2) ∨
            (v.1.2.val = n - 2 ∧ 2 ≤ v.1.1.val ∧ v.1.1.val < n - 2) := by
          dsimp [Mem] at hv
          dsimp [InnerCorner] at hi
          dsimp [IsGridBoundary] at hb
          omega
        rcases hcoords with h | h | h | h
        · refine ⟨(⟨2, by omega⟩, v.1.2), ?_⟩
          ext w
          simp only [mem_filter, mem_neighborFinset, mem_singleton]
          change (adjacent n n v.1 w ∧ ¬ Mem w) ↔ _
          simp only [adjacent, Mem, Prod.ext_iff, Fin.ext_iff]
          have := w.1.isLt
          have := w.2.isLt
          omega
        · refine ⟨(⟨n - 3, by omega⟩, v.1.2), ?_⟩
          ext w
          simp only [mem_filter, mem_neighborFinset, mem_singleton]
          change (adjacent n n v.1 w ∧ ¬ Mem w) ↔ _
          simp only [adjacent, Mem, Prod.ext_iff, Fin.ext_iff]
          have := w.1.isLt
          have := w.2.isLt
          omega
        · refine ⟨(v.1.1, ⟨2, by omega⟩), ?_⟩
          ext w
          simp only [mem_filter, mem_neighborFinset, mem_singleton]
          change (adjacent n n v.1 w ∧ ¬ Mem w) ↔ _
          simp only [adjacent, Mem, Prod.ext_iff, Fin.ext_iff]
          have := w.1.isLt
          have := w.2.isLt
          omega
        · refine ⟨(v.1.1, ⟨n - 3, by omega⟩), ?_⟩
          ext w
          simp only [mem_filter, mem_neighborFinset, mem_singleton]
          change (adjacent n n v.1 w ∧ ¬ Mem w) ↔ _
          simp only [adjacent, Mem, Prod.ext_iff, Fin.ext_iff]
          have := w.1.isLt
          have := w.2.isLt
          omega
      obtain ⟨w, hw⟩ := hex
      rw [hw, card_singleton] at hd
      rw [if_neg hi]
      omega

theorem outerCorner_card_le_four {n : Nat} (S : Finset (Vertex n)) :
    (S.filter (fun v => OuterCorner v.1)).card ≤ 4 := by
  classical
  let f : {v : Vertex n // v ∈ S.filter (fun v => OuterCorner v.1)} → Bool × Bool :=
    fun v => (decide (v.1.1.1.val = 0), decide (v.1.1.2.val = 0))
  have hi : Function.Injective f := by
    intro v w he
    have hv := (mem_filter.mp v.2).2
    have hw := (mem_filter.mp w.2).2
    have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    dsimp [f] at h1 h2
    have h1' : (v.1.1.1.val = 0) ↔ (w.1.1.1.val = 0) := by simpa using h1
    have h2' : (v.1.1.2.val = 0) ↔ (w.1.1.2.val = 0) := by simpa using h2
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext <;> dsimp [OuterCorner] at hv hw <;> omega
  have := Fintype.card_le_of_injective f hi
  simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_bool] using this

end GridGraphs.CarrierLayers.Annulus
