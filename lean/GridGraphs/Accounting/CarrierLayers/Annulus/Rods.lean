import GridGraphs.Accounting.CarrierLayers.Annulus.Cap
import GridGraphs.Accounting.CarrierLayers.FourCarrier.DeepSaturation

/-! # Physical axes of full deep carriers

Fullness is the cardinality of the deep part of an actual induced component.
It implies saturation of a literal row or column, without a boundary root
or a parallelism hypothesis.
-/

namespace GridGraphs.CarrierLayers.Annulus

open Finset SimpleGraph FourCarrier
open scoped Sym2

attribute [local instance] Classical.propDecidable

abbrev Carrier {n : Nat} (F : Finset (GridVertex n n)) :=
  ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent

noncomputable def deepVertices {n : Nat} (F : Finset (GridVertex n n))
    (C : Carrier F) : Finset (GridVertex n n) :=
  (deepCarrierPart F C).map ⟨Subtype.val, Subtype.val_injective⟩

noncomputable def fullCarriers {n : Nat} (F : Finset (GridVertex n n)) :
    Finset (Carrier F) := univ.filter (fun C => (deepVertices F C).card = n - 4)

theorem deepVertices_card {n : Nat} (F : Finset (GridVertex n n)) (C : Carrier F) :
    (deepVertices F C).card = (deepCarrierPart F C).card := card_map _

theorem mem_deepVertices {n : Nat} (hn : 5 ≤ n) (F : Finset (GridVertex n n))
    (C : Carrier F) (v : GridVertex n n) :
    v ∈ deepVertices F C ↔ ∃ hv : v ∈ F,
      (⟨v, hv⟩ : (↑F : Set _)) ∈ C.supp ∧ ¬ Mem v := by
  simp only [deepVertices, mem_map, deepCarrierPart, mem_filter, Set.mem_toFinset]
  constructor
  · rintro ⟨w, ⟨hw, hb, hi⟩, rfl⟩
    exact ⟨w.2, hw, fun h => ((mem_iff_layers hn w.1).mp h).elim hb hi⟩
  · rintro ⟨hv, hs, ha⟩
    have hl : ¬ IsGridBoundary v ∧ ¬ IsNextRing v := by
      rw [mem_iff_layers hn] at ha
      exact not_or.mp ha
    exact ⟨⟨v, hv⟩, ⟨hs, hl⟩, rfl⟩

theorem deepVertices_disjoint {n : Nat} (hn : 5 ≤ n)
    (F : Finset (GridVertex n n)) {C D : Carrier F} (hCD : C ≠ D) :
    Disjoint (deepVertices F C) (deepVertices F D) := by
  apply Finset.disjoint_left.mpr
  intro v hv hw
  obtain ⟨hvF, hvC, _⟩ := (mem_deepVertices hn F C v).mp hv
  obtain ⟨_, hvD, _⟩ := (mem_deepVertices hn F D v).mp hw
  exact hCD (ConnectedComponent.eq_of_common_vertex hvC hvD)

structure Axis (n : Nat) where
  horizontal : Bool
  fixed : Fin n
  deep : 2 ≤ fixed.val ∧ fixed.val + 2 < n

def Axis.point {n : Nat} (a : Axis n) (t : Fin n) : GridVertex n n :=
  if a.horizontal then (a.fixed, t) else (t, a.fixed)

theorem Axis.point_injective {n : Nat} (a : Axis n) : Function.Injective a.point := by
  intro t u h
  cases ha : a.horizontal <;> simpa [Axis.point, ha] using h

theorem Axis.point_mem {n : Nat} (a : Axis n) (t : Fin n) :
    Mem (a.point t) ↔ t.val < 2 ∨ n ≤ t.val + 2 := by
  have hd := a.deep
  cases ha : a.horizontal <;> simp only [Axis.point, ha, Bool.false_eq_true,
    ↓reduceIte, Mem] <;> omega

theorem Axis.point_adj {n : Nat} (a : Axis n) {t u : Fin n}
    (h : t.val + 1 = u.val) : (gridGraph n n).Adj (a.point t) (a.point u) := by
  change adjacent n n _ _
  cases ha : a.horizontal <;> simp [Axis.point, ha, adjacent, h]

/-- Every deep point of the physical axis lies in the full actual carrier. -/
theorem full_axis_exists {n : Nat} (hn : 5 ≤ n) (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (C : Carrier F) (hfull : C ∈ fullCarriers F) :
    ∃ a : Axis n, ∀ t : Fin n, 2 ≤ t.val → t.val + 2 < n →
      a.point t ∈ deepVertices F C := by
  have hcard : (deepVertices F C).card = n - 4 := (mem_filter.mp hfull).2
  have hs (v : deepVertices F C) : ∃ hv : v.1 ∈ F,
      (⟨v.1, hv⟩ : (↑F : Set _)) ∈ C.supp :=
    let ⟨hv, hc, _⟩ := (mem_deepVertices hn F C v.1).mp v.2
    ⟨hv, hc⟩
  have hb (v : deepVertices F C) :
      2 ≤ v.1.1.val ∧ v.1.1.val + 2 < n ∧
      2 ≤ v.1.2.val ∧ v.1.2.val + 2 < n := by
    obtain ⟨_, _, ha⟩ := (mem_deepVertices hn F C v.1).mp v.2
    dsimp [Mem] at ha
    omega
  obtain ⟨v, hv⟩ := card_pos.mp (show 0 < (deepVertices F C).card by omega)
  have hvb := hb ⟨v, hv⟩
  rcases induced_forced_connectedComponent_straight hacyc C with ⟨r, hr⟩ | ⟨c, hc⟩
  · have hrow (w : deepVertices F C) : w.1.1 = r := hr _ (hs w).choose_spec
    have hrd : 2 ≤ r.val ∧ r.val + 2 < n := by
      have he := congrArg Fin.val (hrow ⟨v, hv⟩)
      dsimp only at he hvb
      omega
    let a : Axis n := ⟨true, r, hrd⟩
    refine ⟨a, ?_⟩
    let f : deepVertices F C → Fin (n - 4) := fun w =>
      ⟨w.1.2.val - 2, by have := hb w; omega⟩
    have hinj : Function.Injective f := by
      intro w x he
      have he' := congrArg Fin.val he
      have hw := hb w
      have hx := hb x
      apply Subtype.ext
      refine Prod.ext ((hrow w).trans (hrow x).symm) (Fin.ext ?_)
      dsimp [f] at he'
      omega
    have hsurj := ((Fintype.bijective_iff_injective_and_card f).mpr
      ⟨hinj, by simpa only [Fintype.card_coe, Fintype.card_fin] using hcard⟩).2
    intro t ht ht'
    obtain ⟨w, hw⟩ := hsurj ⟨t.val - 2, by omega⟩
    have he := congrArg Fin.val hw
    have hwb := hb w
    have heq : w.1 = a.point t := by
      apply Prod.ext
      · exact hrow w
      · apply Fin.ext
        change w.1.2.val = t.val
        dsimp [f] at he
        omega
    exact heq ▸ w.2
  · have hcol (w : deepVertices F C) : w.1.2 = c := hc _ (hs w).choose_spec
    have hcd : 2 ≤ c.val ∧ c.val + 2 < n := by
      have he := congrArg Fin.val (hcol ⟨v, hv⟩)
      dsimp only at he hvb
      omega
    let a : Axis n := ⟨false, c, hcd⟩
    refine ⟨a, ?_⟩
    let f : deepVertices F C → Fin (n - 4) := fun w =>
      ⟨w.1.1.val - 2, by have := hb w; omega⟩
    have hinj : Function.Injective f := by
      intro w x he
      have he' := congrArg Fin.val he
      have hw := hb w
      have hx := hb x
      apply Subtype.ext
      refine Prod.ext (Fin.ext ?_) ((hcol w).trans (hcol x).symm)
      dsimp [f] at he'
      omega
    have hsurj := ((Fintype.bijective_iff_injective_and_card f).mpr
      ⟨hinj, by simpa only [Fintype.card_coe, Fintype.card_fin] using hcard⟩).2
    intro t ht ht'
    obtain ⟨w, hw⟩ := hsurj ⟨t.val - 2, by omega⟩
    have he := congrArg Fin.val hw
    have hwb := hb w
    have heq : w.1 = a.point t := by
      apply Prod.ext
      · apply Fin.ext
        change w.1.1.val = t.val
        dsimp [f] at he
        omega
      · exact hcol w
    exact heq ▸ w.2

def Axis.edge {n : Nat} (hn : 5 ≤ n) (a : Axis n) (j : Fin (n - 3)) :
    Sym2 (GridVertex n n) :=
  s(a.point ⟨j.val + 1, by have := j.isLt; omega⟩,
    a.point ⟨j.val + 2, by have := j.isLt; omega⟩)

theorem Axis.edge_injective {n : Nat} (hn : 5 ≤ n) (a : Axis n) :
    Function.Injective (a.edge hn) := by
  intro j k he
  rcases Sym2.eq_iff.mp he with h | h
  · have h1 := congrArg Fin.val (a.point_injective h.1)
    apply Fin.ext
    dsimp [Axis.edge] at h1
    omega
  · have h1 := congrArg Fin.val (a.point_injective h.1)
    have h2 := congrArg Fin.val (a.point_injective h.2)
    apply Fin.ext
    dsimp [Axis.edge] at h1 h2
    omega

/-- A packet contains `n-3 = (n-4)+1` distinct longitudinal forced edges.
Each edge has a deep endpoint in this carrier; any nonannulus endpoint is
also in this carrier. This is the physical separation used in edge counting. -/
theorem Axis.edge_physical {n : Nat} (hn : 5 ≤ n) (F : Finset (GridVertex n n))
    (C : Carrier F) (a : Axis n)
    (hfull : ∀ t : Fin n, 2 ≤ t.val → t.val + 2 < n → a.point t ∈ deepVertices F C)
    (j : Fin (n - 3)) :
    a.edge hn j ∈ (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).edgeFinset ∧
      (∃ v ∈ a.edge hn j, v ∈ deepVertices F C) ∧
      (∀ v ∈ a.edge hn j, Mem v ∨ v ∈ deepVertices F C) := by
  have hj := j.isLt
  let t : Fin n := ⟨j.val + 1, by omega⟩
  let u : Fin n := ⟨j.val + 2, by omega⟩
  have hdeep : a.point t ∈ deepVertices F C ∨ a.point u ∈ deepVertices F C := by
    by_cases hz : j.val = 0
    · exact Or.inr (hfull u (by dsimp [u]; omega) (by dsimp [u]; omega))
    · exact Or.inl (hfull t (by dsimp [t]; omega) (by dsimp [t]; omega))
  have hF : a.point t ∈ F ∨ a.point u ∈ F :=
    hdeep.elim (fun h => Or.inl ((mem_deepVertices hn F C _).mp h).choose)
      (fun h => Or.inr ((mem_deepVertices hn F C _).mp h).choose)
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_edgeFinset]
    exact ⟨a.point_adj (by rfl), hF⟩
  · rcases hdeep with h | h
    · exact ⟨a.point t, by simp [Axis.edge, t], h⟩
    · exact ⟨a.point u, by simp [Axis.edge, u], h⟩
  · intro v hv
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    all_goals
      apply or_iff_not_imp_left.mpr
      intro hm
      rw [a.point_mem] at hm
      exact hfull _ (by omega) (by omega)

end GridGraphs.CarrierLayers.Annulus
