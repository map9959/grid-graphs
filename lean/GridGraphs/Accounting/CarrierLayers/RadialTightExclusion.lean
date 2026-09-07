import GridGraphs.Accounting.CarrierLayers.RadialTightPacking
import GridGraphs.Accounting.CarrierLayers.Counterexamples

/-!
# Excluding the tight radial boundary budget

Local coordinates run along the missing side first and inward second.
The second root forces an extra off-side hole by a six-cycle, independently
of the two holes supplied by the opposite corner cells.
-/

namespace GridGraphs.CarrierLayers

open Finset SimpleGraph

attribute [local instance] Classical.propDecidable

private def sideFrame {n : Nat} (s : Fin 4) (v : GridVertex n n) : GridVertex n n :=
  if s.val = 0 then (v.2, v.1)
  else if s.val = 1 then (v.2.rev, v.1)
  else if s.val = 2 then v else (v.1, v.2.rev)

private theorem sideFrame_injective {n : Nat} (s : Fin 4) :
    Function.Injective (sideFrame (n := n) s) := by
  intro u v he
  fin_cases s <;> simp [sideFrame, Prod.ext_iff, Fin.ext_iff] at * <;> omega

private theorem sideFrame_adj {n : Nat} (s : Fin 4) {u v : GridVertex n n}
    (h : (gridGraph n n).Adj u v) :
    (gridGraph n n).Adj (sideFrame s u) (sideFrame s v) := by
  fin_cases s <;> simp [sideFrame, gridGraph, adjacent, Fin.ext_iff] at * <;> omega

private theorem sideFrame_acyclic {n : Nat} (s : Fin 4)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic) :
    (forcedEdgeGraph (gridGraph n n) {v | sideFrame s v ∈ F}).IsAcyclic := by
  let f : forcedEdgeGraph (gridGraph n n) {v | sideFrame s v ∈ F} →g
      forcedEdgeGraph (gridGraph n n) (↑F : Set _) :=
    { toFun := sideFrame s
      map_rel' := fun h => ⟨sideFrame_adj s h.1, h.2⟩ }
  exact hacyc.comap f (sideFrame_injective s)

/-- A preserved corner and a radial root at position two force at least three
off-side boundary holes. The two far-corner witnesses cannot reuse the hole
forced by the corner-adjacent six-cycle. -/
private theorem second_radial_root_offside_holes {n : Nat} (hn : 5 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (s : Fin 4)
    (hc : sideFrame s (⟨0, by omega⟩, ⟨0, by omega⟩) ∈ F)
    (hr : sideFrame s (⟨2, by omega⟩, ⟨0, by omega⟩) ∈ F)
    (hi : sideFrame s (⟨2, by omega⟩, ⟨1, by omega⟩) ∈ F) :
    3 ≤ ((univ \ F).filter (fun v => IsGridBoundary v ∧ ¬ OnOpenSide s v)).card := by
  classical
  let P : Set (GridVertex n n) := {v | sideFrame s v ∈ F}
  have hP := sideFrame_acyclic s F hacyc
  let a : GridVertex n n := (⟨0, by omega⟩, ⟨1, by omega⟩)
  have ha : a ∉ P := by
    intro ha
    exact forced_rectangle_two_rows_false (⟨0, by omega⟩ : Fin (n - 2))
      (⟨0, by omega⟩ : Fin (n - 1)) hP hc ha hr hi
  let b : GridVertex n n := (⟨0, by omega⟩, ⟨n - 2, by omega⟩)
  let c : GridVertex n n := (⟨1, by omega⟩, ⟨n - 1, by omega⟩)
  let d : GridVertex n n := (⟨n - 2, by omega⟩, ⟨n - 1, by omega⟩)
  let e : GridVertex n n := (⟨n - 1, by omega⟩, ⟨n - 2, by omega⟩)
  have hlast : n - 2 + 1 = n - 1 := by omega
  have hbc : b ∉ P ∨ c ∉ P := by
    have H := grid_cell_has_unforced_edge
      (⟨0, by omega⟩ : Fin (n - 1)) (⟨n - 2, by omega⟩ : Fin (n - 1)) hP
    simp only [cell00, cell01, cell11, cell10, hlast] at H
    rcases H with H | H | H | H
    · exact Or.inl H.1
    · exact Or.inr H.2
    · exact Or.inr H.1
    · exact Or.inl H.2
  have hde : d ∉ P ∨ e ∉ P := by
    have H := grid_cell_has_unforced_edge
      (⟨n - 2, by omega⟩ : Fin (n - 1)) (⟨n - 2, by omega⟩ : Fin (n - 1)) hP
    simp only [cell00, cell01, cell11, cell10, hlast] at H
    rcases H with H | H | H | H
    · exact Or.inl H.2
    · exact Or.inl H.1
    · exact Or.inr H.2
    · exact Or.inr H.1
  have choose (u v : GridVertex n n) (h : u ∉ P ∨ v ∉ P) :
      ∃ q, (q = u ∨ q = v) ∧ q ∉ P := by
    rcases h with h | h
    · exact ⟨u, Or.inl rfl, h⟩
    · exact ⟨v, Or.inr rfl, h⟩
  obtain ⟨q, hq, hqU⟩ := choose b c hbc
  obtain ⟨t, ht, htU⟩ := choose d e hde
  let Q : Finset (GridVertex n n) := {a, q, t}
  have hQcard : Q.card = 3 := by
    rcases hq with rfl | rfl <;> rcases ht with rfl | rfl <;>
      simp only [Q, card_insert_eq_ite, card_singleton, mem_insert, mem_singleton,
        a, b, c, d, e, Prod.ext_iff, Fin.ext_iff] <;> split_ifs <;> omega
  have hgeom : ∀ v ∈ Q, IsGridBoundary (sideFrame s v) ∧ ¬ OnOpenSide s (sideFrame s v) := by
    intro v hv
    simp only [Q, mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · fin_cases s <;> simp [sideFrame, a, IsGridBoundary, OnOpenSide, OnSide]
    · rcases hq with rfl | rfl <;> fin_cases s <;>
        simp [sideFrame, b, c, IsGridBoundary, OnOpenSide, OnSide] <;> omega
    · rcases ht with rfl | rfl <;> fin_cases s <;>
        simp [sideFrame, d, e, IsGridBoundary, OnOpenSide, OnSide] <;> omega
  have hsub : Q.image (sideFrame s) ⊆
      (univ \ F).filter (fun v => IsGridBoundary v ∧ ¬ OnOpenSide s v) := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hv
    refine mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_univ _, ?_⟩, hgeom u hu⟩
    simp only [Q, mem_insert, mem_singleton] at hu
    rcases hu with rfl | rfl | rfl
    · exact ha
    · exact hqU
    · exact htU
  have hcard := card_le_card hsub
  rw [card_image_of_injective Q (sideFrame_injective s), hQcard] at hcard
  exact hcard

/-- Tight radial packing on a missing side is geometrically impossible:
the second root supplies a third off-side hole. -/
theorem tight_missing_side_false {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = 2 * k + 2)
    (s : Fin 4)
    (hmissing : ∀ C ∈ pureBoundaryCarriers F, ∀ v ∈ C.supp,
      ¬ OnOpenSide s v.val) : False := by
  classical
  obtain ⟨_, Q, _, _, _, _, hoff, _, hcorners⟩ :=
    tight_missing_side_boundary hk F hacyc hb s hmissing
  let r : GridVertex (3 * k + 2) (3 * k + 2) :=
    sideFrame s (⟨2, by omega⟩, ⟨0, by omega⟩)
  have hrs : OnOpenSide s r := by
    fin_cases s <;> simp [r, sideFrame, OnOpenSide, OnSide] <;> omega
  have hrpos : sidePosition s r = 2 := by
    fin_cases s <;> simp [r, sideFrame, sidePosition]
  have hr : r ∈ F := (tight_missing_side_exact_phase hk F hacyc hb s hmissing r hrs).mpr
    ⟨0, by omega, by simpa using hrpos⟩
  let v : (↑F : Set _) := ⟨r, hr⟩
  let C := ((gridGraph (3 * k + 2) (3 * k + 2)).induce
    (↑F : Set _)).connectedComponentMk v
  have hv : v ∈ C.supp := by simp [C, ConnectedComponent.mem_supp_iff]
  have hC : C ∉ pureBoundaryCarriers F := fun h => hmissing C h v hv hrs
  obtain ⟨w, _, hwr, hadj⟩ := boundary_nonpure_carrier_nextRing_neighbor
    (by omega) F hacyc C hC hv (openSide_boundary hrs)
  have he : w.val = sideFrame s (⟨2, by omega⟩, ⟨1, by omega⟩) := by
    change (gridGraph (3 * k + 2) (3 * k + 2)).Adj r w.val at hadj
    unfold IsNextRing at hwr
    fin_cases s <;> dsimp [r, sideFrame] at hadj ⊢ <;>
      simp only [gridGraph, adjacent, Prod.ext_iff, Fin.ext_iff, Fin.val_rev,
        Fin.val_zero, Fin.val_one] at hadj ⊢ <;> omega
  have hi : sideFrame s (⟨2, by omega⟩, ⟨1, by omega⟩) ∈ F := he ▸ w.property
  have hc : sideFrame s (⟨0, by omega⟩, ⟨0, by omega⟩) ∈ F := by
    apply hcorners
    fin_cases s <;> simp [sideFrame, BoundarySix.Corner]
  have hthree := second_radial_root_offside_holes (by omega) F hacyc s hc hr hi
  omega

end GridGraphs.CarrierLayers

namespace GridGraphs

open Finset SimpleGraph CarrierLayers

/-- The at-most-three-pure-carriers branch has boundary budget at least
`2k+3`, with no maximality or preserved-cardinality assumption. -/
theorem two_mul_add_three_le_boundaryDeficiencySum_of_pure_carriers_le_three
    {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hp : (pureBoundaryCarriers F).card ≤ 3) :
    2 * k + 3 ≤ boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) := by
  have hlower := two_mul_add_two_le_boundaryDeficiencySum_of_pure_carriers_le_three
    hk F hacyc hp
  have hne : boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) ≠ 2 * k + 2 := by
    intro hb
    obtain ⟨s, hs⟩ := exists_side_without_pure_carrier (by omega) F hacyc hp
    exact tight_missing_side_false hk F hacyc hb s hs
  omega

/-- After excluding the tight radial endpoint, two excess vertices in the
at-most-three branch have the unique numerical profile `(k+2, 1, 2k+3)`.
This remaining profile is a necessary condition, not a contradiction. -/
theorem residueTwo_two_excess_three_carrier_profile_unique {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hp : (pureBoundaryCarriers F).card ≤ 3)
    (hcard : 3 * k ^ 2 + 7 * k + 2 ≤ F.card) :
    F.card = 3 * k ^ 2 + 7 * k + 2 ∧
      Fintype.card ((gridGraph (3 * k + 2) (3 * k + 2)).induce
        (↑F : Set _)).ConnectedComponent = k + 2 ∧
      Fintype.card (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
        (↑F : Set _)).ConnectedComponent = 1 ∧
      boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) = 2 * k + 3 := by
  have hb := two_mul_add_three_le_boundaryDeficiencySum_of_pure_carriers_le_three
    hk F hacyc hp
  obtain ⟨hcardEq, hprofile⟩ := residueTwo_two_excess_three_carrier_profiles hk F hacyc hp hcard
  exact ⟨hcardEq, by omega⟩

end GridGraphs
