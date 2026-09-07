import GridGraphs.Accounting.CarrierLayers.CoveredBoundary
import GridGraphs.Accounting.CarrierLayers.RadialSideGeometry

/-!
# Lower pure-mass deficit from physical inward-carrier shadows

A boundary vertex diagonally opposite a preserved next-ring vertex is an
actual hole, not a potential carrier endpoint. Count the union of these
shadows, never the sum over inward carriers. In the four-pure-carrier branch
this gives a lower bound on full-side length shortfall.

A nontrivial horizontal interval on row one casts an expanded contiguous
shadow on row zero. Interval filling lets two vertices of one actual carrier
certify the entire shadow. No ambient connectivity or maximality is assumed.
-/

namespace GridGraphs

open Finset SimpleGraph

attribute [local instance] Classical.propDecidable

/-- Physical boundary shadows, with shared witnesses counted only once. -/
noncomputable def coveredBoundaryShadow {n : Nat} (F : Finset (GridVertex n n)) :
    Finset (GridVertex n n) :=
  univ.filter fun v => IsGridBoundary v ∧ ∃ w ∈ F, IsNextRing w ∧
    (v.1.val + 1 = w.1.val ∨ w.1.val + 1 = v.1.val) ∧
    (v.2.val + 1 = w.2.val ∨ w.2.val + 1 = v.2.val)

/-- Each shadow point is an actual unpreserved vertex: the two diagonally
opposite preserved vertices would force all four edges of a unit cell. -/
theorem coveredBoundaryShadow_notMem {n : Nat} (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    {v : GridVertex n n} (hv : v ∈ coveredBoundaryShadow F) : v ∉ F := by
  obtain ⟨_, w, hw, _, hr, hc⟩ := (mem_filter.mp hv).2
  have diagonal (r c : Fin (n - 1)) :
      (cell00 r c ∉ F ∨ cell11 r c ∉ F) ∧
      (cell01 r c ∉ F ∨ cell10 r c ∉ F) := by
    rcases grid_cell_has_unforced_edge r c hacyc with h | h | h | h
    · exact ⟨Or.inl h.1, Or.inl h.2⟩
    · exact ⟨Or.inr h.2, Or.inl h.1⟩
    · exact ⟨Or.inr h.1, Or.inr h.2⟩
    · exact ⟨Or.inl h.2, Or.inr h.1⟩
  intro hvF
  rcases hr with hr | hr <;> rcases hc with hc | hc
  · let r : Fin (n - 1) := ⟨v.1.val, by have := w.1.isLt; omega⟩
    let c : Fin (n - 1) := ⟨v.2.val, by have := w.2.isLt; omega⟩
    have he : cell11 r c = w := by
      apply Prod.ext <;> apply Fin.ext <;> assumption
    exact (diagonal r c).1.elim (fun h => h hvF) (fun h => h (he.symm ▸ hw))
  · let r : Fin (n - 1) := ⟨v.1.val, by have := w.1.isLt; omega⟩
    let c : Fin (n - 1) := ⟨w.2.val, by have := v.2.isLt; omega⟩
    have hev : cell01 r c = v := by
      apply Prod.ext <;> apply Fin.ext
      · rfl
      · exact hc
    have hew : cell10 r c = w := by
      apply Prod.ext <;> apply Fin.ext
      · exact hr
      · rfl
    exact (diagonal r c).2.elim
      (fun h => h (hev.symm ▸ hvF)) (fun h => h (hew.symm ▸ hw))
  · let r : Fin (n - 1) := ⟨w.1.val, by have := v.1.isLt; omega⟩
    let c : Fin (n - 1) := ⟨v.2.val, by have := w.2.isLt; omega⟩
    have hev : cell10 r c = v := by
      apply Prod.ext <;> apply Fin.ext
      · exact hr
      · rfl
    have hew : cell01 r c = w := by
      apply Prod.ext <;> apply Fin.ext
      · rfl
      · exact hc
    exact (diagonal r c).2.elim
      (fun h => h (hew.symm ▸ hw)) (fun h => h (hev.symm ▸ hvF))
  · let r : Fin (n - 1) := ⟨w.1.val, by have := v.1.isLt; omega⟩
    let c : Fin (n - 1) := ⟨w.2.val, by have := v.2.isLt; omega⟩
    have he : cell11 r c = v := by
      apply Prod.ext <;> apply Fin.ext <;> assumption
    exact (diagonal r c).1.elim (fun h => h hw) (fun h => h (he.symm ▸ hvF))

/-- The actual pure mass and the union of inward shadows occupy disjoint
physical boundary sites. This is an upper bound on mass, hence a lower loss. -/
theorem pure_mass_add_coveredBoundaryShadow_le_perimeter {n : Nat} (hn : 7 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic) :
    (pureBoundaryVertices F).card + (coveredBoundaryShadow F).card ≤ 4 * n - 4 := by
  classical
  let P := (pureBoundaryVertices F).image Subtype.val
  have hP : P.card = (pureBoundaryVertices F).card :=
    card_image_of_injective _ Subtype.val_injective
  have hd : Disjoint P (coveredBoundaryShadow F) := by
    apply Finset.disjoint_left.mpr
    intro v hv hs
    obtain ⟨u, _, rfl⟩ := mem_image.mp hv
    exact coveredBoundaryShadow_notMem F hacyc hs u.property
  have hsub : P ∪ coveredBoundaryShadow F ⊆
      ({v | IsGridBoundary v} : Set (GridVertex n n)).toFinset := by
    intro v hv
    apply Set.mem_toFinset.mpr
    rcases mem_union.mp hv with hv | hv
    · obtain ⟨u, hu, rfl⟩ := mem_image.mp hv
      obtain ⟨C, hC, huC⟩ := mem_biUnion.mp hu
      exact (mem_filter.mp hC).2 u (Set.mem_toFinset.mp huC)
    · exact (mem_filter.mp hv).2.1
  have h := card_le_card hsub
  rw [card_union_of_disjoint hd, hP, BoundaryFiveConstruction.boundary_card hn] at h
  exact h

/-- A lower, not upper, bound on four-carrier full-side shortfall. The shadow
is a union across all four sides and all inward carriers. -/
theorem coveredBoundaryShadow_add_four_le_shortfall {n : Nat} (hn : 7 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hp : (pureBoundaryCarriers F).card = 4) :
    (coveredBoundaryShadow F).card + 4 ≤
      n * (pureBoundaryCarriers F).card - (pureBoundaryVertices F).card := by
  have h := pure_mass_add_coveredBoundaryShadow_le_perimeter hn F hacyc
  rw [hp]
  omega

/-- All-side coverage, without assuming exactly four carriers. Additional pure
carriers contribute their full extra side capacities to the same lower loss. -/
theorem all_sides_covered_shadow_shortfall {n : Nat} (hn : 7 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hcovered : ∀ s : Fin 4, ∃ C ∈ pureBoundaryCarriers F, ∃ v ∈ C.supp,
      CarrierLayers.OnOpenSide s v.val) :
    n * ((pureBoundaryCarriers F).card - 4) + (coveredBoundaryShadow F).card + 4 ≤
      n * (pureBoundaryCarriers F).card - (pureBoundaryVertices F).card := by
  have hp : 4 ≤ (pureBoundaryCarriers F).card := by
    by_contra h
    obtain ⟨s, hs⟩ := CarrierLayers.exists_side_without_pure_carrier
      (by omega) F hacyc (by omega)
    obtain ⟨C, hC, v, hv, hvs⟩ := hcovered s
    exact hs C hC v hv hvs
  have h := pure_mass_add_coveredBoundaryShadow_le_perimeter hn F hacyc
  have hmul := Nat.mul_le_mul_left n hp
  rw [Nat.mul_sub_left_distrib]
  omega

/-- Combining physical loss with the existing contact budget gives a lower
cost. This cancels the shared pure mass; it does not add the two budgets. -/
theorem coveredBoundaryShadow_add_twice_pure_le_cost {n : Nat} (hn : 7 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic) :
    (coveredBoundaryShadow F).card + 2 * (pureBoundaryCarriers F).card ≤
      boundaryDeficiencySum n n (univ \ F) +
        2 * Fintype.card ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent := by
  have hloss := pure_mass_add_coveredBoundaryShadow_le_perimeter hn F hacyc
  have hbudget := (perimeter_le_pure_mass_physical_budgets hn F hacyc).2
  have hp := pureBoundaryCarriers_card_le F
  omega

/-- Two distinct positions of an actual row-one carrier force every boundary
site from `a-1` through `b+1` to be a hole. In particular the shadow is a real
contiguous UU run, not a list of hypothetical pure-carrier endpoints. -/
theorem top_carrier_expanded_shadow {n : Nat} (hn : 5 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (C : ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent)
    (u v : (↑F : Set (GridVertex n n))) (hu : u ∈ C.supp) (hv : v ∈ C.supp)
    (hru : u.val.1.val = 1) (hrv : v.val.1.val = 1)
    (ha : 1 ≤ u.val.2.val) (hab : u.val.2.val < v.val.2.val)
    (hb : v.val.2.val + 1 < n)
    (t : Fin n) (ht : u.val.2.val - 1 ≤ t.val ∧ t.val ≤ v.val.2.val + 1) :
    (⟨0, by omega⟩, t) ∈ coveredBoundaryShadow F := by
  let j : Fin n := ⟨if t.val ≤ u.val.2.val then t.val + 1 else t.val - 1, by
    split_ifs <;> omega⟩
  have hj : u.val.2.val ≤ j.val ∧ j.val ≤ v.val.2.val := by
    dsimp [j]
    split_ifs <;> omega
  have hrows : u.val.1 = v.val.1 := Fin.ext (hru.trans hrv.symm)
  obtain ⟨hwF, _⟩ := induced_forced_connectedComponent_horizontal_interval_of_le
    hacyc C hu hv hrows j hj.1 hj.2
  refine mem_filter.mpr ⟨mem_univ _, ?_, (u.val.1, j), hwF, ?_, ?_, ?_⟩
  · exact Or.inl rfl
  · dsimp [IsNextRing]
    omega
  · exact Or.inl hru.symm
  · dsimp [j]
    split_ifs <;> omega

/-- A length `L >= 2` next-ring carrier segment forces at least `L+2`
distinct boundary holes. Endpoints belong to one actual induced component. -/
theorem top_carrier_length_add_two_le_shadow {n : Nat} (hn : 5 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (C : ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent)
    (u v : (↑F : Set (GridVertex n n))) (hu : u ∈ C.supp) (hv : v ∈ C.supp)
    (hru : u.val.1.val = 1) (hrv : v.val.1.val = 1)
    (ha : 1 ≤ u.val.2.val) (hab : u.val.2.val < v.val.2.val)
    (hb : v.val.2.val + 1 < n) :
    v.val.2.val - u.val.2.val + 3 ≤ (coveredBoundaryShadow F).card := by
  let f : Fin (v.val.2.val - u.val.2.val + 3) → coveredBoundaryShadow F := fun i =>
    ⟨(⟨0, by omega⟩, ⟨u.val.2.val - 1 + i.val, by have := i.isLt; omega⟩),
      top_carrier_expanded_shadow hn F hacyc C u v hu hv hru hrv ha hab hb _
        (by have := i.isLt; dsimp; omega)⟩
  have hinj : Function.Injective f := by
    intro i j he
    have h := congrArg (fun w : coveredBoundaryShadow F => w.val.2.val) he
    apply Fin.ext
    dsimp [f] at h
    omega
  simpa only [Fintype.card_fin, Fintype.card_coe] using Fintype.card_le_of_injective f hinj

/-- Concrete length loss in the exactly-four-pure-carrier branch: a physical
next-ring segment of length `L` costs at least `L+6` full-side capacity. -/
theorem top_carrier_length_add_six_le_pure_shortfall {n : Nat} (hn : 7 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hp : (pureBoundaryCarriers F).card = 4)
    (C : ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent)
    (u v : (↑F : Set (GridVertex n n))) (hu : u ∈ C.supp) (hv : v ∈ C.supp)
    (hru : u.val.1.val = 1) (hrv : v.val.1.val = 1)
    (ha : 1 ≤ u.val.2.val) (hab : u.val.2.val < v.val.2.val)
    (hb : v.val.2.val + 1 < n) :
    v.val.2.val - u.val.2.val + 7 ≤ 4 * n - (pureBoundaryVertices F).card := by
  have hshadow := top_carrier_length_add_two_le_shadow (by omega) F hacyc
    C u v hu hv hru hrv ha hab hb
  have hloss := coveredBoundaryShadow_add_four_le_shortfall hn F hacyc hp
  rw [hp] at hloss
  omega

/-- Exact integration with the stable target. This is a sufficient physical
cost certificate, not a claim that every covered configuration supplies one.
For `p=4`, the threshold is `|shadow| + b + 2c >= 6k+11`. -/
theorem residueTwo_card_le_target_of_covered_shadow_cost {k : Nat} (hk : 5 ≤ k)
    (F : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑F : Set _)).IsAcyclic)
    (hcost : 6 * k + 19 ≤ (coveredBoundaryShadow F).card +
      2 * (pureBoundaryCarriers F).card +
      boundaryDeficiencySum (3 * k + 2) (3 * k + 2) (univ \ F) +
      2 * Fintype.card (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
        (↑F : Set _)).ConnectedComponent) :
    F.card ≤ 3 * k ^ 2 + 7 * k := by
  have hcharge := coveredBoundaryShadow_add_twice_pure_le_cost (by omega) F hacyc
  have hledger := grid_component_reduction F hacyc
  have hpartition := boundaryDeficiencySum_add_compl (3 * k + 2) (3 * k + 2) F
  have htotal := total_boundaryDeficiencySum
    (by omega : 2 ≤ 3 * k + 2) (by omega : 2 ≤ 3 * k + 2)
  nlinarith

end GridGraphs
