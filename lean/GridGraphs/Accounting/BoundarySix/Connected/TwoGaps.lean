import GridGraphs.Accounting.BoundarySix.Connected.PerimeterLedger

/-! # The two actual omitted perimeter edges

Ambient connectivity and an empty next ring make the boundary holes a
matching. With four pure carriers, the two omitted edges exhaust the two
extra holes beyond four independent near-corner witnesses.
-/

namespace GridGraphs.BoundarySix.Connected

open Finset SimpleGraph CarrierLayers CarrierLayers.FourCarrier CarrierLayers.Annulus

attribute [local instance] Classical.propDecidable

@[simp] theorem mem_perimeterHoles_pair {n : Nat} (F : Finset (GridVertex n n))
    (u v : PerimeterVertex n) : s(u, v) ∈ perimeterHoles F ↔
      (gridGraph n n).Adj u.1 v.1 ∧ u.1 ∉ F ∧ v.1 ∉ F := by
  simp only [perimeterHoles, mem_sdiff, mem_edgeFinset]
  change ((gridGraph n n).Adj u.1 v.1 ∧ ¬ ((gridGraph n n).Adj u.1 v.1 ∧
    (u ∈ perimeterSelected F ∨ v ∈ perimeterSelected F))) ↔ _
  simp only [mem_perimeterSelected]
  tauto

/-- Two omitted perimeter edges cannot share an endpoint: its only possible
preserved neighbor would lie on the empty next ring. -/
theorem boundary_hole_neighbor_unique {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hc : Fintype.card (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).ConnectedComponent = 1)
    (hEmpty : F.filter IsNextRing = ∅)
    (u v w : PerimeterVertex n) (hu : u.1 ∉ F) (hv : v.1 ∉ F) (hw : w.1 ∉ F)
    (huv : (gridGraph n n).Adj u.1 v.1) (huw : (gridGraph n n).Adj u.1 w.1) : v = w := by
  by_contra hne
  obtain ⟨a, haF, hua⟩ := preserved_neighbor_of_one_forced_component (by omega) F hc u.1 hu
  have hab : IsGridBoundary a := by
    by_contra hab
    have har : IsNextRing a := by
      have hub := u.2
      simp only [gridGraph, adjacent, Fin.ext_iff] at hua
      unfold IsGridBoundary at hub hab
      unfold IsNextRing
      omega
    have hm := mem_filter.mpr ⟨haF, har⟩
    rw [hEmpty] at hm
    exact notMem_empty _ hm
  let a' : PerimeterVertex n := ⟨a, hab⟩
  have hav : a' ≠ v := fun he => hv (congrArg Subtype.val he ▸ haF)
  have haw : a' ≠ w := fun he => hw (congrArg Subtype.val he ▸ haF)
  have hsub : {a', v, w} ⊆ (perimeterGraph n).neighborFinset u := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact (mem_neighborFinset _ _ _).mpr hua
    · exact (mem_neighborFinset _ _ _).mpr huv
    · exact (mem_neighborFinset _ _ _).mpr huw
  have hcard := card_le_card hsub
  rw [card_neighborFinset_eq_degree, perimeter_degree (by omega)] at hcard
  have hthree : ({a', v, w} : Finset (PerimeterVertex n)).card = 3 := by simp [hav, haw, hne]
  omega

/-- Six boundary holes, four preserved perimeter components, and exactly two
omitted perimeter edges in the remaining geometric branch. -/
theorem two_perimeter_holes {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 6)
    (hp : (pureBoundaryCarriers F).card = 4)
    (hEmpty : F.filter IsNextRing = ∅)
    (hcorners : ∀ z, Corner z → z ∈ F) :
    ((univ \ F).filter IsGridBoundary).card = 6 ∧ (perimeterHoles F).card = 2 := by
  have hweight (v : GridVertex n n) (hv : v ∈ univ \ F) :
      gridBoundaryDeficiency n n v = if IsGridBoundary v then 1 else 0 := by
    have hnc : ¬ Corner v := fun h => (mem_sdiff.mp hv).2 (hcorners v h)
    rw [gridBoundaryDeficiency_eq_four_side_indicators (by omega) (by omega)]
    unfold IsGridBoundary Corner at *
    split_ifs <;> omega
  have hholes : ((univ \ F).filter IsGridBoundary).card = 6 := by
    have hsum := sum_congr (s₁ := univ \ F) rfl hweight
    simp only [sum_boole, Nat.cast_id] at hsum
    change boundaryDeficiencySum n n (univ \ F) =
      ((univ \ F).filter IsGridBoundary).card at hsum
    omega
  have hpartition : F.filter IsGridBoundary ∪ (univ \ F).filter IsGridBoundary =
      ({v | IsGridBoundary v} : Set (GridVertex n n)).toFinset := by
    ext v
    by_cases hv : v ∈ F <;> simp [hv]
  have hdisj : Disjoint (F.filter IsGridBoundary) ((univ \ F).filter IsGridBoundary) := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    exact (mem_sdiff.mp (mem_filter.mp hw).1).2 (mem_filter.mp hv).1
  have htotal := congrArg Finset.card hpartition
  rw [card_union_of_disjoint hdisj, BoundaryFiveConstruction.boundary_card (by omega)] at htotal
  have hledger := perimeter_holes_card hn F hacyc hEmpty
  exact ⟨hholes, by omega⟩

/-- The boundary holes consist exactly of four near-corner witnesses and two
distinct second-position holes. The two omitted edges pair the extras with
distinct witnesses; their four endpoints are distinct. -/
theorem two_gap_classification {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 6)
    (hp : (pureBoundaryCarriers F).card = 4)
    (hc : Fintype.card (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).ConnectedComponent = 1)
    (hEmpty : F.filter IsNextRing = ∅)
    (hcorners : ∀ z, Corner z → z ∈ F) :
    ∃ (Q : Finset (GridVertex n n)) (u v q r : PerimeterVertex n),
      Q.card = 4 ∧ (∀ z ∈ Q, Near z) ∧
      u.1 ∉ Q ∧ v.1 ∉ Q ∧ u ≠ v ∧ q.1 ∈ Q ∧ r.1 ∈ Q ∧ q ≠ r ∧
      Second u.1 ∧ Second v.1 ∧
      (gridGraph n n).Adj u.1 q.1 ∧ (gridGraph n n).Adj v.1 r.1 ∧
      (univ \ F).filter IsGridBoundary = insert u.1 (insert v.1 Q) ∧
      perimeterHoles F = {s(u, q), s(v, r)} := by
  obtain ⟨hBcard, hEcard⟩ := two_perimeter_holes hn F hacyc hb hp hEmpty hcorners
  obtain ⟨Q, hQcard, hQU, hQnear⟩ := corner_witnesses hn F hacyc
  let B := (univ \ F).filter IsGridBoundary
  change B.card = 6 at hBcard
  have hQB : Q ⊆ B := by
    intro z hz
    refine mem_filter.mpr ⟨hQU hz, ?_⟩
    have h := hQnear z hz
    unfold Near IsGridBoundary at *
    omega
  have hrest : (B \ Q).card = 2 := by rw [card_sdiff_of_subset hQB]; omega
  have orient (e : Sym2 (PerimeterVertex n)) (he : e ∈ perimeterHoles F) :
      ∃ u q : PerimeterVertex n, e = s(u, q) ∧ u.1 ∉ Q := by
    induction e using Sym2.inductionOn with
    | _ u q =>
      obtain ⟨huq, _, _⟩ := (mem_perimeterHoles_pair F u q).mp he
      by_cases hu : u.1 ∈ Q
      · refine ⟨q, u, Sym2.eq_swap, ?_⟩
        intro hq
        have hnu := hQnear u.1 hu
        have hnq := hQnear q.1 hq
        simp only [gridGraph, adjacent, Fin.ext_iff] at huq
        unfold Near at hnu hnq
        omega
      · exact ⟨u, q, rfl, hu⟩
  obtain ⟨e, f, hef, hEf⟩ := card_eq_two.mp hEcard
  obtain ⟨u, q, rfl, huQ⟩ := orient e (by rw [hEf]; simp)
  obtain ⟨v, r, rfl, hvQ⟩ := orient f (by rw [hEf]; simp)
  obtain ⟨huq, huF, hqF⟩ := (mem_perimeterHoles_pair F u q).mp (by rw [hEf]; simp)
  obtain ⟨hvr, hvF, hrF⟩ := (mem_perimeterHoles_pair F v r).mp (by rw [hEf]; simp)
  have huv : u ≠ v := by
    intro he
    subst v
    have hqr := boundary_hole_neighbor_unique hn F hc hEmpty u q r huF hqF hrF huq hvr
    exact hef (hqr ▸ rfl)
  have hqv : q ≠ v := by
    intro he
    subst v
    have hur := boundary_hole_neighbor_unique hn F hc hEmpty q u r hqF huF hrF huq.symm hvr
    subst r
    exact hef Sym2.eq_swap
  have hru : r ≠ u := by
    intro he
    subst r
    have hqv' := boundary_hole_neighbor_unique hn F hc hEmpty u q v huF hqF hvF huq hvr.symm
    exact hqv hqv'
  have hqr : q ≠ r := by
    intro he
    subst r
    have huv' := boundary_hole_neighbor_unique hn F hc hEmpty q u v hqF huF hvF huq.symm hvr.symm
    exact huv huv'
  have huB : u.1 ∈ B := mem_filter.mpr ⟨by simp [huF], u.2⟩
  have hvB : v.1 ∈ B := mem_filter.mpr ⟨by simp [hvF], v.2⟩
  have huvval : u.1 ≠ v.1 := fun h => huv (Subtype.ext h)
  have hrestEq : B \ Q = {u.1, v.1} := by
    symm
    apply eq_of_subset_of_card_le
    · exact insert_subset (mem_sdiff.mpr ⟨huB, huQ⟩)
        (singleton_subset_iff.mpr (mem_sdiff.mpr ⟨hvB, hvQ⟩))
    · rw [hrest, card_pair huvval]
  have hqQ : q.1 ∈ Q := by
    by_contra h
    have hm : q.1 ∈ B \ Q := mem_sdiff.mpr ⟨mem_filter.mpr ⟨by simp [hqF], q.2⟩, h⟩
    rw [hrestEq] at hm
    rcases mem_insert.mp hm with he | he
    · exact huq.ne he.symm
    · exact hqv (Subtype.ext (mem_singleton.mp he))
  have hrQ : r.1 ∈ Q := by
    by_contra h
    have hm : r.1 ∈ B \ Q := mem_sdiff.mpr ⟨mem_filter.mpr ⟨by simp [hrF], r.2⟩, h⟩
    rw [hrestEq] at hm
    rcases mem_insert.mp hm with he | he
    · exact hru (Subtype.ext he)
    · exact hvr.ne (mem_singleton.mp he).symm
  have huSecond := (neighbor_near hn u.2 (hQnear q.1 hqQ) huq).resolve_left
    (fun h => huF (hcorners u.1 h))
  have hvSecond := (neighbor_near hn v.2 (hQnear r.1 hrQ) hvr).resolve_left
    (fun h => hvF (hcorners v.1 h))
  refine ⟨Q, u, v, q, r, hQcard, hQnear, huQ, hvQ, huv, hqQ, hrQ, hqr,
    huSecond, hvSecond, huq, hvr, ?_, hEf⟩
  change B = _
  have h := sdiff_union_of_subset hQB
  rw [hrestEq] at h
  simpa using h.symm

end GridGraphs.BoundarySix.Connected
