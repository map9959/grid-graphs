import GridGraphs.Accounting.BoundarySix.Connected.MissingCorner

/-! # The actual perimeter ledger in the empty-next-ring case -/

namespace GridGraphs.BoundarySix.Connected

open Finset SimpleGraph CarrierLayers CarrierLayers.FourCarrier CarrierLayers.Annulus

attribute [local instance] Classical.propDecidable

abbrev PerimeterVertex (n : Nat) := {v : GridVertex n n // IsGridBoundary v}

def perimeterGraph (n : Nat) : SimpleGraph (PerimeterVertex n) :=
  (gridGraph n n).induce IsGridBoundary

noncomputable def perimeterSelected {n : Nat} (F : Finset (GridVertex n n)) :
    Finset (PerimeterVertex n) := univ.filter (fun v => v.1 ∈ F)

@[simp] theorem mem_perimeterSelected {n : Nat} (F : Finset (GridVertex n n))
    (v : PerimeterVertex n) : v ∈ perimeterSelected F ↔ v.1 ∈ F := by
  simp [perimeterSelected]

theorem perimeterSelected_card {n : Nat} (F : Finset (GridVertex n n)) :
    (perimeterSelected F).card = (F.filter IsGridBoundary).card := by
  apply card_bij (fun v _ => v.1)
  · intro v hv
    exact mem_filter.mpr ⟨(mem_perimeterSelected F v).mp hv, v.2⟩
  · intro v _ w _ he
    exact Subtype.ext he
  · intro v hv
    exact ⟨⟨v, (mem_filter.mp hv).2⟩, (mem_perimeterSelected F _).mpr (mem_filter.mp hv).1, rfl⟩

private theorem boundary_chart {n : Nat} (hn : 2 ≤ n) (v : PerimeterVertex n) :
    ∃ (s : Fin 4) (t : Fin n), v.1 = sideChart s (t, ⟨0, by omega⟩) := by
  rcases v.2 with h | h | h | h
  · refine ⟨0, v.1.2, ?_⟩
    apply Prod.ext <;> apply Fin.ext <;> simp [sideChart]
    omega
  · refine ⟨1, v.1.2, ?_⟩
    apply Prod.ext <;> apply Fin.ext <;> simp [sideChart]
    omega
  · refine ⟨2, v.1.1, ?_⟩
    apply Prod.ext <;> apply Fin.ext <;> simp [sideChart]
    omega
  · refine ⟨3, v.1.1, ?_⟩
    apply Prod.ext <;> apply Fin.ext <;> simp [sideChart]
    omega

/-- Every vertex of the actual perimeter has degree two, including corners. -/
theorem perimeter_degree {n : Nat} (hn : 3 ≤ n) (v : PerimeterVertex n) :
    (perimeterGraph n).degree v = 2 := by
  obtain ⟨s, t, ht⟩ := boundary_chart (by omega) v
  let x : GridVertex n n := if t.val = 0 then (t, ⟨1, by omega⟩)
    else (⟨t.val - 1, by omega⟩, ⟨0, by omega⟩)
  let y : GridVertex n n := if hy : t.val + 1 = n then (t, ⟨1, by omega⟩)
    else (⟨t.val + 1, by omega⟩, ⟨0, by omega⟩)
  have hx : IsGridBoundary (sideChart s x) := by
    rw [sideChart_boundary]
    dsimp [x]
    split_ifs <;> simp [IsGridBoundary]
    omega
  have hy : IsGridBoundary (sideChart s y) := by
    rw [sideChart_boundary]
    dsimp [y]
    split_ifs <;> simp [IsGridBoundary]
    omega
  let a : PerimeterVertex n := ⟨sideChart s x, hx⟩
  let b : PerimeterVertex n := ⟨sideChart s y, hy⟩
  have hab : a ≠ b := by
    intro he
    have hxy := sideChart_injective s (congrArg Subtype.val he)
    simp only [Prod.ext_iff, Fin.ext_iff] at hxy
    dsimp [x, y] at hxy
    split_ifs at hxy <;> simp only at hxy <;> omega
  have heq : (perimeterGraph n).neighborFinset v = {a, b} := by
    ext w
    obtain ⟨z, hz⟩ := sideChart_surjective s w.1
    have hzb : IsGridBoundary z := (sideChart_boundary s z).mp (hz ▸ w.2)
    simp only [mem_neighborFinset, mem_insert, mem_singleton]
    change (gridGraph n n).Adj v.1 w.1 ↔ w = a ∨ w = b
    rw [ht, ← hz, sideChart_adj]
    have haeq : w = a ↔ z = x := by
      rw [Subtype.ext_iff]
      change w.1 = sideChart s x ↔ _
      rw [← hz]
      exact (sideChart_injective s).eq_iff
    have hbeq : w = b ↔ z = y := by
      rw [Subtype.ext_iff]
      change w.1 = sideChart s y ↔ _
      rw [← hz]
      exact (sideChart_injective s).eq_iff
    rw [haeq, hbeq]
    simp only [gridGraph, adjacent, Prod.ext_iff, Fin.ext_iff]
    dsimp [x, y]
    unfold IsGridBoundary at hzb
    have hzr := z.1.isLt
    have hzc := z.2.isLt
    have htt := t.isLt
    split_ifs <;> dsimp only <;> simp only [or_false] <;> omega
  rw [← card_neighborFinset_eq_degree, heq, card_pair hab]

/-- Empty next-ring occupancy makes the preserved perimeter components
exactly the actual pure boundary carriers, not merely a lower bound. -/
theorem perimeter_components_eq_pure {n : Nat} (hn : 5 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hEmpty : F.filter IsNextRing = ∅) :
    Fintype.card ((perimeterGraph n).induce (↑(perimeterSelected F) : Set _)).ConnectedComponent =
      (pureBoundaryCarriers F).card := by
  let G := (gridGraph n n).induce (↑F : Set _)
  let L := (perimeterGraph n).induce (↑(perimeterSelected F) : Set _)
  let inc : L →g G :=
    { toFun := fun v => ⟨v.1.1, (mem_perimeterSelected F v.1).mp v.2⟩
      map_rel' := by intro v w h; exact h }
  have hpure (C : G.ConnectedComponent) (v : (↑F : Set (GridVertex n n)))
      (hv : v ∈ C.supp) (hvb : IsGridBoundary v.1) : C ∈ pureBoundaryCarriers F := by
    by_contra hC
    obtain ⟨w, _, hwR, _⟩ := boundary_nonpure_carrier_nextRing_neighbor hn F hacyc C hC hv hvb
    have hm := mem_filter.mpr ⟨w.2, hwR⟩
    rw [hEmpty] at hm
    exact notMem_empty _ hm
  have hmap (C : L.ConnectedComponent) : C.map inc ∈ pureBoundaryCarriers F := by
    induction C using ConnectedComponent.ind with
    | h v => exact hpure _ (inc v) rfl v.1.2
  let f (C : L.ConnectedComponent) : pureBoundaryCarriers F := ⟨C.map inc, hmap C⟩
  have hi : Function.Injective f := by
    intro C D he
    induction C using ConnectedComponent.ind with
    | h v =>
      induction D using ConnectedComponent.ind with
      | h w =>
        have he' := congrArg Subtype.val he
        let K := G.connectedComponentMk (inc v)
        have hvK : inc v ∈ K.supp := rfl
        have hwK : inc w ∈ K.supp := he'.symm
        have hpK := hmap (L.connectedComponentMk v)
        let back : K.toSimpleGraph →g L :=
          { toFun := fun u => ⟨⟨u.1.1, (mem_filter.mp hpK).2 u.1 u.2⟩,
              (mem_perimeterSelected F _).mpr u.1.2⟩
            map_rel' := by intro u u' h; exact h }
        exact ConnectedComponent.sound ((K.reachable_toSimpleGraph hvK hwK).map back)
  have hs : Function.Surjective f := by
    intro C
    obtain ⟨v, hv⟩ := C.1.nonempty_supp
    have hvb := (mem_filter.mp C.2).2 v hv
    let w : (↑(perimeterSelected F) : Set (PerimeterVertex n)) :=
      ⟨⟨v.1, hvb⟩, (mem_perimeterSelected F _).mpr v.2⟩
    refine ⟨L.connectedComponentMk w, ?_⟩
    exact Subtype.ext hv
  simpa only [Fintype.card_coe] using Fintype.card_of_bijective (f := f) ⟨hi, hs⟩

noncomputable def perimeterHoles {n : Nat} (F : Finset (GridVertex n n)) :
    Finset (Sym2 (PerimeterVertex n)) :=
  (perimeterGraph n).edgeFinset \ (forcedEdgeGraph (perimeterGraph n)
    (↑(perimeterSelected F) : Set _)).edgeFinset

/-- Exact degree-two forest ledger for omitted perimeter edges. -/
theorem perimeter_holes_card {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hEmpty : F.filter IsNextRing = ∅) :
    (perimeterHoles F).card + (F.filter IsGridBoundary).card +
      (pureBoundaryCarriers F).card = 4 * n - 4 := by
  let P := perimeterGraph n
  let S := perimeterSelected F
  let H := forcedEdgeGraph P (↑S : Set _)
  let inc : H →g forcedEdgeGraph (gridGraph n n) (↑F : Set _) :=
    { toFun := Subtype.val
      map_rel' := by
        intro v w h
        exact ⟨h.1, h.2.elim (fun hv => Or.inl ((mem_perimeterSelected F v).mp hv))
          (fun hw => Or.inr ((mem_perimeterSelected F w).mp hw))⟩ }
  have hac := hacyc.comap inc Subtype.val_injective
  have hhand := sum_degrees_finset_eq_forced_add_induced P S
  have hsum : (∑ v ∈ S, P.degree v) = 2 * S.card := by
    simp only [P, perimeter_degree (n := n) (by omega), sum_const, smul_eq_mul]
    omega
  have hi := induce_finset_forest_ledger P S hac
  have hp := perimeter_components_eq_pure (by omega) F hacyc hEmpty
  have hS := perimeterSelected_card F
  have hdeg := P.sum_degrees_eq_twice_card_edges
  have hV : Fintype.card (PerimeterVertex n) = 4 * n - 4 := by
    convert BoundaryFiveConstruction.boundary_card (n := n) (by omega) using 1
    rw [Set.toFinset_card]
    exact Fintype.card_congr (Equiv.refl _)
  have hP : P.edgeFinset.card = 4 * n - 4 := by
    have hs : (∑ v : PerimeterVertex n, P.degree v) = 2 * Fintype.card (PerimeterVertex n) := by
      simp only [P, perimeter_degree (n := n) (by omega), sum_const, card_univ, smul_eq_mul]
      omega
    omega
  have hdiff := card_sdiff_add_card_eq_card
    (edgeFinset_mono (forcedEdgeGraph_le P (↑S : Set _)))
  change (perimeterHoles F).card + H.edgeFinset.card = P.edgeFinset.card at hdiff
  change (∑ v ∈ S, P.degree v) = H.edgeFinset.card + _ at hhand
  change _ + Fintype.card (P.induce (↑S : Set _)).ConnectedComponent = S.card at hi
  change Fintype.card (P.induce (↑S : Set _)).ConnectedComponent = _ at hp
  change S.card = _ at hS
  omega

end GridGraphs.BoundarySix.Connected
