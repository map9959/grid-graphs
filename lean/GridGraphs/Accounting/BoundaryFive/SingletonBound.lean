import GridGraphs.Accounting.BoundaryStratifiedCarrierBound
import GridGraphs.Accounting.CarrierLayerBound

/-! # The capacity saving from an actual deep singleton

Singleton existence is an explicit hypothesis, not a normalization assumption
or a claimed consequence of boundary deficiency five.
-/

namespace GridGraphs.BoundaryFive

open Finset SimpleGraph

private theorem component_box_cap {n : Nat} {F : Finset (GridVertex n n)}
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (C : ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent)
    (lo width : Nat)
    (hbox : ∀ v ∈ C.supp, lo ≤ v.1.1.val ∧ v.1.1.val < lo + width ∧
      lo ≤ v.1.2.val ∧ v.1.2.val < lo + width) :
    C.supp.toFinset.card ≤ width := by
  classical
  rw [Set.toFinset_card]
  rcases induced_forced_connectedComponent_straight hacyc C with ⟨r, hr⟩ | ⟨c, hc⟩
  · let f : C.supp → Fin width := fun v =>
      ⟨v.1.1.2.val - lo, by have h := hbox v.1 v.2; omega⟩
    have hinj : Function.Injective f := by
      intro v w h
      have he := congrArg Fin.val h
      have hv := hbox v.1 v.2
      have hw := hbox w.1 w.2
      apply Subtype.ext
      apply Subtype.ext
      refine Prod.ext ((hr v.1 v.2).trans (hr w.1 w.2).symm) (Fin.ext ?_)
      dsimp [f] at he
      omega
    simpa using Fintype.card_le_of_injective f hinj
  · let f : C.supp → Fin width := fun v =>
      ⟨v.1.1.1.val - lo, by have h := hbox v.1 v.2; omega⟩
    have hinj : Function.Injective f := by
      intro v w h
      have he := congrArg Fin.val h
      have hv := hbox v.1 v.2
      have hw := hbox w.1 w.2
      apply Subtype.ext
      apply Subtype.ext
      refine Prod.ext (Fin.ext ?_) ((hc v.1 v.2).trans (hc w.1 w.2).symm)
      dsimp [f] at he
      omega
    simpa using Fintype.card_le_of_injective f hinj

/-- Subtraction-free singleton capacity bound: `f + n <= (n-4)r + 12`.
The singleton is an actual nonpure induced component. -/
theorem card_add_side_le_of_singleton {n : Nat} (hn : 10 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 5)
    (Z : ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent)
    (hZ : Z ∉ pureBoundaryCarriers F) (hsize : Z.supp.toFinset.card = 1) :
    F.card + n ≤ (n - 4) *
      Fintype.card ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent + 12 := by
  classical
  let G := (gridGraph n n).induce (↑F : Set _)
  let B := pureBoundaryCarriers F
  have hnext (v : GridVertex n n) (hv : IsNextRing v) : v ∉ F := by
    exact boundaryDeficiencySum_compl_eq_five_next_ring_notMem (by omega) F hacyc hb v
      hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1 hv.2.2.2.2
  have hpure {C : G.ConnectedComponent} {v : (↑F : Set (GridVertex n n))}
      (hv : v ∈ C.supp) (hvb : IsGridBoundary v.1) : C ∈ B := by
    by_contra h
    obtain ⟨w, _, hw, _⟩ := boundary_nonpure_carrier_nextRing_neighbor
      (by omega) F hacyc C h hv hvb
    exact hnext w.1 hw w.2
  have hsum (S : Finset G.ConnectedComponent) :
      (S.biUnion fun C => C.supp.toFinset).card = ∑ C ∈ S, C.supp.toFinset.card := by
    rw [card_biUnion]
    intro C _ D _ hne
    simpa using pairwise_disjoint_supp_connectedComponent G hne
  have hcover : (univ.biUnion fun C : G.ConnectedComponent => C.supp.toFinset) =
      (univ : Finset (↑F : Set (GridVertex n n))) := by
    ext v
    simp [ConnectedComponent.mem_supp_iff]
  have htotal : F.card = ∑ C : G.ConnectedComponent, C.supp.toFinset.card := by
    rw [← hsum, hcover]
    simp
  have hBcover : (B.biUnion fun C => C.supp.toFinset) =
      univ.filter (fun v : (↑F : Set (GridVertex n n)) => IsGridBoundary v.1) := by
    ext v
    simp only [mem_biUnion, Set.mem_toFinset, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨C, hC, hv⟩
      exact (mem_filter.mp hC).2 v hv
    · intro hv
      exact ⟨G.connectedComponentMk v,
        hpure (by simp [ConnectedComponent.mem_supp_iff]) hv,
        by simp [ConnectedComponent.mem_supp_iff, G]⟩
  have hBmass : (∑ C ∈ B, C.supp.toFinset.card) = 4 * n - 9 := by
    rw [← hsum, hBcover]
    have heq : (univ.filter (fun v : (↑F : Set (GridVertex n n)) =>
        IsGridBoundary v.1)).card = (F.filter IsGridBoundary).card := by
      apply card_bij (fun v _ => v.1)
      · intro v hv
        exact mem_filter.mpr ⟨v.2, (mem_filter.mp hv).2⟩
      · intro v _ w _ h
        exact Subtype.ext h
      · intro v hv
        exact ⟨⟨v, (mem_filter.mp hv).1⟩,
          mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hv).2⟩, rfl⟩
    rw [heq]
    have hholes := (boundaryDeficiencySum_compl_eq_five_corners_and_card
      (by omega) F hacyc hb).2
    have hall := BoundaryFiveConstruction.boundary_card (by omega : 7 ≤ n)
    have hpartition : F.filter IsGridBoundary ∪ (univ \ F).filter IsGridBoundary =
        ({v | IsGridBoundary v} : Set (GridVertex n n)).toFinset := by
      ext v
      by_cases hv : v ∈ F <;> simp [hv]
    have hdisj : Disjoint (F.filter IsGridBoundary) ((univ \ F).filter IsGridBoundary) := by
      apply Finset.disjoint_left.mpr
      intro v hv hw
      exact (mem_sdiff.mp (mem_filter.mp hw).1).2 (mem_filter.mp hv).1
    have h := card_union_of_disjoint hdisj
    rw [hpartition, hall, hholes] at h
    omega
  have hfour : 4 ≤ B.card := by
    have hcap : 4 * n - 9 ≤ n * B.card := by
      rw [← hBmass]
      calc
        _ ≤ ∑ _C ∈ B, n := sum_le_sum (fun C _ =>
          component_box_cap hacyc C 0 n (by intro v _; simp))
        _ = _ := by simp [Nat.mul_comm]
    by_contra h
    have hmul := Nat.mul_le_mul_left n (show B.card ≤ 3 by omega)
    omega
  have hcap (C : G.ConnectedComponent) (hC : C ∉ B) :
      C.supp.toFinset.card ≤ n - 4 := by
    apply component_box_cap hacyc C 2 (n - 4)
    intro v hv
    have hd := boundary_five_mem_deep_of_not_boundary (by omega) F hacyc hb v.2
      (fun h => hC (hpure hv h))
    dsimp [BoundaryFiveConstruction.Deep] at hd
    omega
  let S := insert Z B
  have hScard : S.card = B.card + 1 := card_insert_of_notMem hZ
  have hSmass : (∑ C ∈ S, C.supp.toFinset.card) = 4 * n - 9 + 1 := by
    rw [sum_insert hZ, hsize, hBmass]
    omega
  have hrest : (∑ C ∈ univ \ S, C.supp.toFinset.card) ≤
      (n - 4) * (Fintype.card G.ConnectedComponent - S.card) := by
    calc
      _ ≤ ∑ _C ∈ univ \ S, (n - 4) := sum_le_sum (fun C hC =>
        hcap C (fun h => (mem_sdiff.mp hC).2 (mem_insert_of_mem h)))
      _ = _ := by simp [card_sdiff_of_subset (subset_univ S), Nat.mul_comm, G]
  have hsplit := sum_sdiff (subset_univ S) (f := fun C : G.ConnectedComponent =>
    C.supp.toFinset.card)
  rw [← htotal, hSmass] at hsplit
  have hSle : S.card ≤ Fintype.card G.ConnectedComponent := by
    simpa using card_le_card (subset_univ S)
  have hscaled := congrArg (fun t => (n - 4) * t) (Nat.sub_add_cancel hSle)
  have hfive := Nat.mul_le_mul_left (n - 4) (show 5 ≤ S.card by omega)
  change F.card + n ≤ (n - 4) * Fintype.card G.ConnectedComponent + 12
  have hnsub : n - 4 + 4 = n := by omega
  have hnine : 4 * n - 9 + 9 = 4 * n := by omega
  nlinarith

end GridGraphs.BoundaryFive
