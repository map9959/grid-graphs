import GridGraphs.Constructions.BoundaryFive.BoundaryFiveConstruction
import GridGraphs.Accounting.BoundaryFiveEquality
import GridGraphs.Accounting.CarrierLengthBound

/-!
# Boundary-stratified carrier bound

At deficiency five the empty next ring separates boundary carriers from deep
carriers. Four boundary carriers are necessary, and deep carriers lose four
units of capacity. This improves the universal numerator from minus six to
minus seven for side lengths at least seven.
-/

namespace GridGraphs

open Finset SimpleGraph

private theorem component_card_le_box {n : Nat} {F : Finset (GridVertex n n)}
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (C : ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent)
    (lo width : Nat)
    (hbox : ∀ v ∈ C.supp,
      lo ≤ v.1.1.val ∧ v.1.1.val < lo + width ∧
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

/-- With five units of complementary boundary deficiency, nonboundary
preserved vertices lie in the twice-cropped square. -/
theorem boundary_five_mem_deep_of_not_boundary {n : Nat} (hn : 7 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 5)
    {v : GridVertex n n} (hv : v ∈ F) (hnb : ¬ IsGridBoundary v) :
    v ∈ BoundaryFiveConstruction.Deep n := by
  unfold IsGridBoundary at hnb
  have hrlo : 1 ≤ v.1.val := by omega
  have hrhi : v.1.val ≤ n - 2 := by omega
  have hclo : 1 ≤ v.2.val := by omega
  have hchi : v.2.val ≤ n - 2 := by omega
  have hside : ¬ (v.1.val = 1 ∨ v.1.val = n - 2 ∨
      v.2.val = 1 ∨ v.2.val = n - 2) := fun h =>
    boundaryDeficiencySum_compl_eq_five_next_ring_notMem hn F hacyc hb v
      hrlo hrhi hclo hchi h hv
  dsimp [BoundaryFiveConstruction.Deep]
  omega

/-- The refined length bound uses the full boundary-five set, with no
normalization hypothesis on its holes or its components. -/
theorem forced_card_le_boundary_stratified_components {n : Nat} (hn : 10 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic)
    (hb : boundaryDeficiencySum n n (univ \ F) = 5) :
    F.card ≤ (n - 4) *
      Fintype.card ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent + 7 := by
  classical
  let G := (gridGraph n n).induce (↑F : Set _)
  let B : Finset G.ConnectedComponent := univ.filter
    (fun C => ∃ v ∈ C.supp, IsGridBoundary v.1)
  have hdeep {v : GridVertex n n} (hv : v ∈ F) (hnb : ¬ IsGridBoundary v) :=
    boundary_five_mem_deep_of_not_boundary (by omega : 7 ≤ n) F hacyc hb hv hnb
  have hstep {u v : (↑F : Set (GridVertex n n))}
      (hu : IsGridBoundary u.1) (huv : G.Adj u v) : IsGridBoundary v.1 := by
    by_contra hv
    have hd := hdeep v.2 hv
    dsimp [BoundaryFiveConstruction.Deep] at hd
    unfold IsGridBoundary at hu
    change adjacent n n u.1 v.1 at huv
    simp only [adjacent, Fin.ext_iff] at huv
    omega
  have hwalk {u v : (↑F : Set (GridVertex n n))} (p : G.Walk u v)
      (hu : IsGridBoundary u.1) : IsGridBoundary v.1 := by
    induction p with
    | nil => exact hu
    | cons h p ih => exact ih (hstep hu h)
  have hboundary (C : G.ConnectedComponent) (hC : C ∈ B)
      (v : (↑F : Set (GridVertex n n))) (hv : v ∈ C.supp) : IsGridBoundary v.1 := by
    obtain ⟨u, hu, hub⟩ := (mem_filter.mp hC).2
    exact (C.reachable_of_mem_supp hu hv).elim (fun p => hwalk p hub)
  have hcap (C : G.ConnectedComponent) : C.supp.toFinset.card ≤ n :=
    component_card_le_box hacyc C 0 n (by intro v _; simp)
  have hdeepcap (C : G.ConnectedComponent) (hC : C ∉ B) :
      C.supp.toFinset.card ≤ n - 4 := by
    apply component_card_le_box hacyc C 2 (n - 4)
    intro v hv
    have hnb : ¬ IsGridBoundary v.1 := fun h =>
      hC (mem_filter.mpr ⟨mem_univ _, v, hv, h⟩)
    have hd := hdeep v.2 hnb
    dsimp [BoundaryFiveConstruction.Deep] at hd
    omega
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
      exact hboundary C hC v hv
    · intro hv
      refine ⟨G.connectedComponentMk v, mem_filter.mpr ⟨mem_univ _, ?_⟩, ?_⟩
      · exact ⟨v, by simp [ConnectedComponent.mem_supp_iff], hv⟩
      · simp [ConnectedComponent.mem_supp_iff]
  have hBcard : (∑ C ∈ B, C.supp.toFinset.card) = 4 * n - 9 := by
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
  have hBcap : 4 * n - 9 ≤ n * B.card := by
    rw [← hBcard]
    calc
      _ ≤ ∑ _C ∈ B, n := sum_le_sum (fun C _ => hcap C)
      _ = _ := by simp [Nat.mul_comm]
  have hfour : 4 ≤ B.card := by
    by_contra h
    have hle : B.card ≤ 3 := by omega
    have hmul := Nat.mul_le_mul_left n hle
    omega
  have hrest : (∑ C ∈ univ \ B, C.supp.toFinset.card) ≤
      (n - 4) * (Fintype.card G.ConnectedComponent - B.card) := by
    calc
      _ ≤ ∑ _C ∈ univ \ B, (n - 4) := sum_le_sum (fun C hC =>
        hdeepcap C (mem_sdiff.mp hC).2)
      _ = _ := by simp [card_sdiff_of_subset (subset_univ B), Nat.mul_comm]
  have hsplit := sum_sdiff (subset_univ B) (f := fun C : G.ConnectedComponent =>
    C.supp.toFinset.card)
  have hB_le : B.card ≤ Fintype.card G.ConnectedComponent := by
    simpa using card_le_card (subset_univ B)
  have hsub := Nat.sub_add_cancel hB_le
  have hscaled := congrArg (fun k => (n - 4) * k) hsub
  have hfourmul := Nat.mul_le_mul_left (n - 4) hfour
  rw [← htotal, hBcard] at hsplit
  change F.card ≤ (n - 4) * Fintype.card G.ConnectedComponent + 7
  have hnsub : n - 4 + 4 = n := by omega
  have hnine : 4 * n - 9 + 9 = 4 * n := by omega
  nlinarith

/-- Subtraction-free strengthened carrier inequality. -/
theorem forced_card_boundary_stratified_inequality {n : Nat} (hn : 7 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic) :
    (3 * n + 1) * F.card + 7 * n ≤ n * (n * n + 4 * n) := by
  classical
  by_cases hlarge : 10 ≤ n
  · have hboundary := five_le_boundaryDeficiencySum_compl (by omega) F hacyc
    have hledger := grid_component_reduction F hacyc
    have hpartition := boundaryDeficiencySum_add_compl n n F
    have htotal := total_boundaryDeficiencySum (by omega : 2 ≤ n) (by omega : 2 ≤ n)
    have hcomponent : 1 ≤ Fintype.card
        (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).ConnectedComponent := by
      apply Fintype.card_pos_iff.mpr
      exact ⟨(forcedEdgeGraph (gridGraph n n) (↑F : Set _)).connectedComponentMk
        (⟨0, by omega⟩, ⟨0, by omega⟩)⟩
    by_cases hb : boundaryDeficiencySum n n (univ \ F) = 5
    · have hlength := forced_card_le_boundary_stratified_components hlarge F hacyc hb
      have hbudget : 3 * F.card +
          Fintype.card ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent + 6 ≤
            n * n + 4 * n := by omega
      have hscaled := Nat.mul_le_mul_left (n - 4) hbudget
      have hrefined : (3 * (n - 4) + 1) * F.card + 6 * (n - 4) ≤
          (n - 4) * (n * n + 4 * n) + 7 := by nlinarith
      have hfinalscale := Nat.mul_le_mul_left (3 * n + 1) hrefined
      have hnsub : n - 4 + 4 = n := by omega
      have hmul : (3 * (n - 4) + 1) * ((3 * n + 1) * F.card + 7 * n) ≤
          (3 * (n - 4) + 1) * (n * (n * n + 4 * n)) := by nlinarith
      exact Nat.le_of_mul_le_mul_left hmul (by omega)
    · have hlength := forced_card_le_side_mul_components F hacyc
      have hbudget : 3 * F.card +
          Fintype.card ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent + 7 ≤
            n * n + 4 * n := by omega
      have hscaled := Nat.mul_le_mul_left n hbudget
      nlinarith
  · have h := forced_card_carrier_length_inequality (by omega) F hacyc
    have hcases : n = 7 ∨ n = 8 ∨ n = 9 := by omega
    rcases hcases with rfl | rfl | rfl <;> omega

/-- Every feasible set satisfies the numerator-minus-seven bound. -/
theorem forced_card_le_boundary_stratified_carrier_bound {n : Nat} (hn : 7 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic) :
    F.card ≤ n * (n * n + 4 * n - 7) / (3 * n + 1) := by
  have h := forced_card_boundary_stratified_inequality hn F hacyc
  have hnonneg : 7 ≤ n * n + 4 * n := by nlinarith
  have hsplit := congrArg (fun a : Nat => n * a) (Nat.sub_add_cancel hnonneg)
  apply (Nat.le_div_iff_mul_le (by omega : 0 < 3 * n + 1)).mpr
  nlinarith

/-- Universal square-grid maximum bound, strengthened by boundary stratification. -/
theorem maxPreserved_le_boundary_stratified_carrier_bound {n : Nat} (hn : 7 ≤ n) :
    maxPreserved n n ≤ n * (n * n + 4 * n - 7) / (3 * n + 1) := by
  classical
  rw [maxPreserved_eq_maxForcedAcyclic (by omega) (by omega)]
  unfold maxForcedAcyclic
  apply Finset.sup_le
  intro F hF
  exact forced_card_le_boundary_stratified_carrier_bound hn F (mem_acyclicForcedSets.mp hF)

/-- Residue-two polynomial form of the strengthened universal upper bound. -/
theorem maxPreserved_residueTwo_le_boundary_stratified {k : Nat} (hk : 2 ≤ k) :
    maxPreserved (3 * k + 2) (3 * k + 2) ≤
      3 * k ^ 2 + 7 * k + (2 * k + 3) / 3 := by
  apply (maxPreserved_le_boundary_stratified_carrier_bound (n := 3 * k + 2) (by omega)).trans
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul (by omega : 0 < 3 * (3 * k + 2) + 1)).mpr
  have hround : 2 * k + 1 ≤ 3 * ((2 * k + 3) / 3) := by omega
  have hscaled := Nat.mul_le_mul_left (9 * k + 7) hround
  have hpoly : (3 * k + 2) * (3 * k + 2) + 4 * (3 * k + 2) =
      9 * k ^ 2 + 24 * k + 12 := by ring
  have hcut : (3 * k + 2) * (3 * k + 2) + 4 * (3 * k + 2) - 7 =
      9 * k ^ 2 + 24 * k + 5 := by rw [hpoly]; omega
  rw [hcut]
  nlinarith

end GridGraphs
