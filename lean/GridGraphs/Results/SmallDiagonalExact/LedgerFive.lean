import GridGraphs.Results.SmallDiagonalExact.BoundaryFive
import GridGraphs.Accounting.CheckerboardComponent
import GridGraphs.Core.MaxPreserved

/-!
# The `5 x 5` component ledger and profile classification

Deficiency and straight-component bounds reduce twelve forced vertices to
eleven boundary vertices and one vertex at or next to the center.
-/

namespace GridGraphs.SmallDiagonalProof

open Finset SimpleGraph

lemma boundaryDeficiency55_le_corner_charge (v : GridVertex 5 5) :
    gridBoundaryDeficiency 5 5 v ≤ 1 + if v ∈ corners55 then 1 else 0 := by
  by_cases hr : v.1.val = 0 ∨ v.1.val + 1 = 5
  · by_cases hc : v.2.val = 0 ∨ v.2.val + 1 = 5
    · unfold gridBoundaryDeficiency
      rw [gridGraph_degree_corner (by omega) (by omega) v hr hc]
      have hv : v ∈ corners55 := by
        simp only [corners55, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hr, hc⟩
      simp [hv]
    · unfold gridBoundaryDeficiency
      rw [gridGraph_degree_border (by omega) (by omega) v (Or.inl ⟨hr, hc⟩)]
      simp [corners55]
  · by_cases hc : v.2.val = 0 ∨ v.2.val + 1 = 5
    · unfold gridBoundaryDeficiency
      rw [gridGraph_degree_border (by omega) (by omega) v (Or.inr ⟨hr, hc⟩)]
      simp [corners55]
    · unfold gridBoundaryDeficiency
      rw [gridGraph_degree_interior (by omega) (by omega) v hr hc]
      simp [corners55]

lemma boundaryDeficiencySum55_le (F : Finset (GridVertex 5 5)) :
    boundaryDeficiencySum 5 5 F ≤ F.card + (F ∩ corners55).card := by
  unfold boundaryDeficiencySum
  calc
    (∑ v ∈ F, gridBoundaryDeficiency 5 5 v) ≤
        ∑ v ∈ F, (1 + if v ∈ corners55 then 1 else 0) := by
      exact Finset.sum_le_sum fun v _ => boundaryDeficiency55_le_corner_charge v
    _ = F.card + (F ∩ corners55).card := by
      rw [Finset.sum_add_distrib]
      simp

lemma boundaryDeficiency55_eq_boundary_add_corner
    (v : GridVertex 5 5) :
    gridBoundaryDeficiency 5 5 v =
      (if v ∈ boundary55 then 1 else 0) +
        if v ∈ corners55 then 1 else 0 := by
  by_cases hr : v.1.val = 0 ∨ v.1.val + 1 = 5
  · by_cases hc : v.2.val = 0 ∨ v.2.val + 1 = 5
    · unfold gridBoundaryDeficiency
      rw [gridGraph_degree_corner (by omega) (by omega) v hr hc]
      have hvB : v ∈ boundary55 := by
        simp only [boundary55, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hr.elim Or.inl (fun h => Or.inr (Or.inl h))
      have hvC : v ∈ corners55 := by
        simp only [corners55, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hr, hc⟩
      simp [hvB, hvC]
    · unfold gridBoundaryDeficiency
      rw [gridGraph_degree_border (by omega) (by omega) v (Or.inl ⟨hr, hc⟩)]
      have hvB : v ∈ boundary55 := by
        simp only [boundary55, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hr.elim Or.inl (fun h => Or.inr (Or.inl h))
      have hvC : v ∉ corners55 := by
        simp only [corners55, Finset.mem_filter, Finset.mem_univ, true_and,
          not_and]
        exact fun _ => hc
      simp [hvB, hvC]
  · by_cases hc : v.2.val = 0 ∨ v.2.val + 1 = 5
    · unfold gridBoundaryDeficiency
      rw [gridGraph_degree_border (by omega) (by omega) v (Or.inr ⟨hr, hc⟩)]
      have hvB : v ∈ boundary55 := by
        simp only [boundary55, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hc.elim (fun h => Or.inr (Or.inr (Or.inl h)))
          (fun h => Or.inr (Or.inr (Or.inr h)))
      have hvC : v ∉ corners55 := by
        simp only [corners55, Finset.mem_filter, Finset.mem_univ, true_and,
          not_and]
        exact fun h => (hr h).elim
      simp [hvB, hvC]
    · unfold gridBoundaryDeficiency
      rw [gridGraph_degree_interior (by omega) (by omega) v hr hc]
      have hvB : v ∉ boundary55 := by
        simp only [boundary55, Finset.mem_filter, Finset.mem_univ, true_and,
          not_or]
        exact ⟨fun h => hr (Or.inl h), fun h => hr (Or.inr h),
          fun h => hc (Or.inl h), fun h => hc (Or.inr h)⟩
      have hvC : v ∉ corners55 := by
        simp only [corners55, Finset.mem_filter, Finset.mem_univ, true_and,
          not_and]
        exact fun h => (hr h).elim
      simp [hvB, hvC]

lemma boundaryDeficiencySum55_eq_boundary_add_corner
    (F : Finset (GridVertex 5 5)) :
    boundaryDeficiencySum 5 5 F =
      (F ∩ boundary55).card + (F ∩ corners55).card := by
  unfold boundaryDeficiencySum
  simp_rw [boundaryDeficiency55_eq_boundary_add_corner,
    Finset.sum_add_distrib, Finset.sum_boole]
  congr 1

noncomputable instance inducedComponentVertexFintype55
    (F : Finset (GridVertex 5 5))
    (C : ((gridGraph 5 5).induce
      (↑F : Set (GridVertex 5 5))).ConnectedComponent) : Fintype C :=
  Fintype.ofFinite C

/-- Straightness limits every induced forced component in a `5 x 5` grid to
five vertices. -/
lemma induced_forced_component_card_le_five
    (F : Finset (GridVertex 5 5))
    (hacyc : (forcedEdgeGraph (gridGraph 5 5)
      (↑F : Set (GridVertex 5 5))).IsAcyclic)
    (C : ((gridGraph 5 5).induce
      (↑F : Set (GridVertex 5 5))).ConnectedComponent) :
    Fintype.card C ≤ 5 := by
  rcases induced_forced_connectedComponent_straight hacyc C with
    ⟨r, hr⟩ | ⟨c, hc⟩
  · let project : C → Fin 5 := fun v => v.1.1.2
    have hinj : Function.Injective project := by
      intro u v huv
      apply Subtype.ext
      apply Subtype.ext
      apply Prod.ext
      · exact (hr u.1 u.2).trans (hr v.1 v.2).symm
      · exact huv
    simpa [project] using Fintype.card_le_of_injective project hinj
  · let project : C → Fin 5 := fun v => v.1.1.1
    have hinj : Function.Injective project := by
      intro u v huv
      apply Subtype.ext
      apply Subtype.ext
      apply Prod.ext
      · exact huv
      · exact (hc u.1 u.2).trans (hc v.1 v.2).symm
    simpa [project] using Fintype.card_le_of_injective project hinj

/-- A `5 x 5` forced set has at most five vertices per induced component. -/
lemma forced_card_le_five_mul_induced_components
    (F : Finset (GridVertex 5 5))
    (hacyc : (forcedEdgeGraph (gridGraph 5 5)
      (↑F : Set (GridVertex 5 5))).IsAcyclic) :
    F.card ≤ 5 * Fintype.card ((gridGraph 5 5).induce
      (↑F : Set (GridVertex 5 5))).ConnectedComponent := by
  classical
  let H := (gridGraph 5 5).induce (↑F : Set (GridVertex 5 5))
  have hpartition : ∑ C : H.ConnectedComponent, Fintype.card C = F.card := by
    calc
      ∑ C : H.ConnectedComponent, Fintype.card C =
          ∑ C : H.ConnectedComponent, C.supp.toFinset.card := by
        apply Finset.sum_congr rfl
        intro C _
        let e : C ≃ C.supp := {
          toFun v := ⟨v, v.property⟩
          invFun v := ⟨v, v.property⟩
          left_inv _ := rfl
          right_inv _ := rfl }
        exact (Fintype.card_congr e).trans (Set.toFinset_card C.supp).symm
      _ = ((Finset.univ : Finset H.ConnectedComponent).biUnion
          fun C => C.supp.toFinset).card := by
        rw [Finset.card_biUnion]
        intro C₁ _ C₂ _ hne
        simpa using pairwise_disjoint_supp_connectedComponent H hne
      _ = F.card := by
        have hunion : ((Finset.univ : Finset H.ConnectedComponent).biUnion
            fun C => C.supp.toFinset) = Finset.univ := by
          ext v
          simp [ConnectedComponent.mem_supp_iff]
        rw [hunion]
        simp
  rw [← hpartition]
  calc
    (∑ C : H.ConnectedComponent, Fintype.card C) ≤
        ∑ _C : H.ConnectedComponent, 5 := by
      exact Finset.sum_le_sum fun C _ =>
        induced_forced_component_card_le_five F hacyc C
    _ = 5 * Fintype.card H.ConnectedComponent := by simp [Nat.mul_comm]

/-- The straight-component ledger already rules out thirteen forced vertices
in the `5 x 5` grid.  Improving this partial bound is reduced to excluding the
twelve-vertex boundary profiles. -/
theorem _root_.GridGraphs.forced_five_five_card_le_twelve
    (F : Finset (GridVertex 5 5))
    (hacyc : (forcedEdgeGraph (gridGraph 5 5)
      (↑F : Set (GridVertex 5 5))).IsAcyclic) :
    F.card ≤ 12 := by
  have hcomponents := forced_card_le_five_mul_induced_components F hacyc
  have hledger := grid_component_reduction F hacyc
  have hdef := boundaryDeficiencySum55_le F
  have hcorners : (F ∩ corners55).card ≤ 4 := by
    have := Finset.card_le_card (Finset.inter_subset_right : F ∩ corners55 ⊆ corners55)
    rw [corners55_card] at this
    exact this
  have hforced : 1 ≤ Fintype.card
      (forcedEdgeGraph (gridGraph 5 5)
        (↑F : Set (GridVertex 5 5))).ConnectedComponent := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨(forcedEdgeGraph (gridGraph 5 5)
      (↑F : Set (GridVertex 5 5))).connectedComponentMk
        ((⟨0, by omega⟩, ⟨0, by omega⟩) : GridVertex 5 5)⟩
  by_contra hnot
  have hinduced : 3 ≤ Fintype.card ((gridGraph 5 5).induce
      (↑F : Set (GridVertex 5 5))).ConnectedComponent := by omega
  omega

/-- Unconditional operational consequence of the straight-component ledger. -/
theorem _root_.GridGraphs.maxPreserved_five_five_le_twelve : maxPreserved 5 5 ≤ 12 := by
  apply maxPreserved_le_of_forall
  intro T _ hT
  let F : Finset (GridVertex 5 5) :=
    Finset.univ.filter fun v => isPreserved 5 5 T v
  have hacyc : (forcedEdgeGraph (gridGraph 5 5)
      (↑F : Set (GridVertex 5 5))).IsAcyclic := by
    apply forcedEdgeGraph_isAcyclic_of_preserves hT.isAcyclic
    intro v hv
    apply preservesIncidentEdges_of_le_of_degree_eq (gridGraph 5 5) T hT.le
    change v ∈ F at hv
    exact (Finset.mem_filter.mp hv).2
  simpa [F, numPreserved] using forced_five_five_card_le_twelve F hacyc

/-- Exact component/deficiency alternatives left by the ledgers at cardinality
twelve.  The first alternative has a connected ambient forced forest; the
second uses all four available corner charges. -/
theorem _root_.GridGraphs.forced_five_five_twelve_ledger_profile
    (F : Finset (GridVertex 5 5)) (hcard : F.card = 12)
    (hacyc : (forcedEdgeGraph (gridGraph 5 5)
      (↑F : Set (GridVertex 5 5))).IsAcyclic) :
    let cInduced := Fintype.card ((gridGraph 5 5).induce
      (↑F : Set (GridVertex 5 5))).ConnectedComponent
    let cForced := Fintype.card (forcedEdgeGraph (gridGraph 5 5)
      (↑F : Set (GridVertex 5 5))).ConnectedComponent
    (boundaryDeficiencySum 5 5 F = 15 ∧ cInduced = 3 ∧ cForced = 1 ∧
        (((F ∩ corners55).card = 3 ∧ (F ∩ boundary55).card = 12) ∨
          ((F ∩ corners55).card = 4 ∧ (F ∩ boundary55).card = 11))) ∨
      (boundaryDeficiencySum 5 5 F = 16 ∧ cInduced + cForced = 5 ∧
        (F ∩ corners55).card = 4 ∧ (F ∩ boundary55).card = 12) := by
  dsimp
  have hcomponentBound := forced_card_le_five_mul_induced_components F hacyc
  have hledger := grid_component_reduction F hacyc
  have hdef := boundaryDeficiencySum55_le F
  have hdefExact := boundaryDeficiencySum55_eq_boundary_add_corner F
  have hcorners : (F ∩ corners55).card ≤ 4 := by
    have := Finset.card_le_card (Finset.inter_subset_right : F ∩ corners55 ⊆ corners55)
    rw [corners55_card] at this
    exact this
  have hforced : 1 ≤ Fintype.card
      (forcedEdgeGraph (gridGraph 5 5)
        (↑F : Set (GridVertex 5 5))).ConnectedComponent := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨(forcedEdgeGraph (gridGraph 5 5)
      (↑F : Set (GridVertex 5 5))).connectedComponentMk
        ((⟨0, by omega⟩, ⟨0, by omega⟩) : GridVertex 5 5)⟩
  have hinduced : 3 ≤ Fintype.card ((gridGraph 5 5).induce
      (↑F : Set (GridVertex 5 5))).ConnectedComponent := by omega
  have hboundary : (F ∩ boundary55).card ≤ 12 := by
    exact hcard ▸ Finset.card_le_card Finset.inter_subset_left
  by_cases hdef15 : boundaryDeficiencySum 5 5 F = 15
  · left
    constructor
    · exact hdef15
    constructor
    · omega
    constructor
    · omega
    omega
  · right
    constructor
    · omega
    constructor
    · omega
    constructor <;> omega

/-- A forced set supported on the boundary of the `5 x 5` grid cannot have a
connected forced-edge graph.  The central vertex has no boundary neighbor, so
it is isolated from (for example) the north-west corner. -/
theorem _root_.GridGraphs.forced_five_five_boundary_supported_two_forced_components
    (F : Finset (GridVertex 5 5)) (hF : F ⊆ boundary55) :
    2 ≤ Fintype.card (forcedEdgeGraph (gridGraph 5 5)
      (↑F : Set (GridVertex 5 5))).ConnectedComponent := by
  classical
  let H := forcedEdgeGraph (gridGraph 5 5)
    (↑F : Set (GridVertex 5 5))
  let z : GridVertex 5 5 := (⟨2, by omega⟩, ⟨2, by omega⟩)
  let a : GridVertex 5 5 := (⟨0, by omega⟩, ⟨0, by omega⟩)
  have hzIsolated : ∀ x, ¬H.Adj z x := by
    intro x hx
    have hxGrid : (gridGraph 5 5).Adj z x := hx.1
    have hzNotF : z ∉ F := by
      intro hzF
      have hzB := hF hzF
      simp [boundary55, z] at hzB
    have hxF : x ∈ F := hx.2.resolve_left hzNotF
    have hxB := hF hxF
    change adjacent 5 5 z x at hxGrid
    dsimp [z] at hxGrid
    simp only [boundary55, Finset.mem_filter, Finset.mem_univ, true_and] at hxB
    rcases hxGrid with ⟨hrow, hcol⟩ | ⟨hcol, hrow⟩
    · have hrowVal := congrArg Fin.val hrow
      norm_num at hrowVal
      rcases hcol with hcol | hcol <;> norm_num at hcol <;>
        rcases hxB with hr | hr | hc | hc <;> omega
    · have hcolVal := congrArg Fin.val hcol
      norm_num at hcolVal
      rcases hrow with hrow | hrow <;> norm_num at hrow <;>
        rcases hxB with hr | hr | hc | hc <;> omega
  have hza : z ≠ a := by
    intro h
    have := congrArg (fun v : GridVertex 5 5 => v.1.val) h
    norm_num [z, a] at this
  have hcomponents : H.connectedComponentMk z ≠ H.connectedComponentMk a := by
    intro heq
    have hreach := ConnectedComponent.exact heq
    have hzSupport := SimpleGraph.mem_support_of_reachable hza hreach
    obtain ⟨x, hzx⟩ := (SimpleGraph.mem_support H).mp hzSupport
    exact hzIsolated x hzx
  let Q : Finset H.ConnectedComponent :=
    {H.connectedComponentMk z, H.connectedComponentMk a}
  have hQcard : Q.card = 2 := by simp [Q, hcomponents]
  have hQsub : Q ⊆ (Finset.univ : Finset H.ConnectedComponent) :=
    Finset.subset_univ Q
  have := Finset.card_le_card hQsub
  simpa [H, hQcard] using this

/-- The boundary-only, exactly-three-corners alternative in the first branch
of `forced_five_five_twelve_ledger_profile` is impossible. -/
theorem _root_.GridGraphs.forced_five_five_twelve_boundary_three_corners_impossible
    (F : Finset (GridVertex 5 5)) (hcard : F.card = 12)
    (_hacyc : (forcedEdgeGraph (gridGraph 5 5)
      (↑F : Set (GridVertex 5 5))).IsAcyclic)
    (hprofile : boundaryDeficiencySum 5 5 F = 15 ∧
      Fintype.card ((gridGraph 5 5).induce
        (↑F : Set (GridVertex 5 5))).ConnectedComponent = 3 ∧
      Fintype.card (forcedEdgeGraph (gridGraph 5 5)
        (↑F : Set (GridVertex 5 5))).ConnectedComponent = 1 ∧
      (F ∩ corners55).card = 3 ∧ (F ∩ boundary55).card = 12) : False := by
  have hFboundary : F ⊆ boundary55 := by
    have hinter : F ∩ boundary55 = F := by
      apply Finset.eq_of_subset_of_card_le Finset.inter_subset_left
      rw [hprofile.2.2.2.2, hcard]
    intro v hv
    have : v ∈ F ∩ boundary55 := by simpa [hinter] using hv
    exact (Finset.mem_inter.mp this).2
  have htwo := forced_five_five_boundary_supported_two_forced_components
    F hFboundary
  omega

/-- Geometry forced by the sole twelve-vertex ledger profile not eliminated
above.  There is one non-boundary forced vertex; connectedness forces it to be
the center or a neighbor of the center.  The four corner-cell obstructions
also force an omission next to every corner. -/
theorem _root_.GridGraphs.forced_five_five_twelve_final_profile_reduction
    (F : Finset (GridVertex 5 5)) (hcard : F.card = 12)
    (hacyc : (forcedEdgeGraph (gridGraph 5 5)
      (↑F : Set (GridVertex 5 5))).IsAcyclic)
    (hcornersCard : (F ∩ corners55).card = 4)
    (hboundaryCard : (F ∩ boundary55).card = 11)
    (hforcedConnected : Fintype.card (forcedEdgeGraph (gridGraph 5 5)
      (↑F : Set (GridVertex 5 5))).ConnectedComponent = 1) :
    corners55 ⊆ F ∧
      ((0, 1) ∉ F ∨ (1, 0) ∉ F) ∧
      ((0, 3) ∉ F ∨ (1, 4) ∉ F) ∧
      ((3, 4) ∉ F ∨ (4, 3) ∉ F) ∧
      ((4, 1) ∉ F ∨ (3, 0) ∉ F) ∧
      ∃ x : GridVertex 5 5,
        F \ boundary55 = {x} ∧ x ∈ F ∧ x ∉ boundary55 ∧
          (x = (2, 2) ∨ (gridGraph 5 5).Adj (2, 2) x) := by
  classical
  have hcorners : corners55 ⊆ F := by
    have hinter : F ∩ corners55 = corners55 :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by
        rw [hcornersCard, corners55_card])
    intro v hv
    have : v ∈ F ∩ corners55 := by simpa [hinter] using hv
    exact (Finset.mem_inter.mp this).1
  have hcorner00 : ((0, 0) : GridVertex 5 5) ∈ F := hcorners (by simp [corners55])
  have hcorner04 : ((0, 4) : GridVertex 5 5) ∈ F := hcorners (by simp [corners55])
  have hcorner44 : ((4, 4) : GridVertex 5 5) ∈ F := hcorners (by simp [corners55])
  have hcorner40 : ((4, 0) : GridVertex 5 5) ∈ F := hcorners (by simp [corners55])
  have homit00 : (0, 1) ∉ F ∨ (1, 0) ∉ F := by
    by_contra h
    push Not at h
    exact (grid_cell_forced_triples_free (F := (↑F : Set _))
      (⟨0, by omega⟩ : Fin (5 - 1)) (⟨0, by omega⟩ : Fin (5 - 1)) hacyc).2.2.2
      (by simpa [cell10, cell00, cell01] using ⟨h.2, hcorner00, h.1⟩)
  have homit04 : (0, 3) ∉ F ∨ (1, 4) ∉ F := by
    by_contra h
    push Not at h
    exact (grid_cell_forced_triples_free (F := (↑F : Set _))
      (⟨0, by omega⟩ : Fin (5 - 1)) (⟨3, by omega⟩ : Fin (5 - 1)) hacyc).1
      (by simpa [cell00, cell01, cell11] using ⟨h.1, hcorner04, h.2⟩)
  have homit44 : (3, 4) ∉ F ∨ (4, 3) ∉ F := by
    by_contra h
    push Not at h
    exact (grid_cell_forced_triples_free (F := (↑F : Set _))
      (⟨3, by omega⟩ : Fin (5 - 1)) (⟨3, by omega⟩ : Fin (5 - 1)) hacyc).2.1
      (by simpa [cell01, cell11, cell10] using ⟨h.1, hcorner44, h.2⟩)
  have homit40 : (4, 1) ∉ F ∨ (3, 0) ∉ F := by
    by_contra h
    push Not at h
    exact (grid_cell_forced_triples_free (F := (↑F : Set _))
      (⟨3, by omega⟩ : Fin (5 - 1)) (⟨0, by omega⟩ : Fin (5 - 1)) hacyc).2.2.1
      (by simpa [cell11, cell10, cell00] using ⟨h.1, hcorner40, h.2⟩)
  have houtsideCard : (F \ boundary55).card = 1 := by
    have hboundaryCard' : (boundary55 ∩ F).card = 11 := by
      simpa [Finset.inter_comm] using hboundaryCard
    rw [Finset.card_sdiff, hboundaryCard', hcard]
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp houtsideCard
  have hxF : x ∈ F := by
    have : x ∈ F \ boundary55 := by simp [hx]
    exact (Finset.mem_sdiff.mp this).1
  have hxNotBoundary : x ∉ boundary55 := by
    have : x ∈ F \ boundary55 := by simp [hx]
    exact (Finset.mem_sdiff.mp this).2
  let z : GridVertex 5 5 := (2, 2)
  have hzNotBoundary : z ∉ boundary55 := by simp [z, boundary55]
  have hxLocation : x = z ∨ (gridGraph 5 5).Adj z x := by
    by_cases hxz : x = z
    · exact Or.inl hxz
    · have hzNotF : z ∉ F := by
        intro hzF
        have hzOutside : z ∈ F \ boundary55 := Finset.mem_sdiff.mpr ⟨hzF, hzNotBoundary⟩
        have : z = x := by simpa [hx] using hzOutside
        exact hxz this.symm
      let H := forcedEdgeGraph (gridGraph 5 5) (↑F : Set (GridVertex 5 5))
      obtain ⟨C, hC⟩ := (Finset.card_eq_one (s := (Finset.univ : Finset H.ConnectedComponent))).mp (by
        simpa [H] using hforcedConnected)
      have hzC : H.connectedComponentMk z = C := by
        have hzmem : H.connectedComponentMk z ∈
            (Finset.univ : Finset H.ConnectedComponent) := Finset.mem_univ _
        rw [hC] at hzmem
        simpa using hzmem
      have hxC : H.connectedComponentMk x = C := by
        have hxmem : H.connectedComponentMk x ∈
            (Finset.univ : Finset H.ConnectedComponent) := Finset.mem_univ _
        rw [hC] at hxmem
        simpa using hxmem
      have hreach : H.Reachable z x :=
        ConnectedComponent.exact (hzC.trans hxC.symm)
      have hzSupport := SimpleGraph.mem_support_of_reachable (Ne.symm hxz) hreach
      obtain ⟨y, hzy⟩ := (SimpleGraph.mem_support H).mp hzSupport
      have hyF : y ∈ F := hzy.2.resolve_left hzNotF
      have hyNotBoundary : y ∉ boundary55 := by
        have hzyGrid : (gridGraph 5 5).Adj z y := hzy.1
        change adjacent 5 5 z y at hzyGrid
        dsimp [z] at hzyGrid
        simp only [boundary55, Finset.mem_filter, Finset.mem_univ, true_and,
          not_or]
        rcases hzyGrid with ⟨hrow, hcol⟩ | ⟨hcol, hrow⟩
        · have hrowVal := congrArg Fin.val hrow
          norm_num at hrowVal
          rcases hcol with hcol | hcol <;> norm_num at hcol <;> omega
        · have hcolVal := congrArg Fin.val hcol
          norm_num at hcolVal
          rcases hrow with hrow | hrow <;> norm_num at hrow <;> omega
      have hyOutside : y ∈ F \ boundary55 :=
        Finset.mem_sdiff.mpr ⟨hyF, hyNotBoundary⟩
      have hyx : y = x := by simpa [hx] using hyOutside
      exact Or.inr (hyx ▸ hzy.1)
  refine ⟨hcorners, homit00, homit04, homit44, homit40, x, hx, hxF,
    hxNotBoundary, ?_⟩
  simpa [z] using hxLocation

/-- The straight-component reduction supplies two of the six checkerboard
component credits sought by the unfinished `5 x 5` analysis.  The remaining
four credits are the `12`-vertex perimeter obstruction isolated by
`forced_five_five_twelve_ledger_profile`. -/
theorem _root_.GridGraphs.five_checkerboard_component_two_credit
    (F : Finset (GridVertex 5 5))
    (hacyc : (forcedEdgeGraph (gridGraph 5 5)
      (↑F : Set (GridVertex 5 5))).IsAcyclic) :
    boundaryDeficiencySum 5 5 F + 2 ≤
      Fintype.card (forcedEdgeGraph (gridGraph 5 5)
        (↑(blackCenters F) : Set (GridVertex 5 5))).ConnectedComponent +
      Fintype.card (forcedEdgeGraph (gridGraph 5 5)
        (↑(whiteCenters F) : Set (GridVertex 5 5))).ConnectedComponent := by
  have hcard := forced_five_five_card_le_twelve F hacyc
  have hchecker := grid_checkerboard_ambient_component_reduction F hacyc
  omega

end GridGraphs.SmallDiagonalProof
