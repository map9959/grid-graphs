import GridGraphs.FiniteDiagonalConstructions
import GridGraphs.StraightForcedComponents
import GridGraphs.ComponentReduction
import GridGraphs.CheckerboardComponent
import GridGraphs.GridBoundaryCycle
import GridGraphs.PerimeterWaste

/-!
# Exact `3 x 3` and `5 x 5` values

The `3 x 3` value is proved exactly using only the forced-forest component
ledger and the local straightness obstruction.  The `5 x 5` argument reduces
the extremal ledger profile to four rotated boundary-attachment cases and
excludes each one by an explicit forced six-cycle.  No spanning trees or
vertex sets are enumerated.
-/

namespace GridGraphs

open Finset SimpleGraph

private def corners33 : Finset (GridVertex 3 3) :=
  Finset.univ.filter fun v =>
    (v.1.val = 0 ∨ v.1.val + 1 = 3) ∧
      (v.2.val = 0 ∨ v.2.val + 1 = 3)

private lemma corners33_card : corners33.card = 4 := by
  let endpoints : Finset (Fin 3) := {0, 2}
  have hcorners : corners33 = endpoints ×ˢ endpoints := by
    ext v
    rw [Finset.mem_product]
    simp only [corners33, Finset.mem_filter, Finset.mem_univ, true_and,
      endpoints, Finset.mem_insert, Finset.mem_singleton]
    constructor <;> rintro ⟨hr, hc⟩
    · constructor
      · rcases hr with h | h
        · left; apply Fin.ext; omega
        · right; apply Fin.ext; omega
      · rcases hc with h | h
        · left; apply Fin.ext; omega
        · right; apply Fin.ext; omega
    · constructor
      · rcases hr with h | h
        · left; simpa [h]
        · right; have := congrArg Fin.val h; norm_num at this ⊢; omega
      · rcases hc with h | h
        · left; simpa [h]
        · right; have := congrArg Fin.val h; norm_num at this ⊢; omega
  have hendpoints : endpoints.card = 2 := by
    rw [Finset.card_pair]
    intro h
    have := congrArg Fin.val h
    norm_num at this
  rw [hcorners, Finset.card_product, hendpoints]

private lemma boundaryDeficiency33_le_corner_charge (v : GridVertex 3 3) :
    gridBoundaryDeficiency 3 3 v ≤ 1 + if v ∈ corners33 then 1 else 0 := by
  by_cases hr : v.1.val = 0 ∨ v.1.val + 1 = 3
  · by_cases hc : v.2.val = 0 ∨ v.2.val + 1 = 3
    · unfold gridBoundaryDeficiency
      rw [gridGraph_degree_corner (by omega) (by omega) v hr hc]
      have hv : v ∈ corners33 := by
        simp only [corners33, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hr, hc⟩
      simp [hv]
    · unfold gridBoundaryDeficiency
      rw [gridGraph_degree_border (by omega) (by omega) v (Or.inl ⟨hr, hc⟩)]
      simp [corners33]
  · by_cases hc : v.2.val = 0 ∨ v.2.val + 1 = 3
    · unfold gridBoundaryDeficiency
      rw [gridGraph_degree_border (by omega) (by omega) v (Or.inr ⟨hr, hc⟩)]
      simp [corners33]
    · unfold gridBoundaryDeficiency
      rw [gridGraph_degree_interior (by omega) (by omega) v hr hc]
      simp [corners33]

private lemma boundaryDeficiencySum33_le (F : Finset (GridVertex 3 3)) :
    boundaryDeficiencySum 3 3 F ≤ F.card + (F ∩ corners33).card := by
  unfold boundaryDeficiencySum
  calc
    (∑ v ∈ F, gridBoundaryDeficiency 3 3 v) ≤
        ∑ v ∈ F, (1 + if v ∈ corners33 then 1 else 0) := by
      exact Finset.sum_le_sum fun v _ => boundaryDeficiency33_le_corner_charge v
    _ = F.card + (F ∩ corners33).card := by
      rw [Finset.sum_add_distrib]
      simp

private lemma two_le_induced_component_count_of_card_five
    (F : Finset (GridVertex 3 3)) (hFcard : F.card = 5)
    (hacyc : (forcedEdgeGraph (gridGraph 3 3)
      (↑F : Set (GridVertex 3 3))).IsAcyclic) :
    2 ≤ Fintype.card ((gridGraph 3 3).induce
      (↑F : Set (GridVertex 3 3))).ConnectedComponent := by
  classical
  let H := (gridGraph 3 3).induce (↑F : Set (GridVertex 3 3))
  have hnot : ¬∀ u v : (↑F : Set (GridVertex 3 3)), H.Reachable u v := by
    intro hall
    have hnonempty : (Set.univ : Set (↑F : Set (GridVertex 3 3))).Nonempty := by
      obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < F.card)
      exact ⟨⟨v, hv⟩, Set.mem_univ _⟩
    have hstraight := induced_forced_preconnected_set_straight hacyc hnonempty
      (fun _ _ _ _ => hall _ _)
    rcases hstraight with ⟨r, hr⟩ | ⟨c, hc⟩
    · have hinj : Function.Injective
          (fun v : (↑F : Set (GridVertex 3 3)) => v.1.2) := by
        intro u v huv
        apply Subtype.ext
        apply Prod.ext
        · exact (hr u (Set.mem_univ u)).trans (hr v (Set.mem_univ v)).symm
        · exact huv
      have hcard := Fintype.card_le_of_injective _ hinj
      simpa [hFcard] using hcard
    · have hinj : Function.Injective
          (fun v : (↑F : Set (GridVertex 3 3)) => v.1.1) := by
        intro u v huv
        apply Subtype.ext
        apply Prod.ext
        · exact huv
        · exact (hc u (Set.mem_univ u)).trans (hc v (Set.mem_univ v)).symm
      have hcard := Fintype.card_le_of_injective _ hinj
      simpa [hFcard] using hcard
  push_neg at hnot
  obtain ⟨u, v, huv⟩ := hnot
  let cu := H.connectedComponentMk u
  let cv := H.connectedComponentMk v
  have hcne : cu ≠ cv := by
    intro h
    exact huv (ConnectedComponent.exact h)
  let pairComponents : Finset H.ConnectedComponent := {cu, cv}
  have hpair : pairComponents.card = 2 := by
    simp [pairComponents, hcne]
  have hsub : pairComponents ⊆ (Finset.univ : Finset H.ConnectedComponent) :=
    Finset.subset_univ _
  have := Finset.card_le_card hsub
  simpa [H, hpair] using this

private lemma perimeter_edge_has_corner33 {u v : GridVertex 3 3}
    (h : IsPerimeterEdge 3 u v) : u ∈ corners33 ∨ v ∈ corners33 := by
  rcases h with ⟨hadj, hu, hv⟩
  unfold IsBoundaryVertex at hu hv
  unfold gridGraph adjacent at hadj
  simp only [corners33, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases hadj with ⟨hrow, hcol⟩ | ⟨hcol, hrow⟩
  · have hrowval := congrArg Fin.val hrow
    rcases hcol with hcol | hcol <;> omega
  · have hcolval := congrArg Fin.val hcol
    rcases hrow with hrow | hrow <;> omega

private lemma numPreserved_three_three_le_four
    (T : SimpleGraph (GridVertex 3 3)) [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph 3 3) T) :
    numPreserved 3 3 T ≤ 4 := by
  have hbasic := preserved_le_refinedUB (m := 3) (n := 3) (by omega) (by omega) hT
  simp only [refinedUB, I, D] at hbasic
  norm_num at hbasic
  by_contra hnot
  have hscore : numPreserved 3 3 T = 5 := by omega
  let F : Finset (GridVertex 3 3) :=
    Finset.univ.filter fun v => isPreserved 3 3 T v
  have hFcard : F.card = 5 := by simpa [F, numPreserved] using hscore
  have hacyc : (forcedEdgeGraph (gridGraph 3 3)
      (↑F : Set (GridVertex 3 3))).IsAcyclic := by
    apply forcedEdgeGraph_isAcyclic_of_preserves hT.isAcyclic
    intro v hv
    apply preservesIncidentEdges_of_le_of_degree_eq (gridGraph 3 3) T hT.le
    change v ∈ F at hv
    exact (Finset.mem_filter.mp hv).2
  have hcomponent := grid_component_reduction F hacyc
  have hinduced := two_le_induced_component_count_of_card_five F hFcard hacyc
  have hforced : 1 ≤ Fintype.card
      (forcedEdgeGraph (gridGraph 3 3)
        (↑F : Set (GridVertex 3 3))).ConnectedComponent := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨(forcedEdgeGraph (gridGraph 3 3)
      (↑F : Set (GridVertex 3 3))).connectedComponentMk
        ((⟨0, by omega⟩, ⟨0, by omega⟩) : GridVertex 3 3)⟩
  have hdef : 9 ≤ boundaryDeficiencySum 3 3 F := by omega
  have hdefUpper := boundaryDeficiencySum33_le F
  have hcornersCard : (F ∩ corners33).card = 4 := by
    have hinter : (F ∩ corners33).card ≤ corners33.card :=
      Finset.card_le_card (Finset.inter_subset_right)
    rw [corners33_card] at hinter
    omega
  have hcorners : corners33 ⊆ F := by
    have hinterEq : F ∩ corners33 = corners33 := by
      exact Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by
        rw [hcornersCard, corners33_card])
    intro v hv
    have : v ∈ F ∩ corners33 := by simpa [hinterEq] using hv
    exact (Finset.mem_inter.mp this).1
  obtain ⟨u, v, hperimeter, huv⟩ := exists_omitted_perimeter_edge (n := 3)
    (by omega) hT
  rcases perimeter_edge_has_corner33 hperimeter with hu | hv
  · exact huv (preservesIncidentEdges_of_le_of_degree_eq
      (gridGraph 3 3) T hT.le u
      ((Finset.mem_filter.mp (hcorners hu)).2) hperimeter.1)
  · exact huv (T.symm (preservesIncidentEdges_of_le_of_degree_eq
      (gridGraph 3 3) T hT.le v
      ((Finset.mem_filter.mp (hcorners hv)).2) hperimeter.1.symm))

/-- Exactly four vertices can be preserved in the `3 x 3` grid. -/
theorem maxPreserved_three_three : maxPreserved 3 3 = 4 := by
  exact Nat.le_antisymm
    (maxPreserved_le_of_forall fun T _ hT => numPreserved_three_three_le_four T hT)
    four_le_maxPreserved_three_three

/-! ## Partial `5 x 5` structural reduction -/

private def corners55 : Finset (GridVertex 5 5) :=
  Finset.univ.filter fun v =>
    (v.1.val = 0 ∨ v.1.val + 1 = 5) ∧
      (v.2.val = 0 ∨ v.2.val + 1 = 5)

private def boundary55 : Finset (GridVertex 5 5) :=
  Finset.univ.filter fun v =>
    v.1.val = 0 ∨ v.1.val + 1 = 5 ∨
      v.2.val = 0 ∨ v.2.val + 1 = 5

private def boundaryPosition55 (i : Fin 16) : GridBoundaryPosition 5 5 :=
  ⟨i.val, by simpa [gridBoundaryLength] using i.isLt⟩

private def boundaryVertex55 (i : Fin 16) : GridVertex 5 5 :=
  gridBoundaryVertex (m := 5) (n := 5) (by omega) (by omega)
    (boundaryPosition55 i)

/-- Boundary positions occupied by a forced set, in clockwise cyclic order. -/
def boundaryForcedPositions55 (F : Finset (GridVertex 5 5)) : Finset (Fin 16) :=
  Finset.univ.filter fun i =>
    boundaryVertex55 i ∈ F

/-- The path forest formed by the cyclic boundary runs of `F`. -/
def boundaryForcedRunGraph55 (F : Finset (GridVertex 5 5)) :
    SimpleGraph (↑(boundaryForcedPositions55 F) : Set (Fin 16)) :=
  (cycleGraph 16).induce (↑(boundaryForcedPositions55 F) : Set (Fin 16))

/-- Number of cyclic boundary `F`-runs. -/
noncomputable def boundaryForcedRunCount55 (F : Finset (GridVertex 5 5)) : Nat :=
  Fintype.card (boundaryForcedRunGraph55 F).ConnectedComponent

private lemma boundaryPosition55_succ (i : Fin 16) :
    gridBoundarySucc (m := 5) (n := 5) (by omega) (by omega)
      (boundaryPosition55 i) = boundaryPosition55 (i + 1) := by
  apply Fin.ext
  rfl

/-- The clockwise boundary numbering embeds the abstract `16`-cycle in the
`5 x 5` grid. -/
private def gridBoundaryCycleHom55 : cycleGraph 16 →g gridGraph 5 5 where
  toFun := boundaryVertex55
  map_rel' := by
    intro i j hij
    have hj : j = i - 1 ∨ j = i + 1 := by
      have hjmem : j ∈ (cycleGraph 16).neighborSet i := hij
      rw [cycleGraph_neighborSet] at hjmem
      simpa [eq_comm] using hjmem
    rcases hj with h | h
    · have hi : i = j + 1 := by
        rw [h]
        simp
      rw [hi]
      change (gridGraph 5 5).Adj (boundaryVertex55 (j + 1)) (boundaryVertex55 j)
      rw [boundaryVertex55, boundaryVertex55, ← boundaryPosition55_succ]
      exact (gridBoundaryVertex_succ_adj (m := 5) (n := 5)
        (by omega) (by omega) (boundaryPosition55 j)).symm
    · rw [h]
      change (gridGraph 5 5).Adj (boundaryVertex55 i) (boundaryVertex55 (i + 1))
      rw [boundaryVertex55, boundaryVertex55, ← boundaryPosition55_succ]
      exact gridBoundaryVertex_succ_adj (m := 5) (n := 5)
        (by omega) (by omega) (boundaryPosition55 i)

set_option maxHeartbeats 800000 in
private lemma gridBoundaryCycleHom55_reflects_adj {i j : Fin 16}
    (hij : (gridGraph 5 5).Adj (boundaryVertex55 i) (boundaryVertex55 j)) :
    (cycleGraph 16).Adj i j := by
  rw [cycleGraph_adj']
  change adjacent 5 5 (boundaryVertex55 i) (boundaryVertex55 j) at hij
  simp only [boundaryVertex55, boundaryPosition55, gridBoundaryVertex] at hij
  split_ifs at hij <;>
    simp only [adjacent, Prod.fst, Prod.snd, Fin.mk.injEq] at hij <;>
    simp only [Fin.sub_def] <;>
    rcases hij with ⟨h, h'⟩ | ⟨h, h'⟩ <;>
    rcases h' with h' | h'
  all_goals norm_num [gridBoundaryLength] at *
  all_goals
    have hmod :
        (16 - j.val + i.val = 1 ∨ 16 - j.val + i.val = 17) ∨
        (16 - i.val + j.val = 1 ∨ 16 - i.val + j.val = 17) := by
      omega
    rcases hmod with (h | h) | (h | h) <;> simp [h]

/-- Inclusion of a cyclic boundary run into the ambient induced forced graph. -/
def boundaryForcedRunToInducedHom55 (F : Finset (GridVertex 5 5)) :
    boundaryForcedRunGraph55 F →g
      (gridGraph 5 5).induce (↑F : Set (GridVertex 5 5)) where
  toFun i := ⟨gridBoundaryCycleHom55 i.1, by
    simpa [boundaryForcedPositions55] using i.2⟩
  map_rel' := by
    intro i j hij
    exact gridBoundaryCycleHom55.map_rel hij

/-- Ambient induced component containing a cyclic boundary run. -/
def boundaryForcedRunAncestor55 (F : Finset (GridVertex 5 5))
    (C : (boundaryForcedRunGraph55 F).ConnectedComponent) :
    ((gridGraph 5 5).induce
      (↑F : Set (GridVertex 5 5))).ConnectedComponent :=
  C.map (boundaryForcedRunToInducedHom55 F)

private lemma cycleGraph_sixteen_adj_not_both_odd {i j : Fin 16}
    (hij : (cycleGraph 16).Adj i j) :
    ¬(i.val % 2 = 1 ∧ j.val % 2 = 1) := by
  intro hodd
  have hj : j = i - 1 ∨ j = i + 1 := by
    have hjmem : j ∈ (cycleGraph 16).neighborSet i := hij
    rw [cycleGraph_neighborSet] at hjmem
    simpa [eq_comm] using hjmem
  have succ_not_both_odd (x : Fin 16)
      (hx : x.val % 2 = 1) (hsucc : (x + 1).val % 2 = 1) : False := by
    change ((x.val + 1) % 16) % 2 = 1 at hsucc
    by_cases hxlast : x.val + 1 < 16
    · rw [Nat.mod_eq_of_lt hxlast] at hsucc
      omega
    · have : x.val + 1 = 16 := by omega
      simp [this] at hsucc
  rcases hj with h | h
  · have hi : i = j + 1 := by rw [h]; simp
    rw [hi] at hodd
    exact succ_not_both_odd j hodd.2 hodd.1
  · rw [h] at hodd
    exact succ_not_both_odd i hodd.1 hodd.2

private lemma boundaryForcedRunCount55_three_le_of_four_odd_omissions
    (F : Finset (GridVertex 5 5)) (Q : Finset (Fin 16))
    (hacyc : (forcedEdgeGraph (gridGraph 5 5)
      (↑F : Set (GridVertex 5 5))).IsAcyclic)
    (hPcard : (boundaryForcedPositions55 F).card = 11)
    (hQcard : Q.card = 4)
    (hQomit : Q ⊆ (Finset.univ : Finset (Fin 16)) 
      \ boundaryForcedPositions55 F)
    (hQodd : ∀ q ∈ Q, q.val % 2 = 1) :
    3 ≤ boundaryForcedRunCount55 F := by
  classical
  let G := cycleGraph 16
  let P := boundaryForcedPositions55 F
  let A := forcedEdgeGraph G (↑Q : Set (Fin 16))
  let B := boundaryForcedRunGraph55 F
  have hdeg (i : Fin 16) : G.degree i = 2 := by
    dsimp [G]
    rw [cycleGraph_degree_two_le, Finset.card_pair]
    intro heq
    have hi : i = i + 2 := by
      have := congrArg (fun x => x + 1) heq
      simpa [sub_eq_add_neg, add_assoc] using this
    have hzero : (0 : Fin 16) = 2 :=
      add_left_cancel (a := i) (by simpa using hi)
    have := congrArg Fin.val hzero
    norm_num at this
  have hQinduced : (G.induce (↑Q : Set (Fin 16))).edgeFinset.card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro e he
    induction e using Sym2.inductionOn with
    | _ i j =>
        rw [SimpleGraph.mem_edgeFinset] at he
        exact cycleGraph_sixteen_adj_not_both_odd he
          ⟨hQodd i i.2, hQodd j j.2⟩
  have hAcard : A.edgeFinset.card = 8 := by
    have hsum := sum_degrees_finset_eq_forced_add_induced G Q
    rw [Finset.sum_congr rfl (fun i _ => hdeg i), hQinduced] at hsum
    simp [hQcard] at hsum
    norm_num [A] at hsum ⊢
    exact hsum.symm
  let E := B.edgeFinset.map
    (Function.Embedding.subtype (↑P : Set (Fin 16))).sym2Map
  have hEcard : E.card = B.edgeFinset.card := by simp [E]
  have hEsub : E ⊆ G.edgeFinset := by
    intro e he
    simp only [E, Finset.mem_map] at he
    obtain ⟨e', he', rfl⟩ := he
    induction e' using Sym2.inductionOn with
    | _ i j =>
        rw [SimpleGraph.mem_edgeFinset] at he' ⊢
        exact he'
  have hAsub : A.edgeFinset ⊆ G.edgeFinset := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ i j =>
        rw [SimpleGraph.mem_edgeFinset] at he ⊢
        exact he.1
  have hdisjoint : Disjoint A.edgeFinset E := by
    rw [Finset.disjoint_left]
    intro e heA heE
    induction e using Sym2.inductionOn with
    | _ i j =>
        rw [SimpleGraph.mem_edgeFinset] at heA
        simp only [E, Finset.mem_map] at heE
        obtain ⟨e', he', heq⟩ := heE
        induction e' using Sym2.inductionOn with
        | _ u v =>
            change s(u.1, v.1) = s(i, j) at heq
            rw [Sym2.eq_iff] at heq
            rw [SimpleGraph.mem_edgeFinset] at he'
            rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · rcases heA.2 with hi | hj
              · exact (Finset.mem_sdiff.mp (hQomit hi)).2 u.2
              · exact (Finset.mem_sdiff.mp (hQomit hj)).2 v.2
            · rcases heA.2 with hi | hj
              · exact (Finset.mem_sdiff.mp (hQomit hi)).2 v.2
              · exact (Finset.mem_sdiff.mp (hQomit hj)).2 u.2
  have hGcard : G.edgeFinset.card = 16 := by
    have hsum := G.sum_degrees_eq_twice_card_edges
    have hleft : (∑ i : Fin 16, G.degree i) = 32 := by
      simp [hdeg]
    rw [hleft] at hsum
    omega
  have hBedge : B.edgeFinset.card ≤ 8 := by
    have hunion : A.edgeFinset ∪ E ⊆ G.edgeFinset :=
      Finset.union_subset hAsub hEsub
    have hc := Finset.card_le_card hunion
    rw [Finset.card_union_of_disjoint hdisjoint, hAcard, hEcard, hGcard] at hc
    omega
  have hBacyc : (boundaryForcedRunGraph55 F).IsAcyclic := by
    let f : B →g forcedEdgeGraph (gridGraph 5 5)
        (↑F : Set (GridVertex 5 5)) := {
      toFun := fun i => boundaryVertex55 i.1
      map_rel' := by
        intro i j hij
        have hiF : boundaryVertex55 i.1 ∈ F := by
          simpa [P, B, boundaryForcedRunGraph55,
            boundaryForcedPositions55] using i.2
        exact ⟨gridBoundaryCycleHom55.map_rel hij, Or.inl hiF⟩ }
    exact hacyc.comap f (fun i j hij => Subtype.ext
      (gridBoundaryVertex_injective (m := 5) (n := 5)
        (by omega) (by omega) hij))
  letI : Fintype (boundaryForcedRunGraph55 F).ConnectedComponent :=
    SetLike.instFintype
  have hledger := hBacyc.card_edgeFinset_add_card_connectedComponent
  have hcomponentInstances :
      @Fintype.card (boundaryForcedRunGraph55 F).ConnectedComponent
          (boundaryForcedRunGraph55 F).instFintypeConnectedComponent =
        @Fintype.card (boundaryForcedRunGraph55 F).ConnectedComponent this :=
    @Fintype.card_congr _ _
      (boundaryForcedRunGraph55 F).instFintypeConnectedComponent this (Equiv.refl _)
  have hverts : Fintype.card
      (↑(boundaryForcedPositions55 F) : Set (Fin 16)) = 11 := by
    simpa using hPcard
  dsimp [B] at hBedge
  rw [hverts] at hledger
  rw [hcomponentInstances] at hledger
  dsimp [B] at hledger
  have hledger' :
      (boundaryForcedRunGraph55 F).edgeFinset.card +
        Fintype.card (boundaryForcedRunGraph55 F).ConnectedComponent = 11 := by
    exact hledger
  have hc : 3 ≤ Fintype.card
      (boundaryForcedRunGraph55 F).ConnectedComponent := by
    omega
  simpa only [boundaryForcedRunCount55] using hc

/-- If the lower bound on cyclic boundary runs is sharp, the fifth omission is
an even side midpoint, flanked by two of the four selected odd omissions. -/
theorem fifth_boundary_omission_is_side_midpoint_of_three_runs
    (F : Finset (GridVertex 5 5)) (Q : Finset (Fin 16))
    (hacyc : (forcedEdgeGraph (gridGraph 5 5)
      (↑F : Set (GridVertex 5 5))).IsAcyclic)
    (hPcard : (boundaryForcedPositions55 F).card = 11)
    (hQcard : Q.card = 4)
    (hQomit : Q ⊆ (Finset.univ : Finset (Fin 16)) \
      boundaryForcedPositions55 F)
    (hQodd : ∀ q ∈ Q, q.val % 2 = 1)
    (hcorners : ∀ i : Fin 16, i.val % 4 = 0 →
      i ∈ boundaryForcedPositions55 F)
    (hruns : boundaryForcedRunCount55 F = 3) :
    ∃ e : Fin 16,
      e ∈ (Finset.univ : Finset (Fin 16)) \ boundaryForcedPositions55 F ∧
      e ∉ Q ∧ e.val ∈ ({2, 6, 10, 14} : Finset Nat) ∧
      e - 1 ∈ Q ∧ e + 1 ∈ Q := by
  classical
  let G := cycleGraph 16
  let P := boundaryForcedPositions55 F
  let O : Finset (Fin 16) := Finset.univ \ P
  let A := forcedEdgeGraph G (↑Q : Set (Fin 16))
  let B := boundaryForcedRunGraph55 F
  have hOcard : O.card = 5 := by
    simp [O, P, Finset.card_sdiff, hPcard]
  have hQO : Q ⊆ O := hQomit
  have hdiffCard : (O \ Q).card = 1 := by
    rw [Finset.card_sdiff_of_subset hQO, hOcard, hQcard]
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp hdiffCard
  have heO : e ∈ O := by
    have : e ∈ O \ Q := by simp [he]
    exact (Finset.mem_sdiff.mp this).1
  have heQ : e ∉ Q := by
    have : e ∈ O \ Q := by simp [he]
    exact (Finset.mem_sdiff.mp this).2
  have hdeg (i : Fin 16) : G.degree i = 2 := by
    dsimp [G]
    rw [cycleGraph_degree_two_le, Finset.card_pair]
    intro heq
    have hi : i = i + 2 := by
      have := congrArg (fun x => x + 1) heq
      simpa [sub_eq_add_neg, add_assoc] using this
    have hzero : (0 : Fin 16) = 2 :=
      add_left_cancel (a := i) (by simpa using hi)
    have := congrArg Fin.val hzero
    norm_num at this
  have hQinduced : (G.induce (↑Q : Set (Fin 16))).edgeFinset.card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro edge hedge
    induction edge using Sym2.inductionOn with
    | _ i j =>
        rw [SimpleGraph.mem_edgeFinset] at hedge
        exact cycleGraph_sixteen_adj_not_both_odd hedge
          ⟨hQodd i i.2, hQodd j j.2⟩
  have hAcard : A.edgeFinset.card = 8 := by
    have hsum := sum_degrees_finset_eq_forced_add_induced G Q
    rw [Finset.sum_congr rfl (fun i _ => hdeg i), hQinduced] at hsum
    simp [hQcard] at hsum
    norm_num [A] at hsum ⊢
    exact hsum.symm
  have hBacyc : B.IsAcyclic := by
    let f : B →g forcedEdgeGraph (gridGraph 5 5)
        (↑F : Set (GridVertex 5 5)) := {
      toFun := fun i => boundaryVertex55 i.1
      map_rel' := by
        intro i j hij
        have hiF : boundaryVertex55 i.1 ∈ F := by
          simpa [P, B, boundaryForcedRunGraph55,
            boundaryForcedPositions55] using i.2
        exact ⟨gridBoundaryCycleHom55.map_rel hij, Or.inl hiF⟩ }
    exact hacyc.comap f (fun i j hij => Subtype.ext
      (gridBoundaryVertex_injective (m := 5) (n := 5)
        (by omega) (by omega) hij))
  letI : Fintype B.ConnectedComponent := SetLike.instFintype
  have hledger := hBacyc.card_edgeFinset_add_card_connectedComponent
  have hcomponentInstances :
      @Fintype.card B.ConnectedComponent B.instFintypeConnectedComponent =
        @Fintype.card B.ConnectedComponent this :=
    @Fintype.card_congr _ _ B.instFintypeConnectedComponent this (Equiv.refl _)
  have hverts : Fintype.card (↑P : Set (Fin 16)) = 11 := by
    simpa [P] using hPcard
  have hcomponents : Fintype.card B.ConnectedComponent = 3 := by
    simpa [B, boundaryForcedRunCount55] using hruns
  have hBcard : B.edgeFinset.card = 8 := by
    rw [hverts, hcomponentInstances, hcomponents] at hledger
    omega
  let E := B.edgeFinset.map
    (Function.Embedding.subtype (↑P : Set (Fin 16))).sym2Map
  have hEcard : E.card = 8 := by
    rw [show E.card = B.edgeFinset.card by simp [E], hBcard]
  have hEsub : E ⊆ G.edgeFinset := by
    intro edge hedge
    simp only [E, Finset.mem_map] at hedge
    obtain ⟨edge', hedge', rfl⟩ := hedge
    induction edge' using Sym2.inductionOn with
    | _ i j =>
        rw [SimpleGraph.mem_edgeFinset] at hedge' ⊢
        exact hedge'
  have hAsub : A.edgeFinset ⊆ G.edgeFinset := by
    intro edge hedge
    induction edge using Sym2.inductionOn with
    | _ i j =>
        rw [SimpleGraph.mem_edgeFinset] at hedge ⊢
        exact hedge.1
  have hdisjoint : Disjoint A.edgeFinset E := by
    rw [Finset.disjoint_left]
    intro edge hedgeA hedgeE
    induction edge using Sym2.inductionOn with
    | _ i j =>
        rw [SimpleGraph.mem_edgeFinset] at hedgeA
        simp only [E, Finset.mem_map] at hedgeE
        obtain ⟨edge', hedge', hedgeq⟩ := hedgeE
        induction edge' using Sym2.inductionOn with
        | _ u v =>
            change s(u.1, v.1) = s(i, j) at hedgeq
            rw [Sym2.eq_iff] at hedgeq
            rcases hedgeq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
              rcases hedgeA.2 with hi | hj
            · exact (Finset.mem_sdiff.mp (hQomit hi)).2 u.2
            · exact (Finset.mem_sdiff.mp (hQomit hj)).2 v.2
            · exact (Finset.mem_sdiff.mp (hQomit hi)).2 v.2
            · exact (Finset.mem_sdiff.mp (hQomit hj)).2 u.2
  have hGcard : G.edgeFinset.card = 16 := by
    have hsum := G.sum_degrees_eq_twice_card_edges
    have hleft : (∑ i : Fin 16, G.degree i) = 32 := by simp [hdeg]
    rw [hleft] at hsum
    omega
  have hunion : A.edgeFinset ∪ E = G.edgeFinset := by
    apply Finset.eq_of_subset_of_card_le (Finset.union_subset hAsub hEsub)
    rw [Finset.card_union_of_disjoint hdisjoint, hAcard, hEcard, hGcard]
  have hneighbor {j : Fin 16} (hej : G.Adj e j) : j ∈ Q := by
    have hedgeG : s(e, j) ∈ G.edgeFinset := by
      rw [SimpleGraph.mem_edgeFinset]
      exact hej
    rw [← hunion] at hedgeG
    rcases Finset.mem_union.mp hedgeG with hedgeA | hedgeE
    · rw [SimpleGraph.mem_edgeFinset] at hedgeA
      exact hedgeA.2.resolve_left heQ
    · simp only [E, Finset.mem_map] at hedgeE
      obtain ⟨edge', hedge', hedgeq⟩ := hedgeE
      induction edge' using Sym2.inductionOn with
      | _ u v =>
          change s(u.1, v.1) = s(e, j) at hedgeq
          rw [Sym2.eq_iff] at hedgeq
          rcases hedgeq with ⟨hue, _⟩ | ⟨_, hve⟩
          · exact ((Finset.mem_sdiff.mp heO).2 (hue ▸ u.2)).elim
          · exact ((Finset.mem_sdiff.mp heO).2 (hve ▸ v.2)).elim
  have hprev : e - 1 ∈ Q := hneighbor (by
    rw [cycleGraph_adj]
    left
    simp)
  have hnext : e + 1 ∈ Q := hneighbor (by
    rw [cycleGraph_adj]
    right
    simp)
  have heEven : e.val % 2 = 0 := by
    have hp := hQodd (e - 1) hprev
    have hn := hQodd (e + 1) hnext
    simp only [Fin.sub_def, Fin.add_def] at hp hn
    norm_num at hp hn
    omega
  have heNotCorner : e.val % 4 ≠ 0 := by
    intro heCorner
    exact (Finset.mem_sdiff.mp heO).2 (hcorners e heCorner)
  have heMid : e.val ∈ ({2, 6, 10, 14} : Finset Nat) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  exact ⟨e, heO, heQ, heMid, hprev, hnext⟩

private lemma corners55_card : corners55.card = 4 := by
  let endpoints : Finset (Fin 5) := {0, 4}
  have hcorners : corners55 = endpoints ×ˢ endpoints := by
    ext v
    rw [Finset.mem_product]
    simp only [corners55, Finset.mem_filter, Finset.mem_univ, true_and,
      endpoints, Finset.mem_insert, Finset.mem_singleton]
    constructor <;> rintro ⟨hr, hc⟩
    · constructor
      · rcases hr with h | h
        · left; apply Fin.ext; omega
        · right; apply Fin.ext; omega
      · rcases hc with h | h
        · left; apply Fin.ext; omega
        · right; apply Fin.ext; omega
    · constructor
      · rcases hr with h | h
        · left; simpa [h]
        · right; have := congrArg Fin.val h; norm_num at this ⊢; omega
      · rcases hc with h | h
        · left; simpa [h]
        · right; have := congrArg Fin.val h; norm_num at this ⊢; omega
  have hendpoints : endpoints.card = 2 := by
    rw [Finset.card_pair]
    intro h
    have := congrArg Fin.val h
    norm_num at this
  rw [hcorners, Finset.card_product, hendpoints]

private lemma cycleGraph_sixteen_not_isAcyclic :
    ¬(cycleGraph 16).IsAcyclic := by
  intro hacyc
  have htree : (cycleGraph 16).IsTree := ⟨cycleGraph_connected, hacyc⟩
  have hcard := htree.card_edgeFinset
  have hdeg := (cycleGraph 16).sum_degrees_eq_twice_card_edges
  have htwo : ∀ i : Fin 16, (cycleGraph 16).degree i = 2 := by
    intro i
    rw [cycleGraph_degree_two_le, Finset.card_pair]
    intro heq
    have hi : i = i + 2 := by
      have := congrArg (fun x => x + 1) heq
      simpa [sub_eq_add_neg, add_assoc] using this
    have hzero : (0 : Fin 16) = 2 :=
      add_left_cancel (a := i) (by simpa using hi)
    have := congrArg Fin.val hzero
    norm_num at this
  rw [Finset.sum_congr rfl (fun i _ => htwo i)] at hdeg
  norm_num at hcard hdeg
  omega

/-- The twelve-vertex profile supported entirely on the boundary and containing
all four corners is impossible.  At every forced corner, one of its two
boundary neighbors must be omitted.  These four omissions are distinct and
odd-numbered; cardinality then makes every omission odd, so every edge of the
boundary cycle is forced. -/
theorem forced_five_five_twelve_boundary_four_corners_impossible
    (F : Finset (GridVertex 5 5))
    (hboundary : (F ∩ boundary55).card = 12)
    (hcornersCard : (F ∩ corners55).card = 4)
    (hacyc : (forcedEdgeGraph (gridGraph 5 5)
      (↑F : Set (GridVertex 5 5))).IsAcyclic) : False := by
  classical
  let P := boundaryForcedPositions55 F
  let O : Finset (Fin 16) := Finset.univ \ P
  have hcorners : corners55 ⊆ F := by
    have hinter : F ∩ corners55 = corners55 :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by
        rw [hcornersCard, corners55_card])
    intro v hv
    have : v ∈ F ∩ corners55 := by simpa [hinter] using hv
    exact (Finset.mem_inter.mp this).1
  have himage : P.image boundaryVertex55 = F ∩ boundary55 := by
    ext v
    constructor
    · rintro hv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
      have hiF : boundaryVertex55 i ∈ F := by
        simpa [P, boundaryForcedPositions55] using hi
      exact Finset.mem_inter.mpr ⟨hiF, by
        simp only [boundary55, Finset.mem_filter, Finset.mem_univ, true_and]
        simpa [IsGridBoundary] using
          (gridBoundaryVertex_isBoundary (m := 5) (n := 5)
            (by omega) (by omega) (boundaryPosition55 i))⟩
    · intro hv
      have hv' := Finset.mem_inter.mp hv
      have hvB : IsGridBoundary v := by
        simpa [boundary55, IsGridBoundary] using hv'.2
      obtain ⟨i, hi⟩ := exists_gridBoundaryPosition (m := 5) (n := 5)
        (by omega) (by omega) v hvB
      refine Finset.mem_image.mpr ⟨⟨i.val, by simpa [gridBoundaryLength] using i.isLt⟩,
        ?_, ?_⟩
      · simpa [P, boundaryForcedPositions55, boundaryVertex55,
          boundaryPosition55, hi] using hv'.1
      · simpa [boundaryVertex55, boundaryPosition55] using hi
  have hPcard : P.card = 12 := by
    have hinj : Function.Injective boundaryVertex55 := by
      intro i j hij
      exact gridBoundaryVertex_injective (m := 5) (n := 5)
        (by omega) (by omega) hij
    rw [← hboundary, ← himage, Finset.card_image_of_injective _ hinj]
  have hOcard : O.card = 4 := by
    calc
      O.card = (Finset.univ : Finset (Fin 16)).card -
          (P ∩ Finset.univ).card := by simp only [O, Finset.card_sdiff]
      _ = 4 := by simp [hPcard]
  have hcorner (r c : Fin 5)
      (hr : r.val = 0 ∨ r.val + 1 = 5)
      (hc : c.val = 0 ∨ c.val + 1 = 5) : (r, c) ∈ F := by
    apply hcorners
    simp only [corners55, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hr, hc⟩
  have htriple00 := (grid_cell_forced_triples_free (F := (↑F : Set _))
    (⟨0, by omega⟩ : Fin (5 - 1)) (⟨0, by omega⟩ : Fin (5 - 1)) hacyc).2.2.2
  have htriple04 := (grid_cell_forced_triples_free (F := (↑F : Set _))
    (⟨0, by omega⟩ : Fin (5 - 1)) (⟨3, by omega⟩ : Fin (5 - 1)) hacyc).1
  have htriple44 := (grid_cell_forced_triples_free (F := (↑F : Set _))
    (⟨3, by omega⟩ : Fin (5 - 1)) (⟨3, by omega⟩ : Fin (5 - 1)) hacyc).2.1
  have htriple40 := (grid_cell_forced_triples_free (F := (↑F : Set _))
    (⟨3, by omega⟩ : Fin (5 - 1)) (⟨0, by omega⟩ : Fin (5 - 1)) hacyc).2.2.1
  have hq0 : ∃ q ∈ ({15, 1} : Finset (Fin 16)), q ∈ O := by
    by_cases h15 : boundaryVertex55 15 ∈ F
    · refine ⟨1, by simp, ?_⟩
      simp only [O, Finset.mem_sdiff, Finset.mem_univ, true_and, P,
        boundaryForcedPositions55, Finset.mem_filter]
      intro h1
      apply htriple00
      simpa [cell10, cell00, cell01, boundaryVertex55, boundaryPosition55,
        gridBoundaryVertex, gridBoundaryLength] using
        ⟨h15, hcorner 0 0 (Or.inl rfl) (Or.inl rfl), h1⟩
    · exact ⟨15, by simp, by simpa [O, P, boundaryForcedPositions55]⟩
  have hq1 : ∃ q ∈ ({3, 5} : Finset (Fin 16)), q ∈ O := by
    by_cases h3 : boundaryVertex55 3 ∈ F
    · refine ⟨5, by simp, ?_⟩
      simp only [O, Finset.mem_sdiff, Finset.mem_univ, true_and, P,
        boundaryForcedPositions55, Finset.mem_filter]
      intro h5
      apply htriple04
      simpa [cell00, cell01, cell11, boundaryVertex55, boundaryPosition55,
        gridBoundaryVertex, gridBoundaryLength] using
        ⟨h3, hcorner 0 4 (Or.inl rfl) (Or.inr (by omega)), h5⟩
    · exact ⟨3, by simp, by simpa [O, P, boundaryForcedPositions55]⟩
  have hq2 : ∃ q ∈ ({7, 9} : Finset (Fin 16)), q ∈ O := by
    by_cases h7 : boundaryVertex55 7 ∈ F
    · refine ⟨9, by simp, ?_⟩
      simp only [O, Finset.mem_sdiff, Finset.mem_univ, true_and, P,
        boundaryForcedPositions55, Finset.mem_filter]
      intro h9
      apply htriple44
      simpa [cell01, cell11, cell10, boundaryVertex55, boundaryPosition55,
        gridBoundaryVertex, gridBoundaryLength] using
        ⟨h7, hcorner 4 4 (Or.inr (by omega)) (Or.inr (by omega)), h9⟩
    · exact ⟨7, by simp, by simpa [O, P, boundaryForcedPositions55]⟩
  have hq3 : ∃ q ∈ ({11, 13} : Finset (Fin 16)), q ∈ O := by
    by_cases h11 : boundaryVertex55 11 ∈ F
    · refine ⟨13, by simp, ?_⟩
      simp only [O, Finset.mem_sdiff, Finset.mem_univ, true_and, P,
        boundaryForcedPositions55, Finset.mem_filter]
      intro h13
      apply htriple40
      simpa [cell11, cell10, cell00, boundaryVertex55, boundaryPosition55,
        gridBoundaryVertex, gridBoundaryLength] using
        ⟨h11, hcorner 4 0 (Or.inr (by omega)) (Or.inl rfl), h13⟩
    · exact ⟨11, by simp, by simpa [O, P, boundaryForcedPositions55]⟩
  obtain ⟨q0, hq0p, hq0O⟩ := hq0
  obtain ⟨q1, hq1p, hq1O⟩ := hq1
  obtain ⟨q2, hq2p, hq2O⟩ := hq2
  obtain ⟨q3, hq3p, hq3O⟩ := hq3
  let Q : Finset (Fin 16) := {q0, q1, q2, q3}
  have hQcard : Q.card = 4 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq0p hq1p hq2p hq3p
    simp [Q]
    aesop
  have hQO : Q ⊆ O := by
    intro q hq
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact hq0O
    · exact hq1O
    · exact hq2O
    · exact hq3O
  have hOQ : O = Q :=
    (Finset.eq_of_subset_of_card_le hQO (by rw [hOcard, hQcard])).symm
  have hq0odd : q0.val % 2 = 1 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq0p
    rcases hq0p with rfl | rfl <;> norm_num
  have hq1odd : q1.val % 2 = 1 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq1p
    rcases hq1p with rfl | rfl <;> norm_num
  have hq2odd : q2.val % 2 = 1 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq2p
    rcases hq2p with rfl | rfl <;> norm_num
  have hq3odd : q3.val % 2 = 1 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq3p
    rcases hq3p with rfl | rfl <;> norm_num
  have hOodd {i : Fin 16} (hi : i ∈ O) : i.val % 2 = 1 := by
    rw [hOQ] at hi
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact hq0odd
    · exact hq1odd
    · exact hq2odd
    · exact hq3odd
  have hedgeForced {i j : Fin 16} (hij : (cycleGraph 16).Adj i j) :
      boundaryVertex55 i ∈ F ∨ boundaryVertex55 j ∈ F := by
    by_contra hnot
    push_neg at hnot
    have hiO : i ∈ O := by simpa [O, P, boundaryForcedPositions55, hnot.1]
    have hjO : j ∈ O := by simpa [O, P, boundaryForcedPositions55, hnot.2]
    have hiOdd := hOodd hiO
    have hjOdd := hOodd hjO
    have hj : j = i - 1 ∨ j = i + 1 := by
      have := show j ∈ (cycleGraph 16).neighborSet i from hij
      rw [cycleGraph_neighborSet] at this
      simpa [eq_comm] using this
    have succ_not_both_odd (x : Fin 16)
        (hxOdd : x.val % 2 = 1) (hyOdd : (x + 1).val % 2 = 1) : False := by
      change ((x.val + 1) % 16) % 2 = 1 at hyOdd
      by_cases hx : x.val + 1 < 16
      · rw [Nat.mod_eq_of_lt hx] at hyOdd
        omega
      · have hxlast : x.val + 1 = 16 := by omega
        simp [hxlast] at hyOdd
    rcases hj with h | h
    · have hi : i = j + 1 := by rw [h]; simp
      rw [hi] at hiOdd
      exact succ_not_both_odd j hjOdd hiOdd
    · rw [h] at hjOdd
      exact succ_not_both_odd i hiOdd hjOdd
  let f : cycleGraph 16 →g forcedEdgeGraph (gridGraph 5 5)
      (↑F : Set (GridVertex 5 5)) := {
    toFun := boundaryVertex55
    map_rel' := by
      intro i j hij
      exact ⟨gridBoundaryCycleHom55.map_rel hij, hedgeForced hij⟩ }
  apply cycleGraph_sixteen_not_isAcyclic
  exact hacyc.comap f (gridBoundaryVertex_injective
    (m := 5) (n := 5) (by omega) (by omega))

private lemma boundaryDeficiency55_le_corner_charge (v : GridVertex 5 5) :
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

private lemma boundaryDeficiencySum55_le (F : Finset (GridVertex 5 5)) :
    boundaryDeficiencySum 5 5 F ≤ F.card + (F ∩ corners55).card := by
  unfold boundaryDeficiencySum
  calc
    (∑ v ∈ F, gridBoundaryDeficiency 5 5 v) ≤
        ∑ v ∈ F, (1 + if v ∈ corners55 then 1 else 0) := by
      exact Finset.sum_le_sum fun v _ => boundaryDeficiency55_le_corner_charge v
    _ = F.card + (F ∩ corners55).card := by
      rw [Finset.sum_add_distrib]
      simp

private lemma boundaryDeficiency55_eq_boundary_add_corner
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
        push_neg
        exact ⟨fun h => hr (Or.inl h), fun h => hr (Or.inr h),
          fun h => hc (Or.inl h), fun h => hc (Or.inr h)⟩
      have hvC : v ∉ corners55 := by
        simp only [corners55, Finset.mem_filter, Finset.mem_univ, true_and,
          not_and]
        exact fun h => (hr h).elim
      simp [hvB, hvC]

private lemma boundaryDeficiencySum55_eq_boundary_add_corner
    (F : Finset (GridVertex 5 5)) :
    boundaryDeficiencySum 5 5 F =
      (F ∩ boundary55).card + (F ∩ corners55).card := by
  unfold boundaryDeficiencySum
  simp_rw [boundaryDeficiency55_eq_boundary_add_corner,
    Finset.sum_add_distrib, Finset.sum_boole]
  congr 1 <;> ext v <;> simp

private noncomputable instance inducedComponentVertexFintype55
    (F : Finset (GridVertex 5 5))
    (C : ((gridGraph 5 5).induce
      (↑F : Set (GridVertex 5 5))).ConnectedComponent) : Fintype C :=
  Fintype.ofFinite C

/-- Straightness limits every induced forced component in a `5 x 5` grid to
five vertices. -/
private lemma induced_forced_component_card_le_five
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
private lemma forced_card_le_five_mul_induced_components
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
theorem forced_five_five_card_le_twelve
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
theorem maxPreserved_five_five_le_twelve : maxPreserved 5 5 ≤ 12 := by
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
theorem forced_five_five_twelve_ledger_profile
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
theorem forced_five_five_boundary_supported_two_forced_components
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
      simpa [boundary55, z] using hzB
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
theorem forced_five_five_twelve_boundary_three_corners_impossible
    (F : Finset (GridVertex 5 5)) (hcard : F.card = 12)
    (hacyc : (forcedEdgeGraph (gridGraph 5 5)
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
theorem forced_five_five_twelve_final_profile_reduction
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
    push_neg at h
    exact (grid_cell_forced_triples_free (F := (↑F : Set _))
      (⟨0, by omega⟩ : Fin (5 - 1)) (⟨0, by omega⟩ : Fin (5 - 1)) hacyc).2.2.2
      (by simpa [cell10, cell00, cell01] using ⟨h.2, hcorner00, h.1⟩)
  have homit04 : (0, 3) ∉ F ∨ (1, 4) ∉ F := by
    by_contra h
    push_neg at h
    exact (grid_cell_forced_triples_free (F := (↑F : Set _))
      (⟨0, by omega⟩ : Fin (5 - 1)) (⟨3, by omega⟩ : Fin (5 - 1)) hacyc).1
      (by simpa [cell00, cell01, cell11] using ⟨h.1, hcorner04, h.2⟩)
  have homit44 : (3, 4) ∉ F ∨ (4, 3) ∉ F := by
    by_contra h
    push_neg at h
    exact (grid_cell_forced_triples_free (F := (↑F : Set _))
      (⟨3, by omega⟩ : Fin (5 - 1)) (⟨3, by omega⟩ : Fin (5 - 1)) hacyc).2.1
      (by simpa [cell01, cell11, cell10] using ⟨h.1, hcorner44, h.2⟩)
  have homit40 : (4, 1) ∉ F ∨ (3, 0) ∉ F := by
    by_contra h
    push_neg at h
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
      obtain ⟨C, hC⟩ := Finset.card_eq_one.mp (by
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

set_option maxHeartbeats 4000000 in
private lemma final_profile_three_runs_and_one_attachment
    (F : Finset (GridVertex 5 5))
    (x : GridVertex 5 5)
    (hxOutside : F \ boundary55 = {x})
    (hxF : x ∈ F) (hxNotBoundary : x ∉ boundary55)
    (hxLocation : x = (2, 2) ∨ (gridGraph 5 5).Adj (2, 2) x)
    (hacyc : (forcedEdgeGraph (gridGraph 5 5)
      (↑F : Set (GridVertex 5 5))).IsAcyclic)
    (hcard : F.card = 12)
    (hcomponents : Fintype.card ((gridGraph 5 5).induce
      (↑F : Set (GridVertex 5 5))).ConnectedComponent = 3)
    (hrunsLower : 3 ≤ boundaryForcedRunCount55 F) :
    boundaryForcedRunCount55 F = 3 ∧
      ((gridGraph 5 5).induce (↑F : Set (GridVertex 5 5))).degree
        ⟨x, hxF⟩ = 1 := by
  classical
  let H := (gridGraph 5 5).induce (↑F : Set (GridVertex 5 5))
  let B := boundaryForcedRunGraph55 F
  let xf : (↑F : Set (GridVertex 5 5)) := ⟨x, hxF⟩
  let f : (↑(boundaryForcedPositions55 F) : Set (Fin 16)) ↪
      (↑F : Set (GridVertex 5 5)) := {
    toFun := fun i => ⟨boundaryVertex55 i.1, by
      simpa [boundaryForcedPositions55] using i.2⟩
    inj' := fun i j hij => Subtype.ext (gridBoundaryVertex_injective
      (m := 5) (n := 5) (by omega) (by omega) (congrArg Subtype.val hij)) }
  have hboundary_of_ne (v : (↑F : Set (GridVertex 5 5)))
      (hv : v ≠ xf) : v.1 ∈ boundary55 := by
    by_contra hvB
    have hvOutside : v.1 ∈ F \ boundary55 :=
      Finset.mem_sdiff.mpr ⟨v.2, hvB⟩
    have hvx : v.1 = x := by simpa [hxOutside] using hvOutside
    exact hv (Subtype.ext hvx)
  have hdelete : H.deleteIncidenceSet xf = B.map f := by
    ext u v
    constructor
    · intro huv
      rw [SimpleGraph.deleteIncidenceSet_adj] at huv
      have huvH : H.Adj u v := huv.1
      have hux : u ≠ xf := by
        exact huv.2.1
      have hvx : v ≠ xf := by
        exact huv.2.2
      have huB := hboundary_of_ne u hux
      have hvB := hboundary_of_ne v hvx
      have huGridBoundary : IsGridBoundary u.1 := by
        simpa [boundary55, IsGridBoundary] using huB
      have hvGridBoundary : IsGridBoundary v.1 := by
        simpa [boundary55, IsGridBoundary] using hvB
      obtain ⟨iu, hiu⟩ := exists_gridBoundaryPosition (m := 5) (n := 5)
        (by omega) (by omega) u.1 huGridBoundary
      obtain ⟨iv, hiv⟩ := exists_gridBoundaryPosition (m := 5) (n := 5)
        (by omega) (by omega) v.1 hvGridBoundary
      let i : Fin 16 := ⟨iu.val, by simpa [gridBoundaryLength] using iu.isLt⟩
      let j : Fin 16 := ⟨iv.val, by simpa [gridBoundaryLength] using iv.isLt⟩
      have hiVertex : boundaryVertex55 i = u.1 := by
        simpa [i, boundaryVertex55, boundaryPosition55] using hiu
      have hjVertex : boundaryVertex55 j = v.1 := by
        simpa [j, boundaryVertex55, boundaryPosition55] using hiv
      have hiP : i ∈ boundaryForcedPositions55 F := by
        simpa [boundaryForcedPositions55, hiVertex] using u.2
      have hjP : j ∈ boundaryForcedPositions55 F := by
        simpa [boundaryForcedPositions55, hjVertex] using v.2
      let iP : (↑(boundaryForcedPositions55 F) : Set (Fin 16)) := ⟨i, hiP⟩
      let jP : (↑(boundaryForcedPositions55 F) : Set (Fin 16)) := ⟨j, hjP⟩
      have hijCycle : (cycleGraph 16).Adj i j := by
        apply gridBoundaryCycleHom55_reflects_adj
        simpa [hiVertex, hjVertex] using huvH
      change (B.map f).Adj u v
      rw [SimpleGraph.map_adj]
      exact ⟨iP, jP, by simpa [B, boundaryForcedRunGraph55, iP, jP],
        by apply Subtype.ext; exact hiVertex,
        by apply Subtype.ext; exact hjVertex⟩
    · intro huv
      rw [SimpleGraph.map_adj] at huv
      obtain ⟨i, j, hij, hiu, hjv⟩ := huv
      subst u
      subst v
      have hiGrid : (gridGraph 5 5).Adj (boundaryVertex55 i.1)
          (boundaryVertex55 j.1) := gridBoundaryCycleHom55.map_rel hij
      have hix : f i ≠ xf := by
        intro h
        have hxB : x ∈ boundary55 := by
          have hiB := gridBoundaryVertex_isBoundary (m := 5) (n := 5)
            (by omega) (by omega) (boundaryPosition55 i.1)
          have heq : boundaryVertex55 i.1 = x := congrArg Subtype.val h
          rw [← heq]
          simpa [boundary55, IsGridBoundary, boundaryVertex55] using hiB
        exact hxNotBoundary hxB
      have hjx : f j ≠ xf := by
        intro h
        have hxB : x ∈ boundary55 := by
          have hjB := gridBoundaryVertex_isBoundary (m := 5) (n := 5)
            (by omega) (by omega) (boundaryPosition55 j.1)
          have heq : boundaryVertex55 j.1 = x := congrArg Subtype.val h
          rw [← heq]
          simpa [boundary55, IsGridBoundary, boundaryVertex55] using hjB
        exact hxNotBoundary hxB
      rw [SimpleGraph.deleteIncidenceSet_adj]
      exact ⟨hiGrid, hix, hjx⟩
  have hHedges : H.edgeFinset.card = 9 := by
    have hledger := induce_finset_forest_ledger (gridGraph 5 5) F hacyc
    rw [hcomponents, hcard] at hledger
    exact Nat.eq_sub_of_add_eq hledger
  have hdegree_le : H.degree xf ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro u hu v hv
    have huAdj : H.Adj xf u := by simpa [SimpleGraph.mem_neighborFinset] using hu
    have hvAdj : H.Adj xf v := by simpa [SimpleGraph.mem_neighborFinset] using hv
    have huB : u.1 ∈ boundary55 := by
      by_contra huNotB
      have huOutside : u.1 ∈ F \ boundary55 :=
        Finset.mem_sdiff.mpr ⟨u.2, huNotB⟩
      have hux : u.1 = x := by simpa [hxOutside] using huOutside
      exact (H.ne_of_adj huAdj) (Subtype.ext hux.symm)
    have hvB : v.1 ∈ boundary55 := by
      by_contra hvNotB
      have hvOutside : v.1 ∈ F \ boundary55 :=
        Finset.mem_sdiff.mpr ⟨v.2, hvNotB⟩
      have hvx : v.1 = x := by simpa [hxOutside] using hvOutside
      exact (H.ne_of_adj hvAdj) (Subtype.ext hvx.symm)
    apply Subtype.ext
    change adjacent 5 5 x u.1 at huAdj
    change adjacent 5 5 x v.1 at hvAdj
    simp only [boundary55, Finset.mem_filter, Finset.mem_univ, true_and] at huB hvB
    have hxCases : x = (2, 2) ∨ x = (1, 2) ∨ x = (2, 3) ∨
        x = (3, 2) ∨ x = (2, 1) := by
      rcases hxLocation with h | h
      · exact Or.inl h
      · change adjacent 5 5 (2, 2) x at h
        rcases h with ⟨hrow, hcol | hcol⟩ | ⟨hcol, hrow | hrow⟩
        · right; right; left
          apply Prod.ext <;> apply Fin.ext <;> norm_num at hrow hcol ⊢ <;> omega
        · right; right; right; right
          apply Prod.ext <;> apply Fin.ext <;> norm_num at hrow hcol ⊢ <;> omega
        · right; right; right; left
          apply Prod.ext <;> apply Fin.ext <;> norm_num at hrow hcol ⊢ <;> omega
        · right; left
          apply Prod.ext <;> apply Fin.ext <;> norm_num at hrow hcol ⊢ <;> omega
    rcases hxCases with hx | hx | hx | hx | hx
    · rw [hx] at huAdj
      exfalso
      rcases huAdj with ⟨hr, hc | hc⟩ | ⟨hc, hr | hr⟩ <;>
        rcases huB with h | h | h | h
      all_goals norm_num at hr hc h <;> omega
    · rw [hx] at huAdj hvAdj
      have huEq : u.1 = (0, 2) := by
        rcases huAdj with ⟨hr, hc | hc⟩ | ⟨hc, hr | hr⟩ <;>
          rcases huB with h | h | h | h <;>
          apply Prod.ext <;> apply Fin.ext <;>
          norm_num at hr hc h ⊢ <;> omega
      have hvEq : v.1 = (0, 2) := by
        rcases hvAdj with ⟨hr, hc | hc⟩ | ⟨hc, hr | hr⟩ <;>
          rcases hvB with h | h | h | h <;>
          apply Prod.ext <;> apply Fin.ext <;>
          norm_num at hr hc h ⊢ <;> omega
      exact huEq.trans hvEq.symm
    · rw [hx] at huAdj hvAdj
      have huEq : u.1 = (2, 4) := by
        rcases huAdj with ⟨hr, hc | hc⟩ | ⟨hc, hr | hr⟩ <;>
          rcases huB with h | h | h | h <;>
          apply Prod.ext <;> apply Fin.ext <;>
          norm_num at hr hc h ⊢ <;> omega
      have hvEq : v.1 = (2, 4) := by
        rcases hvAdj with ⟨hr, hc | hc⟩ | ⟨hc, hr | hr⟩ <;>
          rcases hvB with h | h | h | h <;>
          apply Prod.ext <;> apply Fin.ext <;>
          norm_num at hr hc h ⊢ <;> omega
      exact huEq.trans hvEq.symm
    · rw [hx] at huAdj hvAdj
      have huEq : u.1 = (4, 2) := by
        rcases huAdj with ⟨hr, hc | hc⟩ | ⟨hc, hr | hr⟩ <;>
          rcases huB with h | h | h | h <;>
          apply Prod.ext <;> apply Fin.ext <;>
          norm_num at hr hc h ⊢ <;> omega
      have hvEq : v.1 = (4, 2) := by
        rcases hvAdj with ⟨hr, hc | hc⟩ | ⟨hc, hr | hr⟩ <;>
          rcases hvB with h | h | h | h <;>
          apply Prod.ext <;> apply Fin.ext <;>
          norm_num at hr hc h ⊢ <;> omega
      exact huEq.trans hvEq.symm
    · rw [hx] at huAdj hvAdj
      have huEq : u.1 = (2, 0) := by
        rcases huAdj with ⟨hr, hc | hc⟩ | ⟨hc, hr | hr⟩ <;>
          rcases huB with h | h | h | h <;>
          apply Prod.ext <;> apply Fin.ext <;>
          norm_num at hr hc h ⊢ <;> omega
      have hvEq : v.1 = (2, 0) := by
        rcases hvAdj with ⟨hr, hc | hc⟩ | ⟨hc, hr | hr⟩ <;>
          rcases hvB with h | h | h | h <;>
          apply Prod.ext <;> apply Fin.ext <;>
          norm_num at hr hc h ⊢ <;> omega
      exact huEq.trans hvEq.symm
  have hdeleteCard : (H.deleteIncidenceSet xf).edgeFinset.card =
      B.edgeFinset.card := by
    let edgeCard (G : SimpleGraph (↑F : Set (GridVertex 5 5))) : Nat :=
      G.edgeSet.ncard
    have heq := congrArg edgeCard hdelete
    have hmap := SimpleGraph.card_edgeFinset_map f B
    exact (show (H.deleteIncidenceSet xf).edgeFinset.card =
        edgeCard (H.deleteIncidenceSet xf) by
          exact (Set.ncard_eq_toFinset_card' _).symm).trans
      (heq.trans ((show edgeCard (B.map f) = (B.map f).edgeFinset.card by
        exact Set.ncard_eq_toFinset_card' _).trans hmap))
  have hdeleteDegree := H.card_edgeFinset_deleteIncidenceSet xf
  have hBacyc : B.IsAcyclic := by
    let g : B →g forcedEdgeGraph (gridGraph 5 5)
        (↑F : Set (GridVertex 5 5)) := {
      toFun := fun i => boundaryVertex55 i.1
      map_rel' := by
        intro i j hij
        have hiF : boundaryVertex55 i.1 ∈ F := by
          simpa [B, boundaryForcedRunGraph55,
            boundaryForcedPositions55] using i.2
        exact ⟨gridBoundaryCycleHom55.map_rel hij, Or.inl hiF⟩ }
    exact hacyc.comap g (fun i j hij => Subtype.ext
      (gridBoundaryVertex_injective (m := 5) (n := 5)
        (by omega) (by omega) hij))
  letI : Fintype B.ConnectedComponent := SetLike.instFintype
  have hBledger := hBacyc.card_edgeFinset_add_card_connectedComponent
  have hPcard : (boundaryForcedPositions55 F).card = 11 := by
    have hboundary : F ∩ boundary55 = F.erase x := by
      ext v
      constructor
      · intro hv
        have hv' := Finset.mem_inter.mp hv
        exact Finset.mem_erase.mpr ⟨fun hvx => hxNotBoundary (hvx ▸ hv'.2), hv'.1⟩
      · intro hv
        have hv' := Finset.mem_erase.mp hv
        refine Finset.mem_inter.mpr ⟨hv'.2, ?_⟩
        by_contra hvB
        have hvOutside : v ∈ F \ boundary55 :=
          Finset.mem_sdiff.mpr ⟨hv'.2, hvB⟩
        have : v = x := by simpa [hxOutside] using hvOutside
        exact hv'.1 this
    have hboundaryCard : (F ∩ boundary55).card = 11 := by
      rw [hboundary, Finset.card_erase_of_mem hxF, hcard]
    have himage : (boundaryForcedPositions55 F).image boundaryVertex55 =
        F ∩ boundary55 := by
      ext v
      constructor
      · rintro hv
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
        exact Finset.mem_inter.mpr ⟨by
          simpa [boundaryForcedPositions55] using hi, by
          simpa [boundary55, IsGridBoundary] using
            gridBoundaryVertex_isBoundary (m := 5) (n := 5)
              (by omega) (by omega) (boundaryPosition55 i)⟩
      · intro hv
        have hv' := Finset.mem_inter.mp hv
        have hvB : IsGridBoundary v := by
          simpa [boundary55, IsGridBoundary] using hv'.2
        obtain ⟨i, hi⟩ := exists_gridBoundaryPosition (m := 5) (n := 5)
          (by omega) (by omega) v hvB
        let j : Fin 16 := ⟨i.val, by simpa [gridBoundaryLength] using i.isLt⟩
        refine Finset.mem_image.mpr ⟨j, ?_, ?_⟩
        · simpa [boundaryForcedPositions55, boundaryVertex55,
            boundaryPosition55, j, hi] using hv'.1
        · simpa [boundaryVertex55, boundaryPosition55, j] using hi
    have hinj : Function.Injective boundaryVertex55 := by
      intro i j hij
      exact gridBoundaryVertex_injective (m := 5) (n := 5)
        (by omega) (by omega) hij
    rw [← hboundaryCard, ← himage, Finset.card_image_of_injective _ hinj]
  have hBverts : Fintype.card (↑(boundaryForcedPositions55 F) : Set (Fin 16)) = 11 := by
    simpa using hPcard
  have hcomponentInstances :
      @Fintype.card B.ConnectedComponent B.instFintypeConnectedComponent =
        @Fintype.card B.ConnectedComponent this :=
    @Fintype.card_congr _ _ B.instFintypeConnectedComponent this (Equiv.refl _)
  rw [hBverts] at hBledger
  rw [hcomponentInstances] at hBledger
  change B.edgeFinset.card + boundaryForcedRunCount55 F = 11 at hBledger
  rw [hHedges, hdeleteCard] at hdeleteDegree
  have hdegree : H.degree xf = 1 := by
    by_contra hne
    have hz : H.degree xf = 0 := by omega
    rw [hz] at hdeleteDegree
    omega
  have hruns : boundaryForcedRunCount55 F = 3 := by
    rw [hdegree] at hdeleteDegree
    omega
  exact ⟨hruns, hdegree⟩

private lemma gridVertex55_eq_iff_vals (u v : GridVertex 5 5) :
    u = v ↔ (u.1.val = v.1.val ∧ u.2.val = v.2.val) := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨hr, hc⟩
    apply Prod.ext <;> apply Fin.ext
    · exact hr
    · exact hc

private lemma odd_boundary_position_forced_of_three_runs
    (F : Finset (GridVertex 5 5)) (Q : Finset (Fin 16)) (t : Fin 16)
    (hacyc : (forcedEdgeGraph (gridGraph 5 5)
      (↑F : Set (GridVertex 5 5))).IsAcyclic)
    (hPcard : (boundaryForcedPositions55 F).card = 11)
    (hQcard : Q.card = 4)
    (hQomit : Q ⊆ (Finset.univ : Finset (Fin 16)) \
      boundaryForcedPositions55 F)
    (hQodd : ∀ q ∈ Q, q.val % 2 = 1)
    (hcorners : ∀ i : Fin 16, i.val % 4 = 0 →
      i ∈ boundaryForcedPositions55 F)
    (hruns : boundaryForcedRunCount55 F = 3)
    (htOdd : t.val % 2 = 1) (htQ : t ∉ Q) :
    t ∈ boundaryForcedPositions55 F := by
  classical
  obtain ⟨e, heO, heQ, heMid, _, _⟩ :=
    fifth_boundary_omission_is_side_midpoint_of_three_runs F Q hacyc hPcard
      hQcard hQomit hQodd hcorners hruns
  by_contra htP
  have htO : t ∈ (Finset.univ : Finset (Fin 16)) \
      boundaryForcedPositions55 F := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, htP⟩
  have hOcard : ((Finset.univ : Finset (Fin 16)) \
      boundaryForcedPositions55 F).card = 5 := by
    simp [Finset.card_sdiff, hPcard]
  have hdiffCard : (((Finset.univ : Finset (Fin 16)) \
      boundaryForcedPositions55 F) \ Q).card = 1 := by
    rw [Finset.card_sdiff_of_subset hQomit, hOcard, hQcard]
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hdiffCard
  have heDiff : e ∈ ((Finset.univ : Finset (Fin 16)) \
      boundaryForcedPositions55 F) \ Q := Finset.mem_sdiff.mpr ⟨heO, heQ⟩
  have htDiff : t ∈ ((Finset.univ : Finset (Fin 16)) \
      boundaryForcedPositions55 F) \ Q := Finset.mem_sdiff.mpr ⟨htO, htQ⟩
  rw [ha] at heDiff htDiff
  simp only [Finset.mem_singleton] at heDiff htDiff
  have hte : t = e := htDiff.trans heDiff.symm
  rw [hte] at htOdd
  simp only [Finset.mem_insert, Finset.mem_singleton] at heMid
  rcases heMid with h | h | h | h <;> norm_num [h] at htOdd

private lemma attachment_boundary_neighbor_forced
    (F : Finset (GridVertex 5 5)) (x b : GridVertex 5 5)
    (hxOutside : F \ boundary55 = {x}) (hxF : x ∈ F)
    (hdegree : ((gridGraph 5 5).induce (↑F : Set (GridVertex 5 5))).degree
      ⟨x, hxF⟩ = 1)
    (honly : ∀ y, (gridGraph 5 5).Adj x y → y ∈ boundary55 → y = b) :
    b ∈ F := by
  let H := (gridGraph 5 5).induce (↑F : Set (GridVertex 5 5))
  have hpos : 0 < H.degree ⟨x, hxF⟩ := by
    change 0 < ((gridGraph 5 5).induce (↑F : Set (GridVertex 5 5))).degree
      ⟨x, hxF⟩
    rw [hdegree]
    norm_num
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hpos
  have hxy : (gridGraph 5 5).Adj x y.1 := by
    simpa [H, SimpleGraph.mem_neighborFinset] using hy
  have hyBoundary : y.1 ∈ boundary55 := by
    by_contra hyNotBoundary
    have hyOutside : y.1 ∈ F \ boundary55 :=
      Finset.mem_sdiff.mpr ⟨y.2, hyNotBoundary⟩
    have hyx : y.1 = x := by simpa [hxOutside] using hyOutside
    exact (gridGraph 5 5).ne_of_adj hxy hyx.symm
  simpa [honly y.1 hxy hyBoundary] using y.2

private lemma corner_boundary_positions_forced (F : Finset (GridVertex 5 5))
    (hcorners : corners55 ⊆ F) :
    ∀ i : Fin 16, i.val % 4 = 0 → i ∈ boundaryForcedPositions55 F := by
  intro i hi
  have hiVal : i.val = 0 ∨ i.val = 4 ∨ i.val = 8 ∨ i.val = 12 := by omega
  have hiCases : i = 0 ∨ i = 4 ∨ i = 8 ∨ i = 12 := by
    rcases hiVal with h | h | h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
    · exact Or.inr (Or.inr (Or.inr (Fin.ext h)))
  rcases hiCases with rfl | rfl | rfl | rfl <;>
    simp only [boundaryForcedPositions55, Finset.mem_filter, Finset.mem_univ,
      true_and, boundaryVertex55, boundaryPosition55, gridBoundaryVertex,
      gridBoundaryLength] <;> apply hcorners <;> simp [corners55]

private lemma forced_six_cycle_false
    (F : Finset (GridVertex 5 5))
    (hacyc : (forcedEdgeGraph (gridGraph 5 5) (↑F : Set _)).IsAcyclic)
    (v0 v1 v2 v3 v4 v5 : GridVertex 5 5)
    (hnodup : [v0, v1, v2, v3, v4, v5].Nodup)
    (h01 : (gridGraph 5 5).Adj v0 v1)
    (h12 : (gridGraph 5 5).Adj v1 v2)
    (h23 : (gridGraph 5 5).Adj v2 v3)
    (h34 : (gridGraph 5 5).Adj v3 v4)
    (h45 : (gridGraph 5 5).Adj v4 v5)
    (h50 : (gridGraph 5 5).Adj v5 v0)
    (hv0 : v0 ∈ F) (hv1 : v1 ∈ F) (hv3 : v3 ∈ F) (hv4 : v4 ∈ F) : False := by
  let G := forcedEdgeGraph (gridGraph 5 5) (↑F : Set (GridVertex 5 5))
  have hg01 : G.Adj v0 v1 := ⟨h01, Or.inl hv0⟩
  have hg12 : G.Adj v1 v2 := ⟨h12, Or.inl hv1⟩
  have hg23 : G.Adj v2 v3 := ⟨h23, Or.inr hv3⟩
  have hg34 : G.Adj v3 v4 := ⟨h34, Or.inl hv3⟩
  have hg45 : G.Adj v4 v5 := ⟨h45, Or.inl hv4⟩
  have hg50 : G.Adj v5 v0 := ⟨h50, Or.inr hv0⟩
  let q : G.Walk v1 v0 := Walk.cons hg12 (Walk.cons hg23
    (Walk.cons hg34 (Walk.cons hg45 (Walk.cons hg50 Walk.nil))))
  let p : G.Walk v0 v0 := Walk.cons hg01 q
  have hqPath : q.IsPath := by
    simp_all [q, List.nodup_cons, eq_comm]
  have hg01Not : s(v0, v1) ∉ q.edges := by
    simp_all [q, List.nodup_cons, eq_comm]
  apply hacyc p
  change (Walk.cons hg01 q).IsCycle
  rw [Walk.cons_isCycle_iff]
  exact ⟨hqPath, hg01Not⟩

private lemma final_profile_attachment_top_impossible
    (F : Finset (GridVertex 5 5))
    (hxOutside : F \ boundary55 = {((1, 2) : GridVertex 5 5)})
    (hxF : ((1, 2) : GridVertex 5 5) ∈ F)
    (hacyc : (forcedEdgeGraph (gridGraph 5 5)
      (↑F : Set (GridVertex 5 5))).IsAcyclic)
    (hPcard : (boundaryForcedPositions55 F).card = 11)
    (hcorners : corners55 ⊆ F)
    (homit00 : (0, 1) ∉ F ∨ (1, 0) ∉ F)
    (homit04 : (0, 3) ∉ F ∨ (1, 4) ∉ F)
    (homit44 : (3, 4) ∉ F ∨ (4, 3) ∉ F)
    (homit40 : (4, 1) ∉ F ∨ (3, 0) ∉ F)
    (hruns : boundaryForcedRunCount55 F = 3)
    (hdegree : ((gridGraph 5 5).induce (↑F : Set (GridVertex 5 5))).degree
      ⟨(1, 2), hxF⟩ = 1) : False := by
  classical
  let x : GridVertex 5 5 := (1, 2)
  let b : GridVertex 5 5 := (0, 2)
  let H := (gridGraph 5 5).induce (↑F : Set (GridVertex 5 5))
  have hbF : b ∈ F := by
    have hpos : 0 < H.degree ⟨x, hxF⟩ := by
      change 0 < ((gridGraph 5 5).induce (↑F : Set (GridVertex 5 5))).degree
        ⟨(1, 2), hxF⟩
      rw [hdegree]
      norm_num
    obtain ⟨y, hy⟩ := Finset.card_pos.mp hpos
    have hxy : (gridGraph 5 5).Adj x y.1 := by
      simpa [H, SimpleGraph.mem_neighborFinset] using hy
    have hyBoundary : y.1 ∈ boundary55 := by
      by_contra hyNotBoundary
      have hyOutside : y.1 ∈ F \ boundary55 :=
        Finset.mem_sdiff.mpr ⟨y.2, hyNotBoundary⟩
      have hyx : y.1 = x := by simpa [hxOutside, x] using hyOutside
      exact (gridGraph 5 5).ne_of_adj hxy hyx.symm
    have hyb : y.1 = b := by
      change adjacent 5 5 x y.1 at hxy
      simp only [boundary55, Finset.mem_filter, Finset.mem_univ, true_and] at hyBoundary
      dsimp [x] at hxy
      dsimp [b]
      rcases hxy with ⟨hr, hc | hc⟩ | ⟨hc, hr | hr⟩ <;>
        rcases hyBoundary with h | h | h | h <;>
        apply Prod.ext <;> apply Fin.ext <;> norm_num at hr hc h ⊢ <;> omega
    simpa [hyb] using y.2
  have h01not : ((0, 1) : GridVertex 5 5) ∉ F := by
    rcases homit00 with h | h
    · exact h
    · by_contra h01
      have hp := forced_two_edge_walk_parallel hacyc hxF hbF h01
        (by simp [gridGraph, adjacent, x, b]) (by simp [gridGraph, adjacent, b])
      rcases hp with hp | hp <;> norm_num [x, b] at hp <;> omega
  have h03not : ((0, 3) : GridVertex 5 5) ∉ F := by
    rcases homit04 with h | h
    · exact h
    · by_contra h03
      have hp := forced_two_edge_walk_parallel hacyc hxF hbF h03
        (by simp [gridGraph, adjacent, x, b]) (by simp [gridGraph, adjacent, b])
      rcases hp with hp | hp <;> norm_num [x, b] at hp <;> omega
  let q2 : Fin 16 := if (3, 4) ∈ F then 9 else 7
  let q3 : Fin 16 := if (4, 1) ∈ F then 13 else 11
  let Q : Finset (Fin 16) := {1, 3, q2, q3}
  have hq2 : q2 = 7 ∨ q2 = 9 := by
    by_cases h : (3, 4) ∈ F <;> simp [q2, h]
  have hq3 : q3 = 11 ∨ q3 = 13 := by
    by_cases h : (4, 1) ∈ F <;> simp [q3, h]
  have hq2omit : boundaryVertex55 q2 ∉ F := by
    dsimp [q2]
    split_ifs with h
    · rcases homit44 with h' | h'
      · exact (h' h).elim
      · simpa [boundaryVertex55, boundaryPosition55, gridBoundaryVertex,
          gridBoundaryLength] using h'
    · simpa [boundaryVertex55, boundaryPosition55, gridBoundaryVertex,
        gridBoundaryLength] using h
  have hq3omit : boundaryVertex55 q3 ∉ F := by
    dsimp [q3]
    split_ifs with h
    · rcases homit40 with h' | h'
      · exact (h' h).elim
      · simpa [boundaryVertex55, boundaryPosition55, gridBoundaryVertex,
          gridBoundaryLength] using h'
    · simpa [boundaryVertex55, boundaryPosition55, gridBoundaryVertex,
        gridBoundaryLength] using h
  have hQcard : Q.card = 4 := by
    rcases hq2 with hq2 | hq2 <;> rcases hq3 with hq3 | hq3 <;>
      simp [Q, hq2, hq3]
  have hQomit : Q ⊆ (Finset.univ : Finset (Fin 16)) \
      boundaryForcedPositions55 F := by
    intro q hq
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | hq | hq
    · simpa [boundaryForcedPositions55, boundaryVertex55, boundaryPosition55,
        gridBoundaryVertex, gridBoundaryLength] using h01not
    · simpa [boundaryForcedPositions55, boundaryVertex55, boundaryPosition55,
        gridBoundaryVertex, gridBoundaryLength] using h03not
    · subst q
      simpa [boundaryForcedPositions55] using hq2omit
    · subst q
      simpa [boundaryForcedPositions55] using hq3omit
  have hQodd : ∀ q ∈ Q, q.val % 2 = 1 := by
    intro q hq
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | hq | hq
    · norm_num
    · norm_num
    · rw [hq]
      rcases hq2 with hq2 | hq2 <;> simp [hq2]
    · rw [hq]
      rcases hq3 with hq3 | hq3 <;> simp [hq3]
  have hcornerPositions : ∀ i : Fin 16, i.val % 4 = 0 →
      i ∈ boundaryForcedPositions55 F := by
    intro i hi
    have hiCases : i = 0 ∨ i = 4 ∨ i = 8 ∨ i = 12 := by
      have hiVal : i.val = 0 ∨ i.val = 4 ∨ i.val = 8 ∨ i.val = 12 := by omega
      rcases hiVal with h | h | h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Or.inl (Fin.ext h))
      · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
      · exact Or.inr (Or.inr (Or.inr (Fin.ext h)))
    rcases hiCases with rfl | rfl | rfl | rfl <;>
      simp only [boundaryForcedPositions55, Finset.mem_filter, Finset.mem_univ,
        true_and, boundaryVertex55, boundaryPosition55, gridBoundaryVertex,
        gridBoundaryLength] <;> apply hcorners <;> simp [corners55]
  obtain ⟨e, heO, heQ, heMid, hePrev, heNext⟩ :=
    fifth_boundary_omission_is_side_midpoint_of_three_runs F Q hacyc hPcard
      hQcard hQomit hQodd hcornerPositions hruns
  have he : e = 10 := by
    have hbP : (2 : Fin 16) ∈ boundaryForcedPositions55 F := by
      simpa [boundaryForcedPositions55, boundaryVertex55, boundaryPosition55,
        gridBoundaryVertex, gridBoundaryLength, b] using hbF
    have heCases : e = 2 ∨ e = 6 ∨ e = 10 ∨ e = 14 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at heMid
      rcases heMid with h | h | h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Or.inl (Fin.ext h))
      · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
      · exact Or.inr (Or.inr (Or.inr (Fin.ext h)))
    rcases heCases with rfl | rfl | rfl | rfl
    · exact ((Finset.mem_sdiff.mp heO).2 hbP).elim
    · have : (5 : Fin 16) ∈ Q := by simpa using hePrev
      rcases hq2 with hq2 | hq2 <;> rcases hq3 with hq3 | hq3 <;>
        simp [Q, hq2, hq3] at this
    · rfl
    · have : (15 : Fin 16) ∈ Q := by simpa using heNext
      rcases hq2 with hq2 | hq2 <;> rcases hq3 with hq3 | hq3 <;>
        simp [Q, hq2, hq3] at this
  have h15F : ((1, 0) : GridVertex 5 5) ∈ F := by
    by_contra h15
    have h15O : (15 : Fin 16) ∈ (Finset.univ : Finset (Fin 16)) \
        boundaryForcedPositions55 F := by
      simpa [boundaryForcedPositions55, boundaryVertex55, boundaryPosition55,
        gridBoundaryVertex, gridBoundaryLength] using h15
    have hOcard : ((Finset.univ : Finset (Fin 16)) \
        boundaryForcedPositions55 F).card = 5 := by
      simp [Finset.card_sdiff, hPcard]
    have h15Q : (15 : Fin 16) ∉ Q := by
      rcases hq2 with hq2 | hq2 <;> rcases hq3 with hq3 | hq3 <;>
        simp [Q, hq2, hq3]
    have hdiffCard : (((Finset.univ : Finset (Fin 16)) \
        boundaryForcedPositions55 F) \ Q).card = 1 := by
      rw [Finset.card_sdiff_of_subset hQomit, hOcard, hQcard]
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hdiffCard
    have heDiff : e ∈ ((Finset.univ : Finset (Fin 16)) \
        boundaryForcedPositions55 F) \ Q := Finset.mem_sdiff.mpr ⟨heO, heQ⟩
    have h15Diff : (15 : Fin 16) ∈ ((Finset.univ : Finset (Fin 16)) \
        boundaryForcedPositions55 F) \ Q := Finset.mem_sdiff.mpr ⟨h15O, h15Q⟩
    rw [ha] at heDiff h15Diff
    simp only [Finset.mem_singleton] at heDiff h15Diff
    have h15e : (15 : Fin 16) = e := h15Diff.trans heDiff.symm
    rw [he] at h15e
    have := congrArg Fin.val h15e
    norm_num at this
  have h00F : ((0, 0) : GridVertex 5 5) ∈ F := hcorners (by simp [corners55])
  exact forced_six_cycle_false F hacyc x b (0, 1) (0, 0) (1, 0) (1, 1)
    (by simp [x, b, gridVertex55_eq_iff_vals])
    (by simp [gridGraph, adjacent, x, b])
    (by simp [gridGraph, adjacent, b])
    (by simp [gridGraph, adjacent])
    (by simp [gridGraph, adjacent])
    (by simp [gridGraph, adjacent])
    (by simp [gridGraph, adjacent, x]) hxF hbF h00F h15F

private lemma final_profile_attachment_right_impossible
    (F : Finset (GridVertex 5 5))
    (hxOutside : F \ boundary55 = {((2, 3) : GridVertex 5 5)})
    (hxF : ((2, 3) : GridVertex 5 5) ∈ F)
    (hacyc : (forcedEdgeGraph (gridGraph 5 5)
      (↑F : Set (GridVertex 5 5))).IsAcyclic)
    (hPcard : (boundaryForcedPositions55 F).card = 11)
    (hcorners : corners55 ⊆ F)
    (homit00 : (0, 1) ∉ F ∨ (1, 0) ∉ F)
    (homit40 : (4, 1) ∉ F ∨ (3, 0) ∉ F)
    (hruns : boundaryForcedRunCount55 F = 3)
    (hdegree : ((gridGraph 5 5).induce (↑F : Set (GridVertex 5 5))).degree
      ⟨(2, 3), hxF⟩ = 1) : False := by
  classical
  let x : GridVertex 5 5 := (2, 3)
  let b : GridVertex 5 5 := (2, 4)
  have hbF : b ∈ F := attachment_boundary_neighbor_forced F x b hxOutside hxF
    (by simpa [x] using hdegree) (by
      intro y hxy hyB
      change adjacent 5 5 x y at hxy
      simp only [boundary55, Finset.mem_filter, Finset.mem_univ, true_and] at hyB
      dsimp [x, b] at hxy ⊢
      rcases hxy with ⟨hr, hc | hc⟩ | ⟨hc, hr | hr⟩ <;>
        rcases hyB with h | h | h | h <;>
        apply Prod.ext <;> apply Fin.ext <;> norm_num at hr hc h ⊢ <;> omega)
  have h14not : ((1, 4) : GridVertex 5 5) ∉ F := by
    intro h14
    have hp := forced_two_edge_walk_parallel hacyc hxF hbF h14
      (by simp [gridGraph, adjacent, x, b]) (by simp [gridGraph, adjacent, b])
    rcases hp with hp | hp <;> norm_num [x, b] at hp <;> omega
  have h34not : ((3, 4) : GridVertex 5 5) ∉ F := by
    intro h34
    have hp := forced_two_edge_walk_parallel hacyc hxF hbF h34
      (by simp [gridGraph, adjacent, x, b]) (by simp [gridGraph, adjacent, b])
    rcases hp with hp | hp <;> norm_num [x, b] at hp <;> omega
  let q0 : Fin 16 := if (1, 0) ∈ F then 1 else 15
  let q3 : Fin 16 := if (4, 1) ∈ F then 13 else 11
  let Q : Finset (Fin 16) := {q0, 5, 7, q3}
  have hq0 : q0 = 1 ∨ q0 = 15 := by
    by_cases h : (1, 0) ∈ F <;> simp [q0, h]
  have hq3 : q3 = 11 ∨ q3 = 13 := by
    by_cases h : (4, 1) ∈ F <;> simp [q3, h]
  have hq0omit : boundaryVertex55 q0 ∉ F := by
    dsimp [q0]
    split_ifs with h
    · rcases homit00 with h' | h'
      · simpa [boundaryVertex55, boundaryPosition55, gridBoundaryVertex,
          gridBoundaryLength] using h'
      · exact (h' h).elim
    · simpa [boundaryVertex55, boundaryPosition55, gridBoundaryVertex,
        gridBoundaryLength] using h
  have hq3omit : boundaryVertex55 q3 ∉ F := by
    dsimp [q3]
    split_ifs with h
    · rcases homit40 with h' | h'
      · exact (h' h).elim
      · simpa [boundaryVertex55, boundaryPosition55, gridBoundaryVertex,
          gridBoundaryLength] using h'
    · simpa [boundaryVertex55, boundaryPosition55, gridBoundaryVertex,
        gridBoundaryLength] using h
  have hQcard : Q.card = 4 := by
    rcases hq0 with hq0 | hq0 <;> rcases hq3 with hq3 | hq3 <;>
      simp [Q, hq0, hq3]
  have hQomit : Q ⊆ (Finset.univ : Finset (Fin 16)) \
      boundaryForcedPositions55 F := by
    intro q hq
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with hq | rfl | rfl | hq
    · subst q; simpa [boundaryForcedPositions55] using hq0omit
    · simpa [boundaryForcedPositions55, boundaryVertex55, boundaryPosition55,
        gridBoundaryVertex, gridBoundaryLength] using h14not
    · simpa [boundaryForcedPositions55, boundaryVertex55, boundaryPosition55,
        gridBoundaryVertex, gridBoundaryLength] using h34not
    · subst q; simpa [boundaryForcedPositions55] using hq3omit
  have hQodd : ∀ q ∈ Q, q.val % 2 = 1 := by
    intro q hq
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with hq | rfl | rfl | hq
    · rw [hq]; rcases hq0 with hq0 | hq0 <;> simp [hq0]
    · norm_num
    · norm_num
    · rw [hq]; rcases hq3 with hq3 | hq3 <;> simp [hq3]
  have hcornerPositions : ∀ i : Fin 16, i.val % 4 = 0 →
      i ∈ boundaryForcedPositions55 F := by
    intro i hi
    have hiVal : i.val = 0 ∨ i.val = 4 ∨ i.val = 8 ∨ i.val = 12 := by omega
    have hiCases : i = 0 ∨ i = 4 ∨ i = 8 ∨ i = 12 := by
      rcases hiVal with h | h | h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Or.inl (Fin.ext h))
      · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
      · exact Or.inr (Or.inr (Or.inr (Fin.ext h)))
    rcases hiCases with rfl | rfl | rfl | rfl <;>
      simp only [boundaryForcedPositions55, Finset.mem_filter, Finset.mem_univ,
        true_and, boundaryVertex55, boundaryPosition55, gridBoundaryVertex,
        gridBoundaryLength] <;> apply hcorners <;> simp [corners55]
  have h03F : ((0, 3) : GridVertex 5 5) ∈ F := by
    have h3P := odd_boundary_position_forced_of_three_runs F Q 3 hacyc hPcard
      hQcard hQomit hQodd hcornerPositions hruns (by norm_num) (by
        rcases hq0 with hq0 | hq0 <;> rcases hq3 with hq3 | hq3 <;>
          simp [Q, hq0, hq3])
    simpa [boundaryForcedPositions55, boundaryVertex55, boundaryPosition55,
      gridBoundaryVertex, gridBoundaryLength] using h3P
  have h04F : ((0, 4) : GridVertex 5 5) ∈ F := hcorners (by simp [corners55])
  exact forced_six_cycle_false F hacyc x b (1, 4) (0, 4) (0, 3) (1, 3)
    (by simp [x, b, gridVertex55_eq_iff_vals])
    (by simp [gridGraph, adjacent, x, b])
    (by simp [gridGraph, adjacent, b])
    (by simp [gridGraph, adjacent])
    (by simp [gridGraph, adjacent])
    (by simp [gridGraph, adjacent])
    (by simp [gridGraph, adjacent, x]) hxF hbF h04F h03F

private lemma final_profile_attachment_bottom_impossible
    (F : Finset (GridVertex 5 5))
    (hxOutside : F \ boundary55 = {((3, 2) : GridVertex 5 5)})
    (hxF : ((3, 2) : GridVertex 5 5) ∈ F)
    (hacyc : (forcedEdgeGraph (gridGraph 5 5) (↑F : Set _)).IsAcyclic)
    (hPcard : (boundaryForcedPositions55 F).card = 11)
    (hcorners : corners55 ⊆ F)
    (homit00 : (0, 1) ∉ F ∨ (1, 0) ∉ F)
    (homit04 : (0, 3) ∉ F ∨ (1, 4) ∉ F)
    (hruns : boundaryForcedRunCount55 F = 3)
    (hdegree : ((gridGraph 5 5).induce (↑F : Set _)).degree
      ⟨(3, 2), hxF⟩ = 1) : False := by
  classical
  let x : GridVertex 5 5 := (3, 2)
  let b : GridVertex 5 5 := (4, 2)
  have hbF : b ∈ F := attachment_boundary_neighbor_forced F x b hxOutside hxF
    (by simpa [x] using hdegree) (by
      intro y hxy hyB
      change adjacent 5 5 x y at hxy
      simp only [boundary55, Finset.mem_filter, Finset.mem_univ, true_and] at hyB
      dsimp [x, b] at hxy ⊢
      rcases hxy with ⟨hr, hc | hc⟩ | ⟨hc, hr | hr⟩ <;>
        rcases hyB with h | h | h | h <;>
        apply Prod.ext <;> apply Fin.ext <;> norm_num at hr hc h ⊢ <;> omega)
  have h43not : ((4, 3) : GridVertex 5 5) ∉ F := by
    intro h43
    have hp := forced_two_edge_walk_parallel hacyc hxF hbF h43
      (by simp [gridGraph, adjacent, x, b]) (by simp [gridGraph, adjacent, b])
    rcases hp with hp | hp <;> norm_num [x, b] at hp <;> omega
  have h41not : ((4, 1) : GridVertex 5 5) ∉ F := by
    intro h41
    have hp := forced_two_edge_walk_parallel hacyc hxF hbF h41
      (by simp [gridGraph, adjacent, x, b]) (by simp [gridGraph, adjacent, b])
    rcases hp with hp | hp <;> norm_num [x, b] at hp <;> omega
  let q0 : Fin 16 := if (1, 0) ∈ F then 1 else 15
  let q1 : Fin 16 := if (1, 4) ∈ F then 3 else 5
  let Q : Finset (Fin 16) := {q0, q1, 9, 11}
  have hq0 : q0 = 1 ∨ q0 = 15 := by
    by_cases h : (1, 0) ∈ F <;> simp [q0, h]
  have hq1 : q1 = 3 ∨ q1 = 5 := by
    by_cases h : (1, 4) ∈ F <;> simp [q1, h]
  have hq0omit : boundaryVertex55 q0 ∉ F := by
    dsimp [q0]; split_ifs with h
    · rcases homit00 with h' | h'
      · simpa [boundaryVertex55, boundaryPosition55, gridBoundaryVertex,
          gridBoundaryLength] using h'
      · exact (h' h).elim
    · simpa [boundaryVertex55, boundaryPosition55, gridBoundaryVertex,
        gridBoundaryLength] using h
  have hq1omit : boundaryVertex55 q1 ∉ F := by
    dsimp [q1]; split_ifs with h
    · rcases homit04 with h' | h'
      · simpa [boundaryVertex55, boundaryPosition55, gridBoundaryVertex,
          gridBoundaryLength] using h'
      · exact (h' h).elim
    · simpa [boundaryVertex55, boundaryPosition55, gridBoundaryVertex,
        gridBoundaryLength] using h
  have hQcard : Q.card = 4 := by
    rcases hq0 with hq0 | hq0 <;> rcases hq1 with hq1 | hq1 <;>
      simp [Q, hq0, hq1]
  have hQomit : Q ⊆ (Finset.univ : Finset (Fin 16)) \
      boundaryForcedPositions55 F := by
    intro q hq
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with hq | hq | rfl | rfl
    · subst q; simpa [boundaryForcedPositions55] using hq0omit
    · subst q; simpa [boundaryForcedPositions55] using hq1omit
    · simpa [boundaryForcedPositions55, boundaryVertex55, boundaryPosition55,
        gridBoundaryVertex, gridBoundaryLength] using h43not
    · simpa [boundaryForcedPositions55, boundaryVertex55, boundaryPosition55,
        gridBoundaryVertex, gridBoundaryLength] using h41not
  have hQodd : ∀ q ∈ Q, q.val % 2 = 1 := by
    intro q hq
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with hq | hq | rfl | rfl
    · rw [hq]; rcases hq0 with hq0 | hq0 <;> simp [hq0]
    · rw [hq]; rcases hq1 with hq1 | hq1 <;> simp [hq1]
    · norm_num
    · norm_num
  have h13F : ((3, 0) : GridVertex 5 5) ∈ F := by
    have h13P := odd_boundary_position_forced_of_three_runs F Q 13 hacyc hPcard
      hQcard hQomit hQodd (corner_boundary_positions_forced F hcorners) hruns
      (by norm_num) (by
        rcases hq0 with hq0 | hq0 <;> rcases hq1 with hq1 | hq1 <;>
          simp [Q, hq0, hq1])
    simpa [boundaryForcedPositions55, boundaryVertex55, boundaryPosition55,
      gridBoundaryVertex, gridBoundaryLength] using h13P
  have h40F : ((4, 0) : GridVertex 5 5) ∈ F := hcorners (by simp [corners55])
  exact forced_six_cycle_false F hacyc x b (4, 1) (4, 0) (3, 0) (3, 1)
    (by simp [x, b, gridVertex55_eq_iff_vals])
    (by simp [gridGraph, adjacent, x, b])
    (by simp [gridGraph, adjacent, b])
    (by simp [gridGraph, adjacent])
    (by simp [gridGraph, adjacent])
    (by simp [gridGraph, adjacent])
    (by simp [gridGraph, adjacent, x]) hxF hbF h40F h13F

private lemma final_profile_attachment_left_impossible
    (F : Finset (GridVertex 5 5))
    (hxOutside : F \ boundary55 = {((2, 1) : GridVertex 5 5)})
    (hxF : ((2, 1) : GridVertex 5 5) ∈ F)
    (hacyc : (forcedEdgeGraph (gridGraph 5 5) (↑F : Set _)).IsAcyclic)
    (hPcard : (boundaryForcedPositions55 F).card = 11)
    (hcorners : corners55 ⊆ F)
    (homit04 : (0, 3) ∉ F ∨ (1, 4) ∉ F)
    (homit44 : (3, 4) ∉ F ∨ (4, 3) ∉ F)
    (hruns : boundaryForcedRunCount55 F = 3)
    (hdegree : ((gridGraph 5 5).induce (↑F : Set _)).degree
      ⟨(2, 1), hxF⟩ = 1) : False := by
  classical
  let x : GridVertex 5 5 := (2, 1)
  let b : GridVertex 5 5 := (2, 0)
  have hbF : b ∈ F := attachment_boundary_neighbor_forced F x b hxOutside hxF
    (by simpa [x] using hdegree) (by
      intro y hxy hyB
      change adjacent 5 5 x y at hxy
      simp only [boundary55, Finset.mem_filter, Finset.mem_univ, true_and] at hyB
      dsimp [x, b] at hxy ⊢
      rcases hxy with ⟨hr, hc | hc⟩ | ⟨hc, hr | hr⟩ <;>
        rcases hyB with h | h | h | h <;>
        apply Prod.ext <;> apply Fin.ext <;> norm_num at hr hc h ⊢ <;> omega)
  have h30not : ((3, 0) : GridVertex 5 5) ∉ F := by
    intro h30
    have hp := forced_two_edge_walk_parallel hacyc hxF hbF h30
      (by simp [gridGraph, adjacent, x, b]) (by simp [gridGraph, adjacent, b])
    rcases hp with hp | hp <;> norm_num [x, b] at hp <;> omega
  have h10not : ((1, 0) : GridVertex 5 5) ∉ F := by
    intro h10
    have hp := forced_two_edge_walk_parallel hacyc hxF hbF h10
      (by simp [gridGraph, adjacent, x, b]) (by simp [gridGraph, adjacent, b])
    rcases hp with hp | hp <;> norm_num [x, b] at hp <;> omega
  let q1 : Fin 16 := if (1, 4) ∈ F then 3 else 5
  let q2 : Fin 16 := if (4, 3) ∈ F then 7 else 9
  let Q : Finset (Fin 16) := {15, q1, q2, 13}
  have hq1 : q1 = 3 ∨ q1 = 5 := by
    by_cases h : (1, 4) ∈ F <;> simp [q1, h]
  have hq2 : q2 = 7 ∨ q2 = 9 := by
    by_cases h : (4, 3) ∈ F <;> simp [q2, h]
  have hq1omit : boundaryVertex55 q1 ∉ F := by
    dsimp [q1]; split_ifs with h
    · rcases homit04 with h' | h'
      · simpa [boundaryVertex55, boundaryPosition55, gridBoundaryVertex,
          gridBoundaryLength] using h'
      · exact (h' h).elim
    · simpa [boundaryVertex55, boundaryPosition55, gridBoundaryVertex,
        gridBoundaryLength] using h
  have hq2omit : boundaryVertex55 q2 ∉ F := by
    dsimp [q2]; split_ifs with h
    · rcases homit44 with h' | h'
      · simpa [boundaryVertex55, boundaryPosition55, gridBoundaryVertex,
          gridBoundaryLength] using h'
      · exact (h' h).elim
    · simpa [boundaryVertex55, boundaryPosition55, gridBoundaryVertex,
        gridBoundaryLength] using h
  have hQcard : Q.card = 4 := by
    rcases hq1 with hq1 | hq1 <;> rcases hq2 with hq2 | hq2 <;>
      simp [Q, hq1, hq2]
  have hQomit : Q ⊆ (Finset.univ : Finset (Fin 16)) \
      boundaryForcedPositions55 F := by
    intro q hq
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | hq | hq | rfl
    · simpa [boundaryForcedPositions55, boundaryVertex55, boundaryPosition55,
        gridBoundaryVertex, gridBoundaryLength] using h10not
    · subst q; simpa [boundaryForcedPositions55] using hq1omit
    · subst q; simpa [boundaryForcedPositions55] using hq2omit
    · simpa [boundaryForcedPositions55, boundaryVertex55, boundaryPosition55,
        gridBoundaryVertex, gridBoundaryLength] using h30not
  have hQodd : ∀ q ∈ Q, q.val % 2 = 1 := by
    intro q hq
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | hq | hq | rfl
    · norm_num
    · rw [hq]; rcases hq1 with hq1 | hq1 <;> simp [hq1]
    · rw [hq]; rcases hq2 with hq2 | hq2 <;> simp [hq2]
    · norm_num
  have h41F : ((4, 1) : GridVertex 5 5) ∈ F := by
    have h11P := odd_boundary_position_forced_of_three_runs F Q 11 hacyc hPcard
      hQcard hQomit hQodd (corner_boundary_positions_forced F hcorners) hruns
      (by norm_num) (by
        rcases hq1 with hq1 | hq1 <;> rcases hq2 with hq2 | hq2 <;>
          simp [Q, hq1, hq2])
    simpa [boundaryForcedPositions55, boundaryVertex55, boundaryPosition55,
      gridBoundaryVertex, gridBoundaryLength] using h11P
  have h40F : ((4, 0) : GridVertex 5 5) ∈ F := hcorners (by simp [corners55])
  exact forced_six_cycle_false F hacyc x b (3, 0) (4, 0) (4, 1) (3, 1)
    (by simp [x, b, gridVertex55_eq_iff_vals])
    (by simp [gridGraph, adjacent, x, b])
    (by simp [gridGraph, adjacent, b])
    (by simp [gridGraph, adjacent])
    (by simp [gridGraph, adjacent])
    (by simp [gridGraph, adjacent])
    (by simp [gridGraph, adjacent, x]) hxF hbF h40F h41F

private lemma boundaryForcedPositions55_card_eq_boundary_inter
    (F : Finset (GridVertex 5 5)) :
    (boundaryForcedPositions55 F).card = (F ∩ boundary55).card := by
  have himage : (boundaryForcedPositions55 F).image boundaryVertex55 =
      F ∩ boundary55 := by
    ext v
    constructor
    · rintro hv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
      exact Finset.mem_inter.mpr ⟨by
        simpa [boundaryForcedPositions55] using hi, by
        simpa [boundary55, IsGridBoundary] using
          gridBoundaryVertex_isBoundary (m := 5) (n := 5)
            (by omega) (by omega) (boundaryPosition55 i)⟩
    · intro hv
      have hv' := Finset.mem_inter.mp hv
      have hvB : IsGridBoundary v := by
        simpa [boundary55, IsGridBoundary] using hv'.2
      obtain ⟨i, hi⟩ := exists_gridBoundaryPosition (m := 5) (n := 5)
        (by omega) (by omega) v hvB
      let j : Fin 16 := ⟨i.val, by simpa [gridBoundaryLength] using i.isLt⟩
      exact Finset.mem_image.mpr ⟨j, by
        simpa [boundaryForcedPositions55, boundaryVertex55,
          boundaryPosition55, j, hi] using hv'.1, by
        simpa [boundaryVertex55, boundaryPosition55, j] using hi⟩
  rw [← himage, Finset.card_image_of_injective]
  intro i j hij
  exact gridBoundaryVertex_injective (m := 5) (n := 5)
    (by omega) (by omega) hij

private lemma final_profile_three_runs_lower
    (F : Finset (GridVertex 5 5))
    (hacyc : (forcedEdgeGraph (gridGraph 5 5) (↑F : Set _)).IsAcyclic)
    (hPcard : (boundaryForcedPositions55 F).card = 11)
    (homit00 : (0, 1) ∉ F ∨ (1, 0) ∉ F)
    (homit04 : (0, 3) ∉ F ∨ (1, 4) ∉ F)
    (homit44 : (3, 4) ∉ F ∨ (4, 3) ∉ F)
    (homit40 : (4, 1) ∉ F ∨ (3, 0) ∉ F) :
    3 ≤ boundaryForcedRunCount55 F := by
  classical
  let q0 : Fin 16 := if (1, 0) ∈ F then 1 else 15
  let q1 : Fin 16 := if (1, 4) ∈ F then 3 else 5
  let q2 : Fin 16 := if (4, 3) ∈ F then 7 else 9
  let q3 : Fin 16 := if (3, 0) ∈ F then 11 else 13
  let Q : Finset (Fin 16) := {q0, q1, q2, q3}
  have hq0 : q0 = 1 ∨ q0 = 15 := by
    by_cases h : (1, 0) ∈ F <;> simp [q0, h]
  have hq1 : q1 = 3 ∨ q1 = 5 := by
    by_cases h : (1, 4) ∈ F <;> simp [q1, h]
  have hq2 : q2 = 7 ∨ q2 = 9 := by
    by_cases h : (4, 3) ∈ F <;> simp [q2, h]
  have hq3 : q3 = 11 ∨ q3 = 13 := by
    by_cases h : (3, 0) ∈ F <;> simp [q3, h]
  have hq0omit : boundaryVertex55 q0 ∉ F := by
    dsimp [q0]; split_ifs with h
    · exact homit00.resolve_right (by simpa using h)
    · simpa [boundaryVertex55, boundaryPosition55, gridBoundaryVertex,
        gridBoundaryLength] using h
  have hq1omit : boundaryVertex55 q1 ∉ F := by
    dsimp [q1]; split_ifs with h
    · exact homit04.resolve_right (by simpa using h)
    · simpa [boundaryVertex55, boundaryPosition55, gridBoundaryVertex,
        gridBoundaryLength] using h
  have hq2omit : boundaryVertex55 q2 ∉ F := by
    dsimp [q2]; split_ifs with h
    · exact homit44.resolve_right (by simpa using h)
    · simpa [boundaryVertex55, boundaryPosition55, gridBoundaryVertex,
        gridBoundaryLength] using h
  have hq3omit : boundaryVertex55 q3 ∉ F := by
    dsimp [q3]; split_ifs with h
    · exact homit40.resolve_right (by simpa using h)
    · simpa [boundaryVertex55, boundaryPosition55, gridBoundaryVertex,
        gridBoundaryLength] using h
  have hQcard : Q.card = 4 := by
    rcases hq0 with hq0 | hq0 <;> rcases hq1 with hq1 | hq1 <;>
      rcases hq2 with hq2 | hq2 <;> rcases hq3 with hq3 | hq3 <;>
      simp [Q, hq0, hq1, hq2, hq3]
  have hQomit : Q ⊆ (Finset.univ : Finset (Fin 16)) \
      boundaryForcedPositions55 F := by
    intro q hq
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with hq | hq | hq | hq
    · subst q; simpa [boundaryForcedPositions55] using hq0omit
    · subst q; simpa [boundaryForcedPositions55] using hq1omit
    · subst q; simpa [boundaryForcedPositions55] using hq2omit
    · subst q; simpa [boundaryForcedPositions55] using hq3omit
  have hQodd : ∀ q ∈ Q, q.val % 2 = 1 := by
    intro q hq
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with hq | hq | hq | hq
    · rw [hq]; rcases hq0 with hq0 | hq0 <;> simp [hq0]
    · rw [hq]; rcases hq1 with hq1 | hq1 <;> simp [hq1]
    · rw [hq]; rcases hq2 with hq2 | hq2 <;> simp [hq2]
    · rw [hq]; rcases hq3 with hq3 | hq3 <;> simp [hq3]
  exact boundaryForcedRunCount55_three_le_of_four_odd_omissions F Q hacyc
    hPcard hQcard hQomit hQodd

/-- Every acyclic forced set in the `5 x 5` grid has at most eleven vertices. -/
theorem forced_five_five_card_le_eleven
    (F : Finset (GridVertex 5 5))
    (hacyc : (forcedEdgeGraph (gridGraph 5 5)
      (↑F : Set (GridVertex 5 5))).IsAcyclic) :
    F.card ≤ 11 := by
  have hle12 := forced_five_five_card_le_twelve F hacyc
  by_contra hnot
  have hcard : F.card = 12 := by omega
  rcases forced_five_five_twelve_ledger_profile F hcard hacyc with hprofile | hprofile
  · rcases hprofile.2.2.2 with hthreeCorners | hfinal
    · exact forced_five_five_twelve_boundary_three_corners_impossible F hcard hacyc
        ⟨hprofile.1, hprofile.2.1, hprofile.2.2.1,
          hthreeCorners.1, hthreeCorners.2⟩
    · have hreduce := forced_five_five_twelve_final_profile_reduction F hcard hacyc
        hfinal.1 hfinal.2 hprofile.2.2.1
      obtain ⟨hcorners, homit00, homit04, homit44, homit40,
        x, hxOutside, hxF, hxNotBoundary, hxLocation⟩ := hreduce
      have hPcard : (boundaryForcedPositions55 F).card = 11 := by
        rw [boundaryForcedPositions55_card_eq_boundary_inter, hfinal.2]
      have hrunsLower := final_profile_three_runs_lower F hacyc hPcard
        homit00 homit04 homit44 homit40
      obtain ⟨hruns, hdegree⟩ := final_profile_three_runs_and_one_attachment
        F x hxOutside hxF hxNotBoundary hxLocation hacyc hcard hprofile.2.1
        hrunsLower
      have hxCases : x = (2, 2) ∨ x = (1, 2) ∨ x = (2, 3) ∨
          x = (3, 2) ∨ x = (2, 1) := by
        rcases hxLocation with h | h
        · exact Or.inl h
        · change adjacent 5 5 (2, 2) x at h
          rcases h with ⟨hrow, hcol | hcol⟩ | ⟨hcol, hrow | hrow⟩
          · right; right; left
            apply Prod.ext <;> apply Fin.ext <;> norm_num at hrow hcol ⊢ <;> omega
          · right; right; right; right
            apply Prod.ext <;> apply Fin.ext <;> norm_num at hrow hcol ⊢ <;> omega
          · right; right; right; left
            apply Prod.ext <;> apply Fin.ext <;> norm_num at hrow hcol ⊢ <;> omega
          · right; left
            apply Prod.ext <;> apply Fin.ext <;> norm_num at hrow hcol ⊢ <;> omega
      rcases hxCases with rfl | rfl | rfl | rfl | rfl
      · have hpos : 0 < ((gridGraph 5 5).induce
            (↑F : Set (GridVertex 5 5))).degree ⟨(2, 2), hxF⟩ := by
          rw [hdegree]
          norm_num
        obtain ⟨y, hy⟩ := Finset.card_pos.mp hpos
        have hxy : (gridGraph 5 5).Adj (2, 2) y.1 := by
          simpa [SimpleGraph.mem_neighborFinset] using hy
        have hyBoundary : y.1 ∈ boundary55 := by
          by_contra hyNotBoundary
          have hyOutside : y.1 ∈ F \ boundary55 :=
            Finset.mem_sdiff.mpr ⟨y.2, hyNotBoundary⟩
          have hySingleton : y.1 ∈ ({(2, 2)} : Finset (GridVertex 5 5)) := by
            rw [← hxOutside]
            exact hyOutside
          have hyCenter : y.1 = (2, 2) := by simpa using hySingleton
          exact (gridGraph 5 5).ne_of_adj hxy hyCenter.symm
        change adjacent 5 5 (2, 2) y.1 at hxy
        simp only [boundary55, Finset.mem_filter, Finset.mem_univ, true_and] at hyBoundary
        rcases hxy with ⟨hr, hc | hc⟩ | ⟨hc, hr | hr⟩ <;>
          rcases hyBoundary with h | h | h | h <;> norm_num at hr hc h <;> omega
      · exact final_profile_attachment_top_impossible F hxOutside hxF hacyc hPcard
          hcorners homit00 homit04 homit44 homit40 hruns hdegree
      · exact final_profile_attachment_right_impossible F hxOutside hxF hacyc hPcard
          hcorners homit00 homit40 hruns hdegree
      · exact final_profile_attachment_bottom_impossible F hxOutside hxF hacyc hPcard
          hcorners homit00 homit04 hruns hdegree
      · exact final_profile_attachment_left_impossible F hxOutside hxF hacyc hPcard
          hcorners homit04 homit44 hruns hdegree
  · exact forced_five_five_twelve_boundary_four_corners_impossible F
      hprofile.2.2.2 hprofile.2.2.1 hacyc

/-- The exact maximum number of preserved vertices in the `5 x 5` grid. -/
theorem maxPreserved_five_five : maxPreserved 5 5 = 11 := by
  apply Nat.le_antisymm
  · apply maxPreserved_le_of_forall
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
    simpa [F, numPreserved] using forced_five_five_card_le_eleven F hacyc
  · exact eleven_le_maxPreserved_five_five

/-- The straight-component reduction supplies two of the six checkerboard
component credits sought by the unfinished `5 x 5` analysis.  The remaining
four credits are the `12`-vertex perimeter obstruction isolated by
`forced_five_five_twelve_ledger_profile`. -/
theorem five_checkerboard_component_two_credit
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

end GridGraphs
