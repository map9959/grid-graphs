import GridGraphs.Results.SmallDiagonalExact.BoundaryFive

/-!
# The single interior attachment in the `5 x 5` grid

Deleting the interior vertex identifies the boundary-run forest. Its ledger
forces three runs and one attachment; auxiliary lemmas prepare cycle exclusions.
-/

namespace GridGraphs.SmallDiagonalProof

open Finset SimpleGraph

set_option maxHeartbeats 4000000 in
lemma final_profile_three_runs_and_one_attachment
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
        simp [boundaryForcedPositions55, hiVertex]
      have hjP : j ∈ boundaryForcedPositions55 F := by
        simp [boundaryForcedPositions55, hjVertex]
      let iP : (↑(boundaryForcedPositions55 F) : Set (Fin 16)) := ⟨i, hiP⟩
      let jP : (↑(boundaryForcedPositions55 F) : Set (Fin 16)) := ⟨j, hjP⟩
      have hijCycle : (cycleGraph 16).Adj i j := by
        apply gridBoundaryCycleHom55_reflects_adj
        rw [hiVertex, hjVertex]
        exact huvH
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
      all_goals norm_num at hr hc h; omega
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
  let : Fintype B.ConnectedComponent := SetLike.instFintype
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
          simpa [boundary55, IsGridBoundary, boundaryVertex55] using
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
        · simpa [mem_boundaryForcedPositions55, boundaryVertex55,
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

lemma gridVertex55_eq_iff_vals (u v : GridVertex 5 5) :
    u = v ↔ (u.1.val = v.1.val ∧ u.2.val = v.2.val) := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨hr, hc⟩
    apply Prod.ext <;> apply Fin.ext
    · exact hr
    · exact hc

lemma odd_boundary_position_forced_of_three_runs
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

lemma attachment_boundary_neighbor_forced
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

lemma corner_boundary_positions_forced (F : Finset (GridVertex 5 5))
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
    simp only [mem_boundaryForcedPositions55, boundaryVertex55, boundaryPosition55, gridBoundaryVertex,
      gridBoundaryLength] <;> apply hcorners <;> simp [corners55]

lemma forced_six_cycle_false
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

lemma final_profile_three_runs_lower
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

end GridGraphs.SmallDiagonalProof
