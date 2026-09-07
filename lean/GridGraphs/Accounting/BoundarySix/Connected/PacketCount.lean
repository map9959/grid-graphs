import GridGraphs.Accounting.BoundarySix.Connected.GapDeepCorners

/-! # Two literal five-edge packets over the forced perimeter -/

namespace GridGraphs.BoundarySix.Connected

open Finset SimpleGraph CarrierLayers CarrierLayers.Annulus

attribute [local instance] Classical.propDecidable

def patchLabel {n : Nat} (v : GridVertex n n) : Bool × Bool :=
  (decide (v.1.val < 4), decide (v.2.val < 4))

/-- Six distinct physical vertices, with exactly four off-perimeter vertices. -/
structure CornerPacket {n : Nat} (H : SimpleGraph (GridVertex n n)) (l : Bool × Bool) where
  point : Fin 6 → GridVertex n n
  injective : Function.Injective point
  adj : ∀ i : Fin 5, H.Adj (point i.castSucc) (point i.succ)
  boundary : ∀ i, IsGridBoundary (point i) ↔ i = 0 ∨ i = 5
  label : ∀ i, patchLabel (point i) = l

def CornerPacket.edge {n : Nat} {H : SimpleGraph (GridVertex n n)} {l : Bool × Bool}
    (P : CornerPacket H l) (i : Fin 5) : Sym2 (GridVertex n n) :=
  s(P.point i.castSucc, P.point i.succ)

theorem CornerPacket.edge_injective {n : Nat} {H : SimpleGraph (GridVertex n n)}
    {l : Bool × Bool} (P : CornerPacket H l) : Function.Injective P.edge := by
  intro i j he
  rcases Sym2.eq_iff.mp he with ⟨h, _⟩ | ⟨h, h'⟩
  · exact Fin.ext (congrArg (Fin.val (n := 6)) (P.injective h))
  · have hi := congrArg Fin.val (P.injective h)
    have hj := congrArg Fin.val (P.injective h')
    dsimp at hi hj
    omega

theorem CornerPacket.edge_outside {n : Nat} {H : SimpleGraph (GridVertex n n)}
    {l : Bool × Bool} (P : CornerPacket H l) (i : Fin 5) :
    ∃ v ∈ P.edge i, ¬ IsGridBoundary v := by
  by_cases hi : i.val = 0
  · refine ⟨P.point i.succ, by simp [CornerPacket.edge], ?_⟩
    rw [P.boundary]
    simp only [Fin.ext_iff]
    dsimp
    omega
  · refine ⟨P.point i.castSucc, by simp [CornerPacket.edge], ?_⟩
    rw [P.boundary]
    simp only [Fin.ext_iff]
    dsimp
    omega

private theorem forest_restriction_card_lt {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hacyc : H.IsAcyclic)
    (U : Finset V) (hU : U.Nonempty) : (H.edgeFinset ∩ U.sym2).card < U.card := by
  let : Fintype U := Subtype.fintype (Membership.mem (↑U : Set V))
  let W := H.induce (↑U : Set _)
  have hmap := congrArg Finset.card (H.map_edgeFinset_induce (s := (↑U : Set _)))
  simp only [card_map, Finset.toFinset_coe] at hmap
  have hledger : W.edgeFinset.card + Fintype.card W.ConnectedComponent = U.card :=
    (hacyc.induce _).card_edgeFinset_add_card_connectedComponent.trans (Fintype.card_coe U)
  have hpos : 1 ≤ Fintype.card W.ConnectedComponent := by
    obtain ⟨v, hv⟩ := hU
    exact Fintype.card_pos_iff.mpr ⟨W.connectedComponentMk ⟨v, hv⟩⟩
  change W.edgeFinset.card = _ at hmap
  omega

/-- The two packets add ten distinct edges but at most eight vertices to a
perimeter forest missing two edges. The actual induced forest cannot contain them. -/
theorem two_corner_packets_false {n : Nat} (hn : 2 ≤ n)
    (H : SimpleGraph (GridVertex n n)) [DecidableRel H.Adj] (hacyc : H.IsAcyclic)
    (hbase : (H.edgeFinset ∩ ({v | IsGridBoundary v} : Set (GridVertex n n)).toFinset.sym2).card + 2 =
      ({v | IsGridBoundary v} : Set (GridVertex n n)).toFinset.card)
    {l m : Bool × Bool} (hlm : l ≠ m) (P : CornerPacket H l) (Q : CornerPacket H m) : False := by
  let B : Finset (GridVertex n n) := {v | IsGridBoundary v}.toFinset
  let I : Finset (Fin 6) := {1, 2, 3, 4}
  let U := B ∪ (I.image P.point ∪ I.image Q.point)
  let R := univ.image P.edge ∪ univ.image Q.edge
  let base := H.edgeFinset ∩ B.sym2
  have hI : I.card = 4 := by decide
  have hU : U.card ≤ B.card + 8 := by
    have h1 := card_image_le (s := I) (f := P.point)
    have h2 := card_image_le (s := I) (f := Q.point)
    have h3 := card_union_le (I.image P.point) (I.image Q.point)
    have h4 := card_union_le B (I.image P.point ∪ I.image Q.point)
    change U.card ≤ _ at h4
    omega
  have hdisj : Disjoint (univ.image P.edge) (univ.image Q.edge) := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨i, _, rfl⟩ := mem_image.mp he
    obtain ⟨j, _, he⟩ := mem_image.mp hf
    have hlabels := hlm
    rcases Sym2.eq_iff.mp he with ⟨h, _⟩ | ⟨h, _⟩
    · exact hlabels ((P.label _).symm.trans ((congrArg patchLabel h).symm.trans (Q.label _)))
    · exact hlabels ((P.label _).symm.trans ((congrArg patchLabel h).symm.trans (Q.label _)))
  have hR : R.card = 10 := by
    rw [card_union_of_disjoint hdisj, card_image_of_injective _ P.edge_injective,
      card_image_of_injective _ Q.edge_injective]
    simp
  have pointsP (i : Fin 6) : P.point i ∈ U := by
    by_cases hi : i = 0 ∨ i = 5
    · exact mem_union_left _ (Set.mem_toFinset.mpr ((P.boundary i).mpr hi))
    · have hiI : i ∈ I := by simp only [I, mem_insert, mem_singleton, Fin.ext_iff] at *; omega
      exact mem_union_right _ (mem_union_left _ (mem_image_of_mem _ hiI))
  have pointsQ (i : Fin 6) : Q.point i ∈ U := by
    by_cases hi : i = 0 ∨ i = 5
    · exact mem_union_left _ (Set.mem_toFinset.mpr ((Q.boundary i).mpr hi))
    · have hiI : i ∈ I := by simp only [I, mem_insert, mem_singleton, Fin.ext_iff] at *; omega
      exact mem_union_right _ (mem_union_right _ (mem_image_of_mem _ hiI))
  have hphysical {e : Sym2 (GridVertex n n)} (he : e ∈ R) :
      e ∈ H.edgeFinset ∩ U.sym2 ∧ ∃ v ∈ e, ¬ IsGridBoundary v := by
    rcases mem_union.mp he with he | he
    · obtain ⟨i, _, rfl⟩ := mem_image.mp he
      refine ⟨mem_inter.mpr ⟨by simpa [CornerPacket.edge] using P.adj i, ?_⟩, P.edge_outside i⟩
      simpa only [CornerPacket.edge, mk_mem_sym2_iff] using ⟨pointsP i.castSucc, pointsP i.succ⟩
    · obtain ⟨i, _, rfl⟩ := mem_image.mp he
      refine ⟨mem_inter.mpr ⟨by simpa [CornerPacket.edge] using Q.adj i, ?_⟩, Q.edge_outside i⟩
      simpa only [CornerPacket.edge, mk_mem_sym2_iff] using ⟨pointsQ i.castSucc, pointsQ i.succ⟩
  have hbR : Disjoint base R := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨v, hve, hv⟩ := (hphysical hf).2
    have hvB : v ∈ B := mem_sym2_iff.mp (mem_inter.mp he).2 v hve
    exact hv (by simpa only [B, Set.mem_toFinset, Set.mem_ofPred_eq] using hvB)
  have hsub : base ∪ R ⊆ H.edgeFinset ∩ U.sym2 := by
    intro e he
    rcases mem_union.mp he with he | he
    · refine mem_inter.mpr ⟨(mem_inter.mp he).1, mem_sym2_iff.mpr ?_⟩
      intro v hv
      exact mem_union_left _ (mem_sym2_iff.mp (mem_inter.mp he).2 v hv)
    · exact (hphysical he).1
  have hcount := card_le_card hsub
  rw [card_union_of_disjoint hbR, hR] at hcount
  have hforest := forest_restriction_card_lt H hacyc U
    ⟨(⟨0, by omega⟩, ⟨0, by omega⟩), mem_union_left _ (by simp [B, IsGridBoundary])⟩
  change base.card + 2 = B.card at hbase
  omega

/-- Transport the exact omitted-perimeter count to physical ambient edges. -/
theorem perimeter_base_two {n : Nat} (hn : 9 ≤ n)
    (F : Finset (GridVertex n n)) (hholes : (perimeterHoles F).card = 2) :
    ((forcedEdgeGraph (gridGraph n n) (↑F : Set _)).edgeFinset ∩
      ({v | IsGridBoundary v} : Set (GridVertex n n)).toFinset.sym2).card + 2 =
      ({v | IsGridBoundary v} : Set (GridVertex n n)).toFinset.card := by
  let H := forcedEdgeGraph (gridGraph n n) (↑F : Set _)
  let P := perimeterGraph n
  let A := forcedEdgeGraph P (↑(perimeterSelected F) : Set _)
  have he : H.induce {v | IsGridBoundary v} = A := by
    ext v w
    change (_ ∧ (v.1 ∈ F ∨ w.1 ∈ F)) ↔ (_ ∧ (v ∈ perimeterSelected F ∨ w ∈ perimeterSelected F))
    simp only [perimeterSelected, mem_filter, mem_univ, true_and]
    rfl
  have hmap := congrArg Finset.card (H.map_edgeFinset_induce (s := {v | IsGridBoundary v}))
  rw [card_map, edgeFinset_inj.mpr he] at hmap
  have hdiff := card_sdiff_add_card_eq_card
    (edgeFinset_mono (forcedEdgeGraph_le P (↑(perimeterSelected F) : Set _)))
  change (perimeterHoles F).card + A.edgeFinset.card = P.edgeFinset.card at hdiff
  have hdeg := P.sum_degrees_eq_twice_card_edges
  have hsum : (∑ v : PerimeterVertex n, P.degree v) = 2 * Fintype.card (PerimeterVertex n) := by
    simp [P, perimeter_degree (n := n) (by omega), Nat.mul_comm]
  have hB : ({v | IsGridBoundary v} : Set (GridVertex n n)).toFinset.card =
      Fintype.card (PerimeterVertex n) := by
    rw [Set.toFinset_card]
    exact Fintype.card_congr (Equiv.refl _)
  change A.edgeFinset.card = _ at hmap
  change (H.edgeFinset ∩ ({v | IsGridBoundary v} : Set (GridVertex n n)).toFinset.sym2).card + 2 = _
  omega

end GridGraphs.BoundarySix.Connected
