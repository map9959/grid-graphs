import GridGraphs.Accounting.CarrierLayers.Annulus.Rods

/-! # Full deep rods consume annulus forest components

Restrict the physical forced forest to the annulus and the deep vertices of
full carriers. Count disjoint longitudinal edge packets in this restriction.
Additional lateral attachments are allowed; only an edge lower bound is used.
-/

namespace GridGraphs.CarrierLayers.Annulus

open Finset SimpleGraph

attribute [local instance] Classical.propDecidable

private theorem forest_packet_count {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hacyc : H.IsAcyclic)
    (U : Finset V) (hU : U.Nonempty) (a b c N M : Nat)
    (hcard : U.card ≤ a + N * M) (hbase : b + c = a)
    (hedges : b + (N + 1) * M ≤ (H.edgeFinset ∩ U.sym2).card) :
    M + 1 ≤ c := by
  let : Fintype U := Subtype.fintype (Membership.mem (↑U : Set V))
  let W := H.induce (↑U : Set V)
  have hW : W.IsAcyclic := hacyc.induce _
  have hmap := congrArg Finset.card (H.map_edgeFinset_induce (s := (↑U : Set V)))
  simp only [card_map, Finset.toFinset_coe] at hmap
  have he : b + (N + 1) * M ≤ W.edgeFinset.card := hedges.trans_eq hmap.symm
  have hf : W.edgeFinset.card + Fintype.card W.ConnectedComponent = U.card := by
    exact hW.card_edgeFinset_add_card_connectedComponent.trans (Fintype.card_coe U)
  have hc : 1 ≤ Fintype.card W.ConnectedComponent := by
    obtain ⟨v, hv⟩ := hU
    exact Fintype.card_pos_iff.mpr ⟨W.connectedComponentMk ⟨v, hv⟩⟩
  have hbound : b + (N + 1) * M + 1 ≤ a + N * M :=
    (Nat.add_le_add he hc).trans (hf.le.trans hcard)
  rw [Nat.add_mul, one_mul] at hbound
  omega

/-- Every full deep carrier uses one of the available annulus component joins.
This is a physical forest edge count, not a contact-graph assumption. -/
theorem fullCarriers_card_add_one_le_components {n : Nat} (hn : 5 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic) :
    (fullCarriers F).card + 1 ≤ Fintype.card
      (forcedEdgeGraph (graph n) (↑(selected F) : Set _)).ConnectedComponent := by
  let H := forcedEdgeGraph (gridGraph n n) (↑F : Set _)
  let A : Finset (GridVertex n n) := {v | Mem v}.toFinset
  let Q := fullCarriers F
  have hex (C : Q) := full_axis_exists hn F hacyc C.1 C.2
  choose a ha using hex
  let P (C : Q) : Finset (Sym2 (GridVertex n n)) := univ.image ((a C).edge hn)
  let R := univ.biUnion P
  let U := A ∪ univ.biUnion (fun C : Q => deepVertices F C.1)
  let base := H.edgeFinset ∩ A.sym2
  have hphysical (C : Q) {e : Sym2 (GridVertex n n)} (he : e ∈ P C) :
      e ∈ H.edgeFinset ∧ (∃ v ∈ e, v ∈ deepVertices F C.1) ∧
        (∀ v ∈ e, Mem v ∨ v ∈ deepVertices F C.1) := by
    obtain ⟨j, _, rfl⟩ := mem_image.mp he
    exact Axis.edge_physical hn F C.1 (a C) (ha C) j
  have hPcard (C : Q) : (P C).card = n - 3 := by
    change (univ.image ((a C).edge hn)).card = n - 3
    rw [card_image_of_injective _ ((a C).edge_injective hn)]
    simp
  have hPdisjoint (C D : Q) (hCD : C ≠ D) : Disjoint (P C) (P D) := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨v, hve, hvC⟩ := (hphysical C he).2.1
    have hvA := ((mem_deepVertices hn F C.1 v).mp hvC).choose_spec.2
    have hvD := ((hphysical D hf).2.2 v hve).resolve_left hvA
    exact Finset.disjoint_left.mp (deepVertices_disjoint hn F
      (fun h => hCD (Subtype.ext h))) hvC hvD
  have hRcard : R.card = (n - 3) * Q.card := by
    change (univ.biUnion P).card = _
    rw [card_biUnion (by intro C _ D _ hCD; exact hPdisjoint C D hCD)]
    simp only [hPcard, sum_const, card_univ, Fintype.card_coe, smul_eq_mul]
    exact Nat.mul_comm _ _
  have hbaseR : Disjoint base R := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨C, _, hC⟩ := mem_biUnion.mp hf
    obtain ⟨v, hve, hvC⟩ := (hphysical C hC).2.1
    have hvA := mem_sym2_iff.mp (mem_inter.mp he).2 v hve
    have hvAmem : Mem v := by simpa only [A, Set.mem_toFinset, Set.mem_ofPred_eq] using hvA
    exact ((mem_deepVertices hn F C.1 v).mp hvC).choose_spec.2
      hvAmem
  have hUcard : U.card ≤ A.card + (n - 4) * Q.card := by
    have hCcard (C : Q) : (deepVertices F C.1).card = n - 4 :=
      (mem_filter.mp C.2).2
    calc
      U.card ≤ A.card + (univ.biUnion (fun C : Q => deepVertices F C.1)).card :=
        card_union_le _ _
      _ ≤ A.card + ∑ C : Q, (deepVertices F C.1).card :=
        Nat.add_le_add_left card_biUnion_le _
      _ = A.card + (n - 4) * Q.card := by simp [hCcard, Nat.mul_comm]
  have hsubset : base ∪ R ⊆ H.edgeFinset ∩ U.sym2 := by
    intro e he
    rcases mem_union.mp he with he | he
    · refine mem_inter.mpr ⟨(mem_inter.mp he).1, mem_sym2_iff.mpr ?_⟩
      intro v hv
      exact mem_union_left _ (mem_sym2_iff.mp (mem_inter.mp he).2 v hv)
    · obtain ⟨C, _, hC⟩ := mem_biUnion.mp he
      refine mem_inter.mpr ⟨(hphysical C hC).1, mem_sym2_iff.mpr ?_⟩
      intro v hv
      rcases (hphysical C hC).2.2 v hv with hv | hv
      · exact mem_union_left _ (Set.mem_toFinset.mpr hv)
      · exact mem_union_right _ (mem_biUnion.mpr ⟨C, mem_univ _, hv⟩)
  have hE := card_le_card hsubset
  rw [card_union_of_disjoint hbaseR, hRcard] at hE
  have hbase_graph : H.induce {v | Mem v} =
      forcedEdgeGraph (graph n) (↑(selected F) : Set _) := by
    ext v w
    change (_ ∧ (v.1 ∈ F ∨ w.1 ∈ F)) ↔
      (_ ∧ (v ∈ selected F ∨ w ∈ selected F))
    simp only [selected, mem_filter, mem_univ, true_and]
    rfl
  have hbase_card := congrArg Finset.card
    (H.map_edgeFinset_induce (s := {v | Mem v}))
  rw [card_map, edgeFinset_inj.mpr hbase_graph] at hbase_card
  change (forcedEdgeGraph (graph n) (↑(selected F) : Set _)).edgeFinset.card =
    base.card at hbase_card
  have hbase_ledger := forcedEdgeGraph_forest_ledger (graph n) (selected F)
    (selected_isAcyclic F hacyc)
  rw [hbase_card] at hbase_ledger
  have hAcard : A.card = Fintype.card (Vertex n) := Set.toFinset_card _
  rw [← hAcard] at hbase_ledger
  have hnonempty : U.Nonempty := by
    refine ⟨(⟨0, by omega⟩, ⟨0, by omega⟩), mem_union_left _ ?_⟩
    apply Set.mem_toFinset.mpr
    exact Or.inl (by change 0 < 2; omega)
  have hwidth : n - 3 = (n - 4) + 1 := by omega
  rw [hwidth] at hE
  exact forest_packet_count H hacyc U hnonempty A.card base.card _ (n - 4) Q.card
    hUcard hbase_ledger hE

end GridGraphs.CarrierLayers.Annulus
