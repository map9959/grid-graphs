import GridGraphs.MaxPreserved

namespace GridGraphs

open Finset SimpleGraph

/-- A preservation count cannot exceed the number of grid vertices. -/
private lemma numPreserved_le_card {m n : Nat}
    (T : SimpleGraph (GridVertex m n)) [DecidableRel T.Adj] :
    numPreserved m n T ≤ m * n := by
  unfold numPreserved
  calc
    ((univ : Finset (GridVertex m n)).filter
        (fun v => isPreserved m n T v)).card
        ≤ (univ : Finset (GridVertex m n)).card := card_filter_le _ _
    _ = m * n := by simp [GridVertex, Fintype.card_prod]

/-- The unique graph on the `1 × 1` grid is an explicit spanning tree. -/
private lemma bot_spanningSubtree_11 :
    IsSpanningSubtree (gridGraph 1 1)
      (⊥ : SimpleGraph (GridVertex 1 1)) := by
  constructor
  · exact bot_le
  · rw [SimpleGraph.isTree_iff_connected_and_card]
    constructor
    · rw [SimpleGraph.connected_iff]
      constructor
      · intro v w
        have hvw : v = w := by
          apply Prod.ext <;> apply Fin.ext <;> omega
        subst w
        exact Reachable.refl v
      · exact ⟨((⟨0, by omega⟩, ⟨0, by omega⟩) : GridVertex 1 1)⟩
    · simp [Nat.card_eq_fintype_card, GridVertex, Fintype.card_prod]

/-- The three-edge path obtained by deleting the bottom edge of the square. -/
private def smallTree22 : SimpleGraph (GridVertex 2 2) where
  Adj v w := (gridGraph 2 2).Adj v w ∧ (v.1.val = 0 ∨ w.1.val = 0)
  symm.symm := by
    rintro v w ⟨hvw, hvwTop⟩
    exact ⟨hvw.symm, hvwTop.symm⟩
  loopless.irrefl := by
    rintro v ⟨hvv, _⟩
    exact (gridGraph 2 2).irrefl hvv

private instance : DecidableRel smallTree22.Adj := by
  intro v w
  change Decidable ((gridGraph 2 2).Adj v w ∧ (v.1.val = 0 ∨ w.1.val = 0))
  infer_instance

private lemma smallTree22_le : smallTree22 ≤ gridGraph 2 2 :=
  fun _ _ h => h.1

private lemma smallTree22_degree (v : GridVertex 2 2) :
    smallTree22.degree v = if v.1.val = 0 then 2 else 1 := by
  rcases v with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> decide

private lemma smallTree22_connected : smallTree22.Connected := by
  rw [SimpleGraph.connected_iff]
  constructor
  · let o : GridVertex 2 2 := (⟨0, by omega⟩, ⟨0, by omega⟩)
    have hreach (v : GridVertex 2 2) : smallTree22.Reachable o v := by
      rcases v with ⟨i, j⟩
      fin_cases i <;> fin_cases j
      · exact Reachable.refl o
      · exact (show smallTree22.Adj o
          (⟨0, by omega⟩, ⟨1, by omega⟩) by decide).reachable
      · exact (show smallTree22.Adj o
          (⟨1, by omega⟩, ⟨0, by omega⟩) by decide).reachable
      · exact (show smallTree22.Adj o
          (⟨0, by omega⟩, ⟨1, by omega⟩) by decide).reachable.trans
          (show smallTree22.Adj
            (⟨0, by omega⟩, ⟨1, by omega⟩)
            (⟨1, by omega⟩, ⟨1, by omega⟩) by decide).reachable
    intro v w
    exact (hreach v).symm.trans (hreach w)
  · exact ⟨((⟨0, by omega⟩, ⟨0, by omega⟩) : GridVertex 2 2)⟩

private lemma smallTree22_edge_card : smallTree22.edgeFinset.card = 3 := by
  have hdegrees := smallTree22.sum_degrees_eq_twice_card_edges
  have hsum : ∑ v : GridVertex 2 2, smallTree22.degree v = 6 := by
    rw [show (∑ v : GridVertex 2 2, smallTree22.degree v) =
        ∑ i : Fin 2, ∑ j : Fin 2, smallTree22.degree (i, j) from
      Fintype.sum_prod_type' (fun i j => smallTree22.degree (i, j))]
    simp_rw [smallTree22_degree]
    decide
  rw [hsum] at hdegrees
  omega

private lemma smallTree22_spanningSubtree :
    IsSpanningSubtree (gridGraph 2 2) smallTree22 := by
  refine ⟨smallTree22_le, ?_⟩
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨smallTree22_connected, ?_⟩
  calc
    Nat.card smallTree22.edgeSet + 1 = smallTree22.edgeFinset.card + 1 := by
      rw [Nat.card_eq_fintype_card, smallTree22.edgeFinset_card]
    _ = 4 := by rw [smallTree22_edge_card]
    _ = Nat.card (GridVertex 2 2) := by
      rw [Nat.card_eq_fintype_card]
      simp [GridVertex, Fintype.card_prod]

private lemma smallTree22_numPreserved : numPreserved 2 2 smallTree22 = 2 := by
  decide

/-- On the square, the degree sum of a spanning tree permits at most two
vertices to retain their ambient degree two. -/
private lemma numPreserved_22_le_two
    (T : SimpleGraph (GridVertex 2 2)) [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph 2 2) T) :
    numPreserved 2 2 T ≤ 2 := by
  let P := (univ : Finset (GridVertex 2 2)).filter
    (fun v => isPreserved 2 2 T v)
  let U := (univ : Finset (GridVertex 2 2)).filter
    (fun v => ¬isPreserved 2 2 T v)
  have hcard : P.card + U.card = 4 := by
    simpa [P, U, GridVertex, Fintype.card_prod] using
      card_filter_add_card_filter_not
        (s := (univ : Finset (GridVertex 2 2)))
        (p := fun v => isPreserved 2 2 T v)
  have hdegree_grid (v : GridVertex 2 2) : (gridGraph 2 2).degree v = 2 := by
    rcases v with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;>
      apply gridGraph_degree_corner (by omega) (by omega) <;> simp
  have hpositive (v : GridVertex 2 2) : 1 ≤ T.degree v :=
    tree_degree_pos (by norm_num) hT v
  have hsum : ∑ v : GridVertex 2 2, T.degree v = 6 := by
    simpa [GridVertex, Fintype.card_prod] using hT.sum_degrees
  have hsplit : ∑ v : GridVertex 2 2, T.degree v =
      (∑ v ∈ P, T.degree v) + ∑ v ∈ U, T.degree v := by
    rw [show (univ : Finset (GridVertex 2 2)) = P ∪ U by
      ext v
      simp only [P, U, mem_univ, mem_union, mem_filter, true_and]
      exact iff_of_true trivial (em (isPreserved 2 2 T v))]
    apply sum_union
    rw [Finset.disjoint_left]
    intro v hvP hvU
    simp only [P, U, mem_filter] at hvP hvU
    exact hvU.2 hvP.2
  have hPsum : 2 * P.card ≤ ∑ v ∈ P, T.degree v := by
    calc
      2 * P.card = ∑ _v ∈ P, 2 := by simp [mul_comm]
      _ ≤ ∑ v ∈ P, T.degree v := by
        apply sum_le_sum
        intro v hv
        simp only [P, mem_filter, mem_univ, true_and] at hv
        rw [hv, hdegree_grid]
  have hUsum : U.card ≤ ∑ v ∈ U, T.degree v := by
    calc
      U.card = ∑ _v ∈ U, 1 := by simp
      _ ≤ ∑ v ∈ U, T.degree v := by
        apply sum_le_sum
        intro v _
        exact hpositive v
  have hPdef : P.card = numPreserved 2 2 T := rfl
  omega

theorem maxPreserved_one_one : maxPreserved 1 1 = 1 := by
  apply Nat.le_antisymm
  · apply maxPreserved_le_of_forall
    intro T _ _
    exact numPreserved_le_card T
  · apply le_maxPreserved_of_witness bot_spanningSubtree_11
    have : numPreserved 1 1 (⊥ : SimpleGraph (GridVertex 1 1)) = 1 := by
      decide
    omega

theorem maxPreserved_two_two : maxPreserved 2 2 = 2 := by
  apply Nat.le_antisymm
  · apply maxPreserved_le_of_forall
    intro T _ hT
    exact numPreserved_22_le_two T hT
  · apply le_maxPreserved_of_witness smallTree22_spanningSubtree
    rw [smallTree22_numPreserved]

end GridGraphs
