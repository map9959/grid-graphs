import GridGraphs.MaxPreserved
import GridGraphs.ResidueOneDual
import GridGraphs.CotreeWaste

/-!
# Maximum preservation on residue-one squares

The residue-one construction supplies the lower bound for squares of side
`3k + 1`. A universal cotree incidence-waste bound supplies the matching
upper bound.
-/

namespace GridGraphs

open Finset SimpleGraph

variable {V : Type*} [Fintype V]

/-- A subgraph which contains every ambient edge incident to `v` has the same
degree as the ambient graph at `v`. -/
theorem degree_eq_of_le_of_preservesIncidentEdges (G T : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel T.Adj] (hTG : T ≤ G) (v : V)
    (hv : preservesIncidentEdges G T v) :
    T.degree v = G.degree v := by
  apply congrArg Finset.card
  ext w
  simp only [SimpleGraph.mem_neighborFinset]
  exact ⟨fun h => hTG h, fun h => hv h⟩

/-- The residue-one construction preserves at least `3k² + 5k` vertices. -/
theorem residueOne_le_maxPreserved (k : Nat) (hk : 1 ≤ k) :
    3 * k ^ 2 + 5 * k ≤ maxPreserved (3 * k + 1) (3 * k + 1) := by
  classical
  obtain ⟨T, hTG, htree, hpreserves⟩ :=
    exists_isTree_preserving_compl_uResidueOne k hk
  apply le_maxPreserved_of_witness ⟨hTG, htree⟩
  have hsubset :
      (Finset.univ \ uResidueOne k) ⊆
        (Finset.univ : Finset (GridVertex (3 * k + 1) (3 * k + 1))).filter
          (fun v => isPreserved (3 * k + 1) (3 * k + 1) T v) := by
    intro v hv
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    unfold isPreserved
    apply degree_eq_of_le_of_preservesIncidentEdges
      (gridGraph (3 * k + 1) (3 * k + 1)) T hTG
    exact hpreserves (by simpa using hv)
  unfold numPreserved
  have hcard := Finset.card_le_card hsubset
  rw [Finset.card_sdiff, Finset.inter_univ, uResidueOne_card k hk] at hcard
  simp only [Finset.card_univ] at hcard
  have hgridcard :
      Fintype.card (GridVertex (3 * k + 1) (3 * k + 1)) =
        (3 * k + 1) * (3 * k + 1) := by
    unfold GridVertex
    simp [Fintype.card_prod]
  rw [hgridcard] at hcard
  have htotal :
      (3 * k + 1) * (3 * k + 1) =
        (6 * k ^ 2 + k + 1) + (3 * k ^ 2 + 5 * k) := by
    ring
  rw [htotal] at hcard
  omega

/-- A universal diagonal cotree-waste bound transfers directly to the
corresponding bound on the operational maximum. -/
theorem maxPreserved_bound_of_forall_incidenceWaste_ge {n : Nat} (hn : 2 ≤ n)
    (hwaste : ∀ (T : SimpleGraph (GridVertex n n)) [DecidableRel T.Adj],
      IsSpanningSubtree (gridGraph n n) T →
        n + 2 ≤ incidenceWaste (gridGraph n n \ T)) :
    3 * maxPreserved n n + 4 ≤ n * n + 3 * n := by
  obtain ⟨T, _, hT, hmax⟩ :=
    exists_spanningSubtree_numPreserved_eq_maxPreserved (by omega : 1 ≤ n)
      (by omega : 1 ≤ n)
  rw [← hmax]
  exact (diagonal_cotree_incidenceWaste_ge_iff_preserved_bound hn hT).mp
    (hwaste T hT)

/-- The residue-one lower bound is exact if every spanning subtree of the
square satisfies the conjectural cotree incidence-waste bound. -/
theorem maxPreserved_residueOne_eq_of_forall_incidenceWaste_ge
    (k : Nat) (hk : 1 ≤ k)
    (hwaste : ∀
      (T : SimpleGraph
        (GridVertex (3 * k + 1) (3 * k + 1))) [DecidableRel T.Adj],
      IsSpanningSubtree
          (gridGraph (3 * k + 1) (3 * k + 1)) T →
        (3 * k + 1) + 2 ≤
          incidenceWaste (gridGraph (3 * k + 1) (3 * k + 1) \ T)) :
    maxPreserved (3 * k + 1) (3 * k + 1) = 3 * k ^ 2 + 5 * k := by
  apply Nat.le_antisymm
  · have h := maxPreserved_bound_of_forall_incidenceWaste_ge
      (n := 3 * k + 1) (by omega) hwaste
    have htotal :
        (3 * k + 1) * (3 * k + 1) + 3 * (3 * k + 1) =
          3 * (3 * k ^ 2 + 5 * k) + 4 := by
      ring
    rw [htotal] at h
    omega
  · exact residueOne_le_maxPreserved k hk

end GridGraphs
