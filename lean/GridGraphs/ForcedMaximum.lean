import GridGraphs.MaxPreserved

/-!
# Forced-forest form of the preservation maximum

Maximizing full-degree vertices over spanning trees is exactly the finite
extremal problem of maximizing a vertex set whose incident-edge graph is
acyclic. This removes the spanning-tree choice from both upper and lower bounds.
-/

namespace GridGraphs

open Finset SimpleGraph

/-- Vertex sets whose complete ambient incident-edge graph is acyclic. -/
noncomputable def acyclicForcedSets (m n : Nat) :
    Finset (Finset (GridVertex m n)) := by
  classical
  exact Finset.univ.filter fun F =>
    (forcedEdgeGraph (gridGraph m n)
      (↑F : Set (GridVertex m n))).IsAcyclic

@[simp] theorem mem_acyclicForcedSets {m n : Nat}
    {F : Finset (GridVertex m n)} :
    F ∈ acyclicForcedSets m n ↔
      (forcedEdgeGraph (gridGraph m n)
        (↑F : Set (GridVertex m n))).IsAcyclic := by
  classical
  simp [acyclicForcedSets]

/-- Maximum cardinality of an acyclic forced vertex set. -/
noncomputable def maxForcedAcyclic (m n : Nat) : Nat :=
  (acyclicForcedSets m n).sup Finset.card

/-- On every nonempty grid, the spanning-tree and forced-forest optimization
problems have exactly the same value. -/
theorem maxPreserved_eq_maxForcedAcyclic
    {m n : Nat} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    maxPreserved m n = maxForcedAcyclic m n := by
  classical
  apply Nat.le_antisymm
  · obtain ⟨T, _, hT, hmax⟩ :=
      exists_spanningSubtree_numPreserved_eq_maxPreserved hm hn
    let F : Finset (GridVertex m n) :=
      Finset.univ.filter fun v => isPreserved m n T v
    have hacyc : (forcedEdgeGraph (gridGraph m n)
        (↑F : Set (GridVertex m n))).IsAcyclic := by
      apply forcedEdgeGraph_isAcyclic_of_preserves hT.isAcyclic
      intro v hv
      have hvPreserved : isPreserved m n T v := by
        change v ∈ F at hv
        exact (Finset.mem_filter.mp hv).2
      exact preservesIncidentEdges_of_le_of_degree_eq
        (gridGraph m n) T hT.le v hvPreserved
    have hFmem : F ∈ acyclicForcedSets m n :=
      mem_acyclicForcedSets.mpr hacyc
    have hFcard : F.card = maxPreserved m n := by
      simpa only [F, numPreserved] using hmax
    rw [← hFcard]
    exact Finset.le_sup (f := Finset.card) hFmem
  · unfold maxForcedAcyclic
    apply Finset.sup_le
    intro F hF
    have hacyc := mem_acyclicForcedSets.mp hF
    obtain ⟨T, hTG, htree, hpreserves⟩ :=
      exists_isTree_preserving_of_forcedEdgeGraph_isAcyclic
        (G := gridGraph m n) (F := (↑F : Set (GridVertex m n)))
        (gridGraph_connected hm hn) hacyc
    apply le_maxPreserved_of_witness (T := T) ⟨hTG, htree⟩
    unfold numPreserved
    apply Finset.card_le_card
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    unfold isPreserved
    exact degree_eq_of_le_of_preservesIncidentEdges
      (gridGraph m n) T hTG v (hpreserves (by simpa using hv))

end GridGraphs
