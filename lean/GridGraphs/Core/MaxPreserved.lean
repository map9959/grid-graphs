import GridGraphs.Core.Spanning

/-!
# The maximum number of preserved grid vertices

This file packages the finite optimization problem over spanning subtrees of a
grid.  The score uses a fixed classical adjacency decision procedure, so the
resulting maximum does not carry a `DecidableRel` argument.
-/

namespace GridGraphs

open Finset SimpleGraph

/-- The finite collection of spanning subtrees of the `m x n` grid. -/
noncomputable def spanningSubtrees (m n : Nat) :
    Finset (SimpleGraph (GridVertex m n)) := by
  classical
  exact Finset.univ.filter (IsSpanningSubtree (gridGraph m n))

@[simp] theorem mem_spanningSubtrees {m n : Nat}
    {T : SimpleGraph (GridVertex m n)} :
    T ∈ spanningSubtrees m n ↔ IsSpanningSubtree (gridGraph m n) T := by
  classical
  simp [spanningSubtrees]

/-- The preservation score computed with a fixed classical decision procedure. -/
noncomputable def preservedScore (m n : Nat)
    (T : SimpleGraph (GridVertex m n)) : Nat := by
  classical
  exact numPreserved m n T

/-- The preservation count is independent of the adjacency decision procedure. -/
theorem numPreserved_eq_preservedScore (m n : Nat)
    (T : SimpleGraph (GridVertex m n)) [inst : DecidableRel T.Adj] :
    numPreserved m n T = preservedScore m n T := by
  classical
  unfold preservedScore
  have hinst : inst = Classical.decRel T.Adj := Subsingleton.elim _ _
  subst hinst
  rfl

/-- Symmetric form of `numPreserved_eq_preservedScore`. -/
theorem preservedScore_eq_numPreserved (m n : Nat)
    (T : SimpleGraph (GridVertex m n)) [DecidableRel T.Adj] :
    preservedScore m n T = numPreserved m n T :=
  (numPreserved_eq_preservedScore m n T).symm

/-- Maximum preservation score over all spanning subtrees.  It is `0` when
the finite search space is empty. -/
noncomputable def maxPreserved (m n : Nat) : Nat :=
  (spanningSubtrees m n).sup (preservedScore m n)

/-- Every spanning subtree's canonical score is at most `maxPreserved`. -/
theorem preservedScore_le_maxPreserved {m n : Nat}
    {T : SimpleGraph (GridVertex m n)}
    (hT : IsSpanningSubtree (gridGraph m n) T) :
    preservedScore m n T ≤ maxPreserved m n := by
  exact Finset.le_sup (f := preservedScore m n) (mem_spanningSubtrees.mpr hT)

/-- Every spanning subtree has at most `maxPreserved` preserved vertices,
regardless of the supplied adjacency decision procedure. -/
theorem numPreserved_le_maxPreserved {m n : Nat}
    {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph m n) T) :
    numPreserved m n T ≤ maxPreserved m n := by
  rw [numPreserved_eq_preservedScore]
  exact preservedScore_le_maxPreserved hT

/-- A concrete spanning-subtree witness gives a lower bound on the maximum. -/
theorem le_maxPreserved_of_witness {m n k : Nat}
    {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph m n) T)
    (hk : k ≤ numPreserved m n T) :
    k ≤ maxPreserved m n :=
  hk.trans (numPreserved_le_maxPreserved hT)

/-- Canonical-score form of the universal upper-bound principle. -/
theorem maxPreserved_le {m n k : Nat}
    (h : ∀ T : SimpleGraph (GridVertex m n),
      IsSpanningSubtree (gridGraph m n) T → preservedScore m n T ≤ k) :
    maxPreserved m n ≤ k := by
  apply Finset.sup_le
  intro T hT
  exact h T (mem_spanningSubtrees.mp hT)

/-- Universal upper bounds for spanning-subtree scores bound the maximum. -/
theorem maxPreserved_le_of_forall {m n k : Nat}
    (h : ∀ (T : SimpleGraph (GridVertex m n)) [DecidableRel T.Adj],
      IsSpanningSubtree (gridGraph m n) T → numPreserved m n T ≤ k) :
    maxPreserved m n ≤ k := by
  classical
  apply maxPreserved_le
  intro T hT
  rw [← numPreserved_eq_preservedScore]
  exact h T hT

/-- The spanning-subtree search space is nonempty for a nonempty grid. -/
theorem spanningSubtrees_nonempty {m n : Nat} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (spanningSubtrees m n).Nonempty := by
  obtain ⟨T, hTG, htree⟩ := (gridGraph_connected hm hn).exists_isTree_le
  exact ⟨T, mem_spanningSubtrees.mpr ⟨hTG, htree⟩⟩

/-- Canonical-score form of existence of a maximizing spanning subtree. -/
theorem exists_maxPreserved {m n : Nat} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ∃ T : SimpleGraph (GridVertex m n),
      IsSpanningSubtree (gridGraph m n) T ∧
        preservedScore m n T = maxPreserved m n := by
  obtain ⟨T, hTmem, hscore⟩ :=
    Finset.exists_mem_eq_sup (spanningSubtrees m n)
      (spanningSubtrees_nonempty hm hn) (preservedScore m n)
  exact ⟨T, mem_spanningSubtrees.mp hTmem, hscore.symm⟩

/-- On a nonempty grid, some spanning subtree attains `maxPreserved`. -/
theorem exists_spanningSubtree_numPreserved_eq_maxPreserved
    {m n : Nat} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ∃ (T : SimpleGraph (GridVertex m n)) (_ : DecidableRel T.Adj),
      IsSpanningSubtree (gridGraph m n) T ∧
        numPreserved m n T = maxPreserved m n := by
  classical
  obtain ⟨T, hT, hscore⟩ := exists_maxPreserved hm hn
  refine ⟨T, Classical.decRel T.Adj, hT, ?_⟩
  rw [numPreserved_eq_preservedScore]
  exact hscore

/-- The operational maximum obeys the basic deficiency upper bound. -/
theorem maxPreserved_le_basicUB {m n : Nat} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    maxPreserved m n ≤ basicUB m n := by
  apply maxPreserved_le_of_forall
  intro T _ hT
  exact preserved_le_basicUB hm hn hT

/-- The operational maximum obeys the refined deficiency upper bound. -/
theorem maxPreserved_le_refinedUB {m n : Nat} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    maxPreserved m n ≤ refinedUB m n := by
  apply maxPreserved_le_of_forall
  intro T _ hT
  exact preserved_le_refinedUB hm hn hT

end GridGraphs
