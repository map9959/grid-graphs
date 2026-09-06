import GridGraphs.Surgery.ThreeFrameSurgery

/-!
# Reverse frame insertion

A reverse frame embeds a forced set from a smaller grid into a larger grid and
then lists the remaining forced vertices in a specified order.  This interface
refactors supplied acyclicity into the existing uniform sequential-insertion
criterion; it does not itself provide an independent local acyclicity proof.
No spanning tree or construction certificate occurs in the interface.
-/

namespace GridGraphs

open Finset SimpleGraph

/-- Data sufficient for a reverse forced-forest step.  `coreAcyclic` includes
the extra large-grid edges incident to the embedded old forced vertices; this
is stronger than acyclicity of the old forced graph itself. -/
structure ReverseFrameTemplate (p q m n : Nat)
    (oldForced : Finset (GridVertex p q))
    (newForced : Finset (GridVertex m n)) (gain : Nat) where
  embedding : GridVertex p q ↪ GridVertex m n
  coreAcyclic :
    (forcedEdgeGraph (gridGraph m n)
      (↑(oldForced.image embedding) : Set (GridVertex m n))).IsAcyclic
  frameOrder : List (GridVertex m n)
  frame_nodup : frameOrder.Nodup
  frame_disjoint : ∀ v ∈ frameOrder, v ∉ oldForced.image embedding
  frame_card : frameOrder.length = gain
  covers : oldForced.image embedding ∪ frameOrder.toFinset = newForced
  sequential : SequentiallyInsertable (gridGraph m n)
    (↑(oldForced.image embedding) : Set (GridVertex m n)) frameOrder

namespace ReverseFrameTemplate

/-- Reassemble acyclicity of the complete new forced set from the template's
stored core acyclicity and sequential-insertion condition.  This is an
application of the existing uniform equivalence, not a new local proof. -/
theorem newForced_isAcyclic {p q m n : Nat}
    {oldForced : Finset (GridVertex p q)}
    {newForced : Finset (GridVertex m n)} {gain : Nat}
    (R : ReverseFrameTemplate p q m n oldForced newForced gain) :
    (forcedEdgeGraph (gridGraph m n)
      (↑newForced : Set (GridVertex m n))).IsAcyclic := by
  rw [← R.covers]
  simpa only [Finset.coe_union] using
    (forcedEdgeGraph_union_list_isAcyclic_iff_sequentiallyInsertable
    (gridGraph m n) (↑(oldForced.image R.embedding) : Set (GridVertex m n))
    R.frameOrder R.frame_nodup R.frame_disjoint R.coreAcyclic).2 R.sequential

/-- Reverse insertion adds exactly `gain` forced vertices. -/
theorem card_newForced {p q m n : Nat}
    {oldForced : Finset (GridVertex p q)}
    {newForced : Finset (GridVertex m n)} {gain : Nat}
    (R : ReverseFrameTemplate p q m n oldForced newForced gain) :
    newForced.card = oldForced.card + gain := by
  rw [← R.covers, Finset.card_union_of_disjoint]
  · rw [Finset.card_image_of_injective _ R.embedding.injective,
      List.toFinset_card_of_nodup R.frame_nodup, R.frame_card]
  · rw [Finset.disjoint_left]
    intro v hvold hvframe
    exact R.frame_disjoint v (by simpa using hvframe) hvold

/-- The new forced set supplied by a reverse frame is a witness for the
large-grid forced-acyclic maximum. -/
theorem card_newForced_le_maxForcedAcyclic {p q m n : Nat}
    {oldForced : Finset (GridVertex p q)}
    {newForced : Finset (GridVertex m n)} {gain : Nat}
    (R : ReverseFrameTemplate p q m n oldForced newForced gain) :
    newForced.card ≤ maxForcedAcyclic m n := by
  apply Finset.le_sup (f := Finset.card)
  exact mem_acyclicForcedSets.mpr R.newForced_isAcyclic

/-- On a nonempty target grid, the reverse-frame construction also bounds the
operational preservation maximum. -/
theorem card_newForced_le_maxPreserved {p q m n : Nat}
    {oldForced : Finset (GridVertex p q)}
    {newForced : Finset (GridVertex m n)} {gain : Nat}
    (R : ReverseFrameTemplate p q m n oldForced newForced gain)
    (hm : 1 ≤ m) (hn : 1 ≤ n) :
    newForced.card ≤ maxPreserved m n := by
  rw [maxPreserved_eq_maxForcedAcyclic hm hn]
  exact R.card_newForced_le_maxForcedAcyclic

/-- A reverse frame gives a genuine lower recurrence when the specified old
forced set is known to attain the old forced-acyclic maximum. -/
theorem maxForcedAcyclic_add_gain_le_maxForcedAcyclic_of_card_oldForced_eq
    {p q m n : Nat} {oldForced : Finset (GridVertex p q)}
    {newForced : Finset (GridVertex m n)} {gain : Nat}
    (R : ReverseFrameTemplate p q m n oldForced newForced gain)
    (hOld : oldForced.card = maxForcedAcyclic p q) :
    maxForcedAcyclic p q + gain ≤ maxForcedAcyclic m n := by
  rw [← hOld, ← R.card_newForced]
  exact R.card_newForced_le_maxForcedAcyclic

/-- Preservation-maximum form of the conditional lower recurrence.  Positivity
is needed only to identify the two finite optimization formulations. -/
theorem maxPreserved_add_gain_le_maxPreserved_of_card_oldForced_eq
    {p q m n : Nat} {oldForced : Finset (GridVertex p q)}
    {newForced : Finset (GridVertex m n)} {gain : Nat}
    (R : ReverseFrameTemplate p q m n oldForced newForced gain)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hOld : oldForced.card = maxForcedAcyclic p q) :
    maxPreserved p q + gain ≤ maxPreserved m n := by
  rw [maxPreserved_eq_maxForcedAcyclic hp hq,
    maxPreserved_eq_maxForcedAcyclic hm hn]
  exact R.maxForcedAcyclic_add_gain_le_maxForcedAcyclic_of_card_oldForced_eq hOld

end ReverseFrameTemplate

end GridGraphs
