import GridGraphs.ResidueTwoWasteEqualityConsequences

/-!
# The remaining residue-two equality obstruction

The proposition below is deliberately stated at the forced-forest/component
level.  It is the one global geometric lemma still needed to exclude equality;
it is not assumed here and no theorem is derived from it.  This avoids
repackaging the desired waste bound as a hidden hypothesis.
-/

namespace GridGraphs

open Finset SimpleGraph

/-- The exact missing structural contradiction.  A residue-two support of the
equality cardinality should not simultaneously have an acyclic forced
complement and the tight boundary-attachment charge.  Unlike the original
statement, this formulation mentions no spanning tree and no incidence waste. -/
def ResidueTwoTightAttachmentContradiction : Prop :=
  ∀ (k : Nat), 1 ≤ k →
    ∀ U : Finset (GridVertex (3 * k + 2) (3 * k + 2)),
      U.card = 6 * k ^ 2 + 5 * k + 2 →
      (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
        (↑((Finset.univ : Finset (GridVertex (3 * k + 2) (3 * k + 2))) \ U) :
          Set (GridVertex (3 * k + 2) (3 * k + 2)))).IsAcyclic →
      residueTwoAttachmentCharge U ≠ 3 * k + 6

/-- A hypothetical waste equality produces precisely a counterexample to the
missing structural contradiction.  This checked reduction records that all
remaining work is in `ResidueTwoTightAttachmentContradiction`. -/
theorem residueTwo_wasteEquality_produces_tightAttachment
    (k : Nat) (hk : 1 ≤ k)
    (T : SimpleGraph (GridVertex (3 * k + 2) (3 * k + 2)))
    [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph (3 * k + 2) (3 * k + 2)) T)
    (heq : incidenceWaste
      (gridGraph (3 * k + 2) (3 * k + 2) \ T) = (3 * k + 2) + 2) :
    let U := residueTwoCotreeSupport T
    U.card = 6 * k ^ 2 + 5 * k + 2 ∧
      (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
        (↑((Finset.univ : Finset (GridVertex (3 * k + 2) (3 * k + 2))) \ U) :
          Set (GridVertex (3 * k + 2) (3 * k + 2)))).IsAcyclic ∧
      residueTwoAttachmentCharge U = 3 * k + 6 := by
  dsimp only
  refine ⟨(residueTwo_wasteEquality_profile k hk T hT heq).2.1, ?_,
    (residueTwo_wasteEquality_profile k hk T hT heq).2.2.2.1⟩
  simpa only [residueTwoCotreeSupport] using
    grid_tree_complement_forcedEdgeGraph_isAcyclic hT

end GridGraphs
