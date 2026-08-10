import GridGraphs.UniversalWasteBoundReduction
import GridGraphs.ResidueTwoWasteEqualityObstruction
import GridGraphs.ResidueTwoNearWasteDebt

/-!
# Width-independent component attachment ledger

For a set `U` whose complementary forced-edge graph is acyclic, the support
cardinality determines the four-side component rank exactly.  The parameter
`q` in `fourSideComponentRank_eq_of_attachment_balance` is a width-independent
defect parameter: any phase-specific argument establishing the corresponding
cardinality balance can use the same theorem.

This ledger also separates the three outstanding geometric obligations.  The
universal waste bound asks for a lower bound on the cardinality balance.  At
the residue-two equality and near-waste cardinalities, however, acyclicity
forces ranks `3k+6` and `3k+9` respectively.  Thus their exclusions must show
that the relevant acyclic profile cannot occur; no stronger rank inequality
can follow from acyclicity and cardinality alone.
-/

namespace GridGraphs

open Finset SimpleGraph

set_option maxHeartbeats 800000

/-- Exact component-resolved attachment ledger.  It applies at every width and
uses only acyclicity of the complementary forced-edge graph. -/
theorem fourSideComponentRank_add_twice_area_eq_attachment_balance
    {n : Nat} (hn : 2 ≤ n) (U : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n)
      (↑((Finset.univ : Finset (GridVertex n n)) \ U) :
        Set (GridVertex n n))).IsAcyclic) :
    fourSideComponentRank n U + 2 * (n * n) =
      3 * U.card + 4 * n := by
  rw [fourSideComponentRank_eq_component_charge hn U]
  exact square_grid_component_reduction_compl hn U hacyc

/-- Defect-parameter form of the exact attachment ledger. -/
theorem fourSideComponentRank_eq_of_attachment_balance
    {n q : Nat} (hn : 2 ≤ n) (U : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n)
      (↑((Finset.univ : Finset (GridVertex n n)) \ U) :
        Set (GridVertex n n))).IsAcyclic)
    (hbalance : 3 * U.card + 4 * n = 2 * (n * n) + q) :
    fourSideComponentRank n U = q := by
  have hledger :=
    fourSideComponentRank_add_twice_area_eq_attachment_balance hn U hacyc
  omega

/-- Threshold form of the ledger.  In particular, the universal rank target is
exactly a support-cardinality balance, rather than a consequence of a weaker
component estimate. -/
theorem fourSideComponentRank_ge_iff_attachment_balance_ge
    {n q : Nat} (hn : 2 ≤ n) (U : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n)
      (↑((Finset.univ : Finset (GridVertex n n)) \ U) :
        Set (GridVertex n n))).IsAcyclic) :
    q ≤ fourSideComponentRank n U ↔
      2 * (n * n) + q ≤ 3 * U.card + 4 * n := by
  have hledger :=
    fourSideComponentRank_add_twice_area_eq_attachment_balance hn U hacyc
  omega

/-- Component/cardinality form of the universal `W ≥ n+2` target for a square
grid spanning tree. -/
theorem square_grid_tree_universalWaste_iff_attachment_balance
    {n : Nat} (hn : 3 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T) :
    n + 2 ≤ incidenceWaste (gridGraph n n \ T) ↔
      2 * (n * n) + (n + 4) ≤
        3 * (supportFinset (gridGraph n n \ T)).card + 4 * n := by
  let U := supportFinset (gridGraph n n \ T)
  have hacyc : (forcedEdgeGraph (gridGraph n n)
      (↑((Finset.univ : Finset (GridVertex n n)) \ U) :
        Set (GridVertex n n))).IsAcyclic := by
    simpa only [U] using grid_tree_complement_forcedEdgeGraph_isAcyclic hT
  rw [square_grid_tree_universalWaste_iff_fourSideComponentRank hn hT]
  change n + 4 ≤ fourSideComponentRank n U ↔
    2 * (n * n) + (n + 4) ≤ 3 * U.card + 4 * n
  exact fourSideComponentRank_ge_iff_attachment_balance_ge (by omega) U hacyc

/-- At the residue-two waste-equality cardinality, acyclicity determines the
tight attachment charge.  Hence excluding equality requires nonexistence of
this acyclic profile, not a different consequence of its numerical data. -/
theorem residueTwo_tight_card_acyclic_attachment_exact
    (k : Nat) (U : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hcard : U.card = 6 * k ^ 2 + 5 * k + 2)
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑((Finset.univ : Finset (GridVertex (3 * k + 2) (3 * k + 2))) \ U) :
        Set (GridVertex (3 * k + 2) (3 * k + 2)))).IsAcyclic) :
    residueTwoAttachmentCharge U = 3 * k + 6 := by
  rw [← fourSideComponentRank_eq_residueTwoAttachmentCharge (by omega) U]
  apply fourSideComponentRank_eq_of_attachment_balance (by omega) U hacyc
  rw [hcard]
  ring

/-- At the near-waste cardinality the same unconditional ledger gives exactly
`3k+9`, one below the persistent-debt target.  A proof of persistent debt must
therefore contradict existence of this acyclic cardinality profile. -/
theorem residueTwo_near_card_acyclic_attachment_exact
    (k : Nat) (U : Finset (GridVertex (3 * k + 2) (3 * k + 2)))
    (hcard : U.card = 6 * k ^ 2 + 5 * k + 3)
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
      (↑((Finset.univ : Finset (GridVertex (3 * k + 2) (3 * k + 2))) \ U) :
        Set (GridVertex (3 * k + 2) (3 * k + 2)))).IsAcyclic) :
    fourSideComponentRank (3 * k + 2) U = 3 * k + 9 := by
  apply fourSideComponentRank_eq_of_attachment_balance (by omega) U hacyc
  rw [hcard]
  ring

/-- The stated tight-attachment obstruction is equivalent to nonexistence of
the corresponding acyclic cardinality profile.  Its charge inequality carries
no additional freedom once the component ledger is applied. -/
theorem residueTwoTightAttachmentContradiction_iff_no_acyclic_profile :
    ResidueTwoTightAttachmentContradiction ↔
      ∀ (k : Nat), 1 ≤ k →
        ∀ U : Finset (GridVertex (3 * k + 2) (3 * k + 2)),
          U.card = 6 * k ^ 2 + 5 * k + 2 →
          ¬(forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
            (↑((Finset.univ :
                Finset (GridVertex (3 * k + 2) (3 * k + 2))) \ U) :
              Set (GridVertex (3 * k + 2) (3 * k + 2)))).IsAcyclic := by
  constructor
  · intro hobstruction k hk U hcard hacyc
    exact (hobstruction k hk U hcard hacyc)
      (residueTwo_tight_card_acyclic_attachment_exact k U hcard hacyc)
  · intro hno k hk U hcard hacyc
    exact (hno k hk U hcard hacyc).elim

/-- Persistent near-waste debt is likewise equivalent to nonexistence of its
spanning-tree/cardinality profile: acyclicity of every tree complement and the
exact ledger would otherwise fix the rank one below the requested debt. -/
theorem stableResidueTwoPersistentAttachmentDebt_iff_no_near_profile :
    StableResidueTwoPersistentAttachmentDebt ↔
      ∀ (k : Nat), 5 ≤ k →
        ∀ (T : SimpleGraph (GridVertex (3 * k + 2) (3 * k + 2)))
          [DecidableRel T.Adj],
          IsSpanningSubtree (gridGraph (3 * k + 2) (3 * k + 2)) T →
          (supportFinset
            (gridGraph (3 * k + 2) (3 * k + 2) \ T)).card =
              6 * k ^ 2 + 5 * k + 3 →
          False := by
  constructor
  · intro hdebt k hk T _ hT hcard
    let U := supportFinset (gridGraph (3 * k + 2) (3 * k + 2) \ T)
    have hacyc : (forcedEdgeGraph (gridGraph (3 * k + 2) (3 * k + 2))
        (↑((Finset.univ : Finset (GridVertex (3 * k + 2) (3 * k + 2))) \ U) :
          Set (GridVertex (3 * k + 2) (3 * k + 2)))).IsAcyclic := by
      simpa only [U] using grid_tree_complement_forcedEdgeGraph_isAcyclic hT
    have hexact := residueTwo_near_card_acyclic_attachment_exact k U hcard hacyc
    have hgap := hdebt k hk T hT hcard
    change 3 * k + 10 ≤ fourSideComponentRank (3 * k + 2) U at hgap
    omega
  · intro hno k hk T _ hT hcard
    exact (hno k hk T hT hcard).elim

end GridGraphs
