import GridGraphs.Accounting.BoundaryFiveBudget
import GridGraphs.Geometry.StraightForcedComponents
import GridGraphs.Core.ForcedMaximum

/-!
# A square-grid upper bound from straight component lengths

Each induced preserved component fits in one row or column, so its size is
at most the side length. Combining that geometric restriction with the exact
component ledger and five units of boundary deficiency improves the elementary
square upper bound. It does not prove the conjectured sharp bound.
-/

namespace GridGraphs

open Finset SimpleGraph

/-- The preserved set has at most `n` vertices per induced component. -/
theorem forced_card_le_side_mul_components {n : Nat}
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic) :
    F.card ≤ n * Fintype.card ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent := by
  classical
  let G := (gridGraph n n).induce (↑F : Set _)
  have hcap (C : G.ConnectedComponent) : C.supp.toFinset.card ≤ n := by
    rw [Set.toFinset_card]
    rcases induced_forced_connectedComponent_straight hacyc C with ⟨r, hr⟩ | ⟨c, hc⟩
    · have hinj : Function.Injective (fun v : C.supp => v.1.1.2) := by
        intro v w h
        apply Subtype.ext
        apply Subtype.ext
        exact Prod.ext ((hr v.1 v.2).trans (hr w.1 w.2).symm) h
      simpa using Fintype.card_le_of_injective _ hinj
    · have hinj : Function.Injective (fun v : C.supp => v.1.1.1) := by
        intro v w h
        apply Subtype.ext
        apply Subtype.ext
        exact Prod.ext h ((hc v.1 v.2).trans (hc w.1 w.2).symm)
      simpa using Fintype.card_le_of_injective _ hinj
  have hcover : (univ.biUnion fun C : G.ConnectedComponent => C.supp.toFinset) =
      (univ : Finset (↑F : Set (GridVertex n n))) := by
    ext v
    simp [ConnectedComponent.mem_supp_iff]
  calc
    F.card = (univ : Finset (↑F : Set (GridVertex n n))).card := by simp
    _ = (univ.biUnion fun C : G.ConnectedComponent => C.supp.toFinset).card :=
      congrArg Finset.card hcover.symm
    _ = ∑ C : G.ConnectedComponent, C.supp.toFinset.card := by
      rw [Finset.card_biUnion]
      intro C _ D _ hne
      simpa using pairwise_disjoint_supp_connectedComponent G hne
    _ ≤ ∑ _C : G.ConnectedComponent, n := Finset.sum_le_sum (fun C _ => hcap C)
    _ = n * Fintype.card G.ConnectedComponent := by simp [Nat.mul_comm]

/-- Subtraction-free operational inequality combining length and boundary costs. -/
theorem forced_card_carrier_length_inequality {n : Nat} (hn : 5 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic) :
    (3 * n + 1) * F.card + 6 * n ≤ n * (n * n + 4 * n) := by
  classical
  have hlength := forced_card_le_side_mul_components F hacyc
  have hboundary := five_le_boundaryDeficiencySum_compl hn F hacyc
  have hledger := grid_component_reduction F hacyc
  have hpartition := boundaryDeficiencySum_add_compl n n F
  have htotal := total_boundaryDeficiencySum (by omega : 2 ≤ n) (by omega : 2 ≤ n)
  have hcomponent : 1 ≤ Fintype.card
      (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).ConnectedComponent := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨(forcedEdgeGraph (gridGraph n n) (↑F : Set _)).connectedComponentMk
      (⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  have hbudget : 3 * F.card +
      Fintype.card ((gridGraph n n).induce (↑F : Set _)).ConnectedComponent + 6 ≤
        n * n + 4 * n := by omega
  have hscaled := Nat.mul_le_mul_left n hbudget
  nlinarith

/-- The cardinality bound applies to every feasible set, including the empty set. -/
theorem forced_card_le_carrier_length_bound {n : Nat} (hn : 5 ≤ n)
    (F : Finset (GridVertex n n))
    (hacyc : (forcedEdgeGraph (gridGraph n n) (↑F : Set _)).IsAcyclic) :
    F.card ≤ n * (n * n + 4 * n - 6) / (3 * n + 1) := by
  have h := forced_card_carrier_length_inequality hn F hacyc
  have hnonneg : 6 ≤ n * n + 4 * n := by nlinarith
  have hsplit := congrArg (fun a : Nat => n * a) (Nat.sub_add_cancel hnonneg)
  apply (Nat.le_div_iff_mul_le (by omega : 0 < 3 * n + 1)).mpr
  nlinarith

/-- Unconditional square-grid upper bound from the carrier-length restriction. -/
theorem maxPreserved_le_carrier_length_bound {n : Nat} (hn : 5 ≤ n) :
    maxPreserved n n ≤ n * (n * n + 4 * n - 6) / (3 * n + 1) := by
  classical
  rw [maxPreserved_eq_maxForcedAcyclic (by omega) (by omega)]
  unfold maxForcedAcyclic
  apply Finset.sup_le
  intro F hF
  exact forced_card_le_carrier_length_bound hn F (mem_acyclicForcedSets.mp hF)

end GridGraphs
