import GridGraphs.Core.MaxPreserved
import GridGraphs.Accounting.CotreeWaste
import GridGraphs.Constructions.ResidueOne.ResidueOneMax

/-!
# Conditional upper bounds for diagonal grids

Universal lower bounds on cotree incidence waste give operational upper bounds
on `maxPreserved`.  In residue two, excluding the first one or two possible
waste values sharpens the bound by the corresponding number of vertices.
-/

namespace GridGraphs

open SimpleGraph

/-- At side length `3k`, the universal cotree-waste bound gives the expected
operational upper bound. -/
theorem maxPreserved_three_mul_le_of_forall_incidenceWaste_ge
    (k : Nat) (hk : 1 ≤ k)
    (hwaste : ∀ (T : SimpleGraph (GridVertex (3 * k) (3 * k)))
      [DecidableRel T.Adj],
      IsSpanningSubtree (gridGraph (3 * k) (3 * k)) T →
        3 * k + 2 ≤ incidenceWaste (gridGraph (3 * k) (3 * k) \ T)) :
    maxPreserved (3 * k) (3 * k) ≤ 3 * k ^ 2 + 3 * k - 2 := by
  have h := maxPreserved_bound_of_forall_incidenceWaste_ge
    (n := 3 * k) (by omega) hwaste
  have hsquare : (3 * k) * (3 * k) + 3 * (3 * k) =
      9 * k ^ 2 + 9 * k := by ring
  rw [hsquare] at h
  omega

/-- At side length `3k+1`, the universal cotree-waste bound gives the
residue-one operational upper bound. -/
theorem maxPreserved_three_mul_add_one_le_of_forall_incidenceWaste_ge
    (k : Nat) (hk : 1 ≤ k)
    (hwaste : ∀ (T : SimpleGraph (GridVertex (3 * k + 1) (3 * k + 1)))
      [DecidableRel T.Adj],
      IsSpanningSubtree (gridGraph (3 * k + 1) (3 * k + 1)) T →
        (3 * k + 1) + 2 ≤
          incidenceWaste (gridGraph (3 * k + 1) (3 * k + 1) \ T)) :
    maxPreserved (3 * k + 1) (3 * k + 1) ≤ 3 * k ^ 2 + 5 * k := by
  have h := maxPreserved_bound_of_forall_incidenceWaste_ge
    (n := 3 * k + 1) (by omega) hwaste
  have hsquare : (3 * k + 1) * (3 * k + 1) + 3 * (3 * k + 1) =
      9 * k ^ 2 + 15 * k + 4 := by ring
  rw [hsquare] at h
  omega

/-- At side length `3k+2`, excluding equality in the basic cotree-waste bound
removes the top arithmetically possible preservation score. -/
theorem maxPreserved_three_mul_add_two_le_of_forall_incidenceWaste_ge
    (k : Nat)
    (hwaste : ∀ (T : SimpleGraph (GridVertex (3 * k + 2) (3 * k + 2)))
      [DecidableRel T.Adj],
      IsSpanningSubtree (gridGraph (3 * k + 2) (3 * k + 2)) T →
        (3 * k + 2) + 2 ≤
          incidenceWaste (gridGraph (3 * k + 2) (3 * k + 2) \ T))
    (hne : ∀ (T : SimpleGraph (GridVertex (3 * k + 2) (3 * k + 2)))
      [DecidableRel T.Adj],
      IsSpanningSubtree (gridGraph (3 * k + 2) (3 * k + 2)) T →
        incidenceWaste (gridGraph (3 * k + 2) (3 * k + 2) \ T) ≠
          (3 * k + 2) + 2) :
    maxPreserved (3 * k + 2) (3 * k + 2) ≤ 3 * k ^ 2 + 7 * k + 1 := by
  obtain ⟨T, _, hT, hmax⟩ :=
    exists_spanningSubtree_numPreserved_eq_maxPreserved
      (m := 3 * k + 2) (n := 3 * k + 2) (by omega) (by omega)
  have hbound :=
    (diagonal_cotree_incidenceWaste_ge_iff_preserved_bound (by omega) hT).mp
      (hwaste T hT)
  have hsquare : (3 * k + 2) * (3 * k + 2) + 3 * (3 * k + 2) =
      9 * k ^ 2 + 21 * k + 10 := by ring
  rw [hsquare] at hbound
  by_contra hle
  have hscore : numPreserved (3 * k + 2) (3 * k + 2) T =
      3 * k ^ 2 + 7 * k + 2 := by
    rw [hmax]
    omega
  have heq : incidenceWaste (gridGraph (3 * k + 2) (3 * k + 2) \ T) =
      (3 * k + 2) + 2 := by
    apply (diagonal_cotree_incidenceWaste_eq_iff_preserved_eq (by omega) hT).mpr
    rw [hscore]
    ring
  exact hne T hT heq

/-- For `k ≥ 5` at side length `3k+2`, excluding the next possible waste value
as well removes one further preservation score. -/
theorem maxPreserved_three_mul_add_two_revised_le_of_forall_incidenceWaste_ge
    (k : Nat) (hk : 5 ≤ k)
    (hwaste : ∀ (T : SimpleGraph (GridVertex (3 * k + 2) (3 * k + 2)))
      [DecidableRel T.Adj],
      IsSpanningSubtree (gridGraph (3 * k + 2) (3 * k + 2)) T →
        (3 * k + 2) + 2 ≤
          incidenceWaste (gridGraph (3 * k + 2) (3 * k + 2) \ T))
    (hne2 : ∀ (T : SimpleGraph (GridVertex (3 * k + 2) (3 * k + 2)))
      [DecidableRel T.Adj],
      IsSpanningSubtree (gridGraph (3 * k + 2) (3 * k + 2)) T →
        incidenceWaste (gridGraph (3 * k + 2) (3 * k + 2) \ T) ≠
          (3 * k + 2) + 2)
    (hne5 : ∀ (T : SimpleGraph (GridVertex (3 * k + 2) (3 * k + 2)))
      [DecidableRel T.Adj],
      IsSpanningSubtree (gridGraph (3 * k + 2) (3 * k + 2)) T →
        incidenceWaste (gridGraph (3 * k + 2) (3 * k + 2) \ T) ≠
          (3 * k + 2) + 5) :
    maxPreserved (3 * k + 2) (3 * k + 2) ≤ 3 * k ^ 2 + 7 * k := by
  have hbase := maxPreserved_three_mul_add_two_le_of_forall_incidenceWaste_ge
    k hwaste hne2
  obtain ⟨T, _, hT, hmax⟩ :=
    exists_spanningSubtree_numPreserved_eq_maxPreserved
      (m := 3 * k + 2) (n := 3 * k + 2) (by omega) (by omega)
  by_contra hle
  have hscore : numPreserved (3 * k + 2) (3 * k + 2) T =
      3 * k ^ 2 + 7 * k + 1 := by
    rw [hmax]
    omega
  have hw := grid_cotree_incidenceWaste_identity (by omega) (by omega) hT
  have hD := D_expand (m := 3 * k + 2) (n := 3 * k + 2)
    (by omega) (by omega)
  have hsquare : (3 * k + 2) * (3 * k + 2) =
      9 * k ^ 2 + 12 * k + 4 := by ring
  rw [hsquare] at hw hD
  have heq : incidenceWaste (gridGraph (3 * k + 2) (3 * k + 2) \ T) =
      (3 * k + 2) + 5 := by
    rw [hscore] at hw
    omega
  exact hne5 T hT heq

/-- Exact residue-zero value from a matching lower bound. -/
theorem maxPreserved_three_mul_eq_of_forall_incidenceWaste_ge
    (k : Nat) (hk : 1 ≤ k)
    (hwaste : ∀ (T : SimpleGraph (GridVertex (3 * k) (3 * k)))
      [DecidableRel T.Adj],
      IsSpanningSubtree (gridGraph (3 * k) (3 * k)) T →
        3 * k + 2 ≤ incidenceWaste (gridGraph (3 * k) (3 * k) \ T))
    (hlower : 3 * k ^ 2 + 3 * k - 2 ≤ maxPreserved (3 * k) (3 * k)) :
    maxPreserved (3 * k) (3 * k) = 3 * k ^ 2 + 3 * k - 2 :=
  Nat.le_antisymm
    (maxPreserved_three_mul_le_of_forall_incidenceWaste_ge k hk hwaste) hlower

/-- Exact residue-one value from a matching lower bound. -/
theorem maxPreserved_three_mul_add_one_eq_of_forall_incidenceWaste_ge
    (k : Nat) (hk : 1 ≤ k)
    (hwaste : ∀ (T : SimpleGraph (GridVertex (3 * k + 1) (3 * k + 1)))
      [DecidableRel T.Adj],
      IsSpanningSubtree (gridGraph (3 * k + 1) (3 * k + 1)) T →
        (3 * k + 1) + 2 ≤
          incidenceWaste (gridGraph (3 * k + 1) (3 * k + 1) \ T))
    (hlower : 3 * k ^ 2 + 5 * k ≤
      maxPreserved (3 * k + 1) (3 * k + 1)) :
    maxPreserved (3 * k + 1) (3 * k + 1) = 3 * k ^ 2 + 5 * k :=
  Nat.le_antisymm
    (maxPreserved_three_mul_add_one_le_of_forall_incidenceWaste_ge k hk hwaste)
    hlower

/-- Exact baseline residue-two value from a matching lower bound. -/
theorem maxPreserved_three_mul_add_two_eq_of_forall_incidenceWaste_ge
    (k : Nat)
    (hwaste : ∀ (T : SimpleGraph (GridVertex (3 * k + 2) (3 * k + 2)))
      [DecidableRel T.Adj],
      IsSpanningSubtree (gridGraph (3 * k + 2) (3 * k + 2)) T →
        (3 * k + 2) + 2 ≤
          incidenceWaste (gridGraph (3 * k + 2) (3 * k + 2) \ T))
    (hne : ∀ (T : SimpleGraph (GridVertex (3 * k + 2) (3 * k + 2)))
      [DecidableRel T.Adj],
      IsSpanningSubtree (gridGraph (3 * k + 2) (3 * k + 2)) T →
        incidenceWaste (gridGraph (3 * k + 2) (3 * k + 2) \ T) ≠
          (3 * k + 2) + 2)
    (hlower : 3 * k ^ 2 + 7 * k + 1 ≤
      maxPreserved (3 * k + 2) (3 * k + 2)) :
    maxPreserved (3 * k + 2) (3 * k + 2) = 3 * k ^ 2 + 7 * k + 1 :=
  Nat.le_antisymm
    (maxPreserved_three_mul_add_two_le_of_forall_incidenceWaste_ge k hwaste hne)
    hlower

/-- Exact revised residue-two value from a matching lower bound. -/
theorem maxPreserved_three_mul_add_two_revised_eq_of_forall_incidenceWaste_ge
    (k : Nat) (hk : 5 ≤ k)
    (hwaste : ∀ (T : SimpleGraph (GridVertex (3 * k + 2) (3 * k + 2)))
      [DecidableRel T.Adj],
      IsSpanningSubtree (gridGraph (3 * k + 2) (3 * k + 2)) T →
        (3 * k + 2) + 2 ≤
          incidenceWaste (gridGraph (3 * k + 2) (3 * k + 2) \ T))
    (hne2 : ∀ (T : SimpleGraph (GridVertex (3 * k + 2) (3 * k + 2)))
      [DecidableRel T.Adj],
      IsSpanningSubtree (gridGraph (3 * k + 2) (3 * k + 2)) T →
        incidenceWaste (gridGraph (3 * k + 2) (3 * k + 2) \ T) ≠
          (3 * k + 2) + 2)
    (hne5 : ∀ (T : SimpleGraph (GridVertex (3 * k + 2) (3 * k + 2)))
      [DecidableRel T.Adj],
      IsSpanningSubtree (gridGraph (3 * k + 2) (3 * k + 2)) T →
        incidenceWaste (gridGraph (3 * k + 2) (3 * k + 2) \ T) ≠
          (3 * k + 2) + 5)
    (hlower : 3 * k ^ 2 + 7 * k ≤
      maxPreserved (3 * k + 2) (3 * k + 2)) :
    maxPreserved (3 * k + 2) (3 * k + 2) = 3 * k ^ 2 + 7 * k :=
  Nat.le_antisymm
    (maxPreserved_three_mul_add_two_revised_le_of_forall_incidenceWaste_ge
      k hk hwaste hne2 hne5)
    hlower

end GridGraphs
