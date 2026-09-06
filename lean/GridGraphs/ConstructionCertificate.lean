import GridGraphs.GridDual
import GridGraphs.ResidueOneMax

/-!
# Construction certificates

A decreasing parent rank is a small, reusable connectivity certificate. For
grid duals, such a certificate feeds directly into the maximum-preservation
lower-bound construction.
-/

namespace GridGraphs

open Finset SimpleGraph

/-- A rooted parent map whose rank strictly decreases away from the root. -/
structure RankedParentCertificate {V : Type*} (G : SimpleGraph V) where
  root : V
  parent : V → V
  rank : V → Nat
  parent_adj : ∀ v, v ≠ root → G.Adj v (parent v)
  rank_parent_lt : ∀ v, v ≠ root → rank (parent v) < rank v

namespace RankedParentCertificate

/-- Following parents reaches the root. -/
theorem reachable_root {V : Type*} {G : SimpleGraph V}
    (C : RankedParentCertificate G) (v : V) : G.Reachable v C.root := by
  have go : ∀ n v, C.rank v = n → G.Reachable v C.root := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro w hw
        by_cases hroot : w = C.root
        · subst w
          exact Reachable.refl C.root
        · exact (C.parent_adj w hroot).reachable.trans
            (ih (C.rank (C.parent w)) (by simpa [hw] using C.rank_parent_lt w hroot)
              (C.parent w) rfl)
  exact go (C.rank v) v rfl

/-- A ranked parent certificate proves graph connectivity. -/
theorem connected {V : Type*} {G : SimpleGraph V}
    (C : RankedParentCertificate G) : G.Connected := by
  let : Nonempty V := ⟨C.root⟩
  constructor
  intro v w
  exact (C.reachable_root v).trans (C.reachable_root w).symm

end RankedParentCertificate

/-- Dual connectivity gives a lower bound from every vertex outside `U`. -/
theorem compl_card_le_maxPreserved_of_uuDual_connected {m n : Nat}
    (hm : 1 ≤ m) (hn : 1 ≤ n) (U : Finset (GridVertex m n))
    (hdual : (uuDualGraph U).Connected) :
    (Finset.univ \ U).card ≤ maxPreserved m n := by
  classical
  obtain ⟨T, hTG, htree, hpreserves⟩ :=
    exists_isTree_preserving_compl_of_uuDual_connected_grid U hdual
      (gridGraph_connected hm hn)
  apply le_maxPreserved_of_witness ⟨hTG, htree⟩
  unfold numPreserved
  apply Finset.card_le_card
  intro v hv
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hv
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  unfold isPreserved
  apply degree_eq_of_le_of_preservesIncidentEdges (gridGraph m n) T hTG
  exact hpreserves (by simpa using hv)

/-- A ranked parent certificate for the U-U dual gives the same lower bound. -/
theorem compl_card_le_maxPreserved_of_rankedDualCertificate {m n : Nat}
    (hm : 1 ≤ m) (hn : 1 ≤ n) (U : Finset (GridVertex m n))
    (C : RankedParentCertificate (uuDualGraph U)) :
    (Finset.univ \ U).card ≤ maxPreserved m n :=
  compl_card_le_maxPreserved_of_uuDual_connected hm hn U C.connected

end GridGraphs
