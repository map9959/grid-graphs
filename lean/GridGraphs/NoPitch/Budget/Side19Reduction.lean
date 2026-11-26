import GridGraphs.NoPitch.Budget.Flow19
import GridGraphs.NoPitch.FaceRows
import GridGraphs.NoPitch.FaceLineRows

namespace GridGraphs.NoPitch.LocalBoard19
open Budget PitchCut GridGraphs.NoPitch.Dual
attribute [local irreducible] chart19

def starEdges (i : Nat) := 13 ≤ i && i ≤ 343
def starPatch (i : Nat) := 344 ≤ i && i ≤ 1163
def patchPairs (i : Nat) := 1164 ≤ i && i ≤ 1927
def outstanding (i : Nat) := starEdges i || starPatch i || patchPairs i || lineLetters i

/-- The correspondence is checked against the source field of every
retained row, not inferred from a continuous interval in the full LP. -/
theorem ranges : ∀ i : Fin chart19.rows.size,
    let s := chart19.rows[i].source
    (normRow i ↔ 2 ≤ s ∧ s≤100) ∧ (starEdges i ↔ 101 ≤ s ∧ s≤630) ∧
    (starPatch i ↔ 631 ≤ s ∧ s≤3196) ∧ (patchPairs i ↔ 3197 ≤ s ∧ s≤4674) ∧
    (flowRow i ∨ lineLetters i ↔ 5173 ≤ s ∧ s≤6063) := by native_decide

theorem remaining_count : (Finset.univ.filter fun i : Fin chart19.rows.size => outstanding i).card=2113 := by
  native_decide

private theorem cover : ∀ i : Fin chart19.rows.size, chart19.rows[i].sense=0 → i.val≠1928 →
    normRow i ∨ flowRow i ∨ FaceRows.selected chart19 i ∨ FaceLines.kept i ∨ outstanding i := by
  native_decide

theorem feasible19_of_overlaps (F : Finset X) (acy : (G F).IsAcyclic)
    (np : ∀ v, ¬(Pitch F v ∨ Pitch (transpose F) v))
    (facePatch : ∀ i : Fin chart19.rows.size, FaceRows.selected chart19 i →
      rowHolds chart19.rows[i].sense (2*lhs chart19 (physicalVector chart19 F (out F)) i)
        (8*chart19.rows[i].rhs.atStep 0))
    (faceLine : ∀ i : Fin chart19.rows.size, FaceLines.kept i →
      rowHolds chart19.rows[i].sense (2*lhs chart19 (physicalVector chart19 F (out F)) i)
        (8*chart19.rows[i].rhs.atStep 0))
    (rows : ∀ i : Fin chart19.rows.size, outstanding i →
      2*lhs chart19 (physicalVector chart19 F (out F)) i=8*chart19.rows[i].rhs.atStep 0) :
    Feasible chart19 (physicalVector chart19 F (out F)) 8 0 (8*19^2) := by
  apply feasible19_of_remaining F acy
  intro i e ne
  rcases cover i e ne with a|b|c|d|h
  · exact normalization19 F acy i a
  · exact flow19 F np _ i b
  · have h := facePatch i c; rw [e] at h; exact h
  · have h := faceLine i d; rw [e] at h; exact h
  · exact rows i h

theorem upper19_of_overlaps (F : Finset X) (acy : (G F).IsAcyclic)
    (np : ∀ v, ¬(Pitch F v ∨ Pitch (transpose F) v))
    (facePatch : ∀ i : Fin chart19.rows.size, FaceRows.selected chart19 i →
      rowHolds chart19.rows[i].sense (2*lhs chart19 (physicalVector chart19 F (out F)) i)
        (8*chart19.rows[i].rhs.atStep 0))
    (faceLine : ∀ i : Fin chart19.rows.size, FaceLines.kept i →
      rowHolds chart19.rows[i].sense (2*lhs chart19 (physicalVector chart19 F (out F)) i)
        (8*chart19.rows[i].rhs.atStep 0))
    (rows : ∀ i : Fin chart19.rows.size, outstanding i →
      2*lhs chart19 (physicalVector chart19 F (out F)) i=8*chart19.rows[i].rhs.atStep 0) :
    F.card ≤ squareScore 19 :=
  physical_finite_upper .n19 (by decide) F acy _ (out_inside F) (feasible19_of_overlaps F acy np facePatch faceLine rows)

end GridGraphs.NoPitch.LocalBoard19
