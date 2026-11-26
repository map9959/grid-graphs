import GridGraphs.NoPitch.Budget.Side19Reduction
import GridGraphs.NoPitch.Budget.StarPatch19
import GridGraphs.Tests.CapSiteTableReplay

namespace GridGraphs.NoPitch.LocalBoard19
open Budget PitchCut GridGraphs.NoPitch.Dual
attribute [local irreducible] chart19

/-- Census against the uncompressed source ids stored by the actual
decoder. This distinguishes star normalization from patch normalization
and checks both subfamilies of the line table. -/
theorem census19 :
    let rows := chart19.rows
    let count (lo hi : Nat) := (rows.filter fun r => lo ≤ r.source && r.source ≤ hi).size
    [count 1 1,count 2 55,count 56 100,count 101 630,count 631 3196,count 3197 4674,
      count 4675 4710,count 4711 5172,count 5173 6063,count 6064 6351,
      ((List.range rows.size).filter flowRow).length,((List.range rows.size).filter lineLetters).length]=
      [1,9,3,331,820,764,1,356,505,81,307,198] := by native_decide

/-- The entire non-face side of the side-19 replay; all events and
successive windows are projected from the same `out F`. -/
theorem overlap_rows19 (F : Finset X) (acy : (G F).IsAcyclic)
    (np : ∀ v, ¬(Pitch F v ∨ Pitch (transpose F) v)) (i : Fin chart19.rows.size)
    (h : outstanding i) :
    2*lhs chart19 (physicalVector chart19 F (out F)) i=8*chart19.rows[i].rhs.atStep 0 := by
  simp only [outstanding,Bool.or_eq_true] at h
  rcases h with ((e|s)|p)|l
  · exact edge_rows19 F acy i e
  · exact sp_rows19 F acy i s
  · exact pair_rows19 F acy i p
  · exact letter_rows19 F acy np i l

def FacePatchRows (F : Finset X) := ∀ i : Fin chart19.rows.size, FaceRows.selected chart19 i →
  rowHolds chart19.rows[i].sense (2*lhs chart19 (physicalVector chart19 F (out F)) i)
    (8*chart19.rows[i].rhs.atStep 0)
def FaceLineRows (F : Finset X) := ∀ i : Fin chart19.rows.size, FaceLines.kept i →
  rowHolds chart19.rows[i].sense (2*lhs chart19 (physicalVector chart19 F (out F)) i)
    (8*chart19.rows[i].rhs.atStep 0)

theorem feasible19_of_face_rows (F : Finset X) (acy : (G F).IsAcyclic)
    (np : ∀ v, ¬(Pitch F v ∨ Pitch (transpose F) v))
    (patch : FacePatchRows F) (line : FaceLineRows F) :
    Feasible chart19 (physicalVector chart19 F (out F)) 8 0 (8*19^2) :=
  feasible19_of_overlaps F acy np patch line (overlap_rows19 F acy np)

/-- Assembly interface for the separately checked two face replays. -/
theorem exact19_of_face_rows
    (patch : ∀ F : Finset X, (G F).IsAcyclic → FacePatchRows F)
    (line : ∀ F : Finset X, (G F).IsAcyclic → (∀ v, ¬(Pitch F v ∨ Pitch (transpose F) v)) → FaceLineRows F) :
    maxPreserved 19 19=138 := by
  change maxPreserved (N 6) (N 6)=squareScore (N 6)
  apply exact_of_no_pitch_verified (by decide)
  intro F hf _ np
  have acy := mem_acyclicForcedSets.mp hf
  exact upper19_of_overlaps F acy np (patch F acy) (line F acy np) (overlap_rows19 F acy np)

end GridGraphs.NoPitch.LocalBoard19
