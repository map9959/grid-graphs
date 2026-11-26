import GridGraphs.NoPitch.TailRows.FaceOverlaps
import GridGraphs.NoPitch.TailRows.FaceLine
import GridGraphs.NoPitch.TailRows.FacePatchRows
import GridGraphs.Tests.CapSiteTableReplay

namespace GridGraphs
open PitchCut NoPitch.Budget NoPitch.TailRows

/-- The physical residue-one equality on the two infinite tail progressions. -/
theorem maxPreserved_residue_one_tail {k : Nat} (hk : 19 ≤ k) :
    maxPreserved (3*k+1) (3*k+1) = squareScore (3*k+1) := by
  apply exact_of_no_pitch_verified (by omega)
  intro F mem _ np
  have acy := mem_acyclicForcedSets.mp mem
  have rows (r) : ¬Pitch F (teeth k r) := fun h => np _ (.inl h)
  have cols (r) : ¬Pitch (trans F) (teeth k r) := fun h => np _ (.inr h)
  apply upper_of_face_overlaps hk F acy rows cols
  intro i h
  rcases Bool.or_eq_true_iff.mp h with patch|line
  · exact FacePatch.face_patch_tail hk F acy (out F) i (beq_iff_eq.mp patch)
  · exact FaceLine.face_line_tail hk F acy rows cols (out F) i (beq_iff_eq.mp line)

end GridGraphs
