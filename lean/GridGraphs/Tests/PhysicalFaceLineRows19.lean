import GridGraphs.Tests.FaceCoverage19
import GridGraphs.Tests.FaceLineChecks19
import GridGraphs.NoPitch.FaceLineSound

namespace GridGraphs.NoPitch.FaceLines
open GridGraphs.NoPitch.Dual PitchCut Keys Wired

private theorem positive_units : chart19.cols.all (fun c => c.units != 0) := by native_decide

theorem kept_count : (chart19.rows.filter fun r => 6064≤r.source && r.source≤6351).size=81 := by
  native_decide

attribute [local irreducible] chart19

/-- All 81 retained face/line marginals in the decoded side-19 chart hold
on the physical vector of every no-pitch forest, for any orientation labels. -/
theorem physical_face_line_rows19 (F : Finset (Site 6)) (acy : (G F).IsAcyclic)
    (np : ∀ v, ¬(Pitch F v ∨ Pitch (transpose F) v)) (out : Site 6 → Option (Fin 4))
    (i : Fin chart19.rows.size) (sel : kept i) :
    rowHolds chart19.rows[i].sense (2*lhs chart19 (physicalVector chart19 F out) i)
      (8*chart19.rows[i].rhs.atStep 0) := by
  refine projected_line_rows chart19 F out np steps19 other19 meta19 ?_ ?_ i sel
  · intro j
    exact bne_iff_ne.mp (Array.all_eq_true_iff_forall_mem.mp positive_units _ (Array.getElem_mem j.isLt))
  · intro p
    let m := faceMask F p
    let q := (faceAtom F p).2
    obtain ⟨lt,mask⟩ := mask_roundtrip m
    obtain ⟨mem,part⟩ := partition_roundtrip q (physical_partition F p)
    obtain ⟨raw,ok⟩ := physical_wiring p F acy
    have cat : colorCode q∈catalog m := List.mem_filter.mpr ⟨mem,by rwa [part]⟩
    exact tile_balance _ tiles19 m q ⟨_,lt⟩ mask _ part cat raw p

end GridGraphs.NoPitch.FaceLines
