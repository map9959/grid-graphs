import GridGraphs.Tests.FaceCoverage19
import GridGraphs.Tests.FacePatchChecks19
import GridGraphs.NoPitch.FaceRowsSound

namespace GridGraphs.NoPitch.FaceRows
open GridGraphs.NoPitch.Dual PitchCut Keys Wired

theorem positive19 : chart19.cols.all (fun c => c.units != 0) := by native_decide
theorem selected_count : (chart19.rows.filter fun r => 4711≤r.source && r.source≤5172).size=356 := by
  native_decide

attribute [local irreducible] chart19

/-- The actual patch/face marginal portion of `Feasible.rows`, in the
decoded dual's original column order, on every side-19 physical forest. -/
theorem physical_patch_rows19 (F : Finset (Site 6)) (acy : (G F).IsAcyclic)
    (out : Site 6 → Option (Fin 4)) (i : Fin chart19.rows.size) (sel : selected chart19 i) :
    rowHolds chart19.rows[i].sense (2*lhs chart19 (physicalVector chart19 F out) i)
      (8*chart19.rows[i].rhs.atStep 0) := by
  apply projected_rows _ _ _ other19 unused19 rows19 _ _ i sel
  · intro j
    exact bne_iff_ne.mp (Array.all_eq_true_iff_forall_mem.mp positive19 _ (Array.getElem_mem j.isLt))
  · intro p
    let m := faceMask F p
    let q := (faceAtom F p).2
    obtain ⟨lt,mask⟩ := mask_roundtrip m
    obtain ⟨mem,part⟩ := partition_roundtrip q (physical_partition F p)
    obtain ⟨raw,ok⟩ := physical_wiring p F acy
    have cat : colorCode q∈catalog m := List.mem_filter.mpr ⟨mem,by rwa [part]⟩
    exact local_tile _ tiles19 m q ⟨_,lt⟩ mask _ part cat raw p

end GridGraphs.NoPitch.FaceRows
