import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStripReplayMatrix

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan

def top14 : Update 14 := ⟨⟨.horizontal,0,2,by decide,by decide⟩,true,by decide⟩

/-- Actual catalogue, first horizontal strip. At top-row column 2 the
seven catalogue plaquettes reduce to exactly these three (NW,NE,SW,SE). -/
theorem top14_cell2 :
    (initialBank 14 0 2).length=7 ∧
    matrixRead (matrixUpdate top14 (matrixOf 14 (initialBank 14))) 0 2 =
      [(73,73,9,9),(73,73,9,73),(73,73,73,73)] := by native_decide

theorem top14_cell2_physical {t : Tiles}
    (ad : Admitted 14 (width 14) (memBank (initialBank 14)) t)
    (tr : top14.window.HasTrace (tileSweep (3*top14.window.depth) top14.window.axis
      (replayTooth top14.window top14.north) (replayExits top14.window))
      (band t top14.window.axis top14.window.start)) :
    word t 0 2 ∈ [(73,73,9,9),(73,73,9,73),(73,73,73,73)] := by
  let m := matrixOf 14 (initialBank 14)
  have valid : Admitted 14 (width 14) (memBank (matrixRead m)) t := by
    intro r c hr hc
    change word t r c ∈ matrixRead (matrixOf 14 (initialBank 14)) r c
    rw [matrixRead_of _ _ _ _ hr hc]
    exact ad r c hr hc
  have survives := survives_update top14.window _ valid tr
  rw [←top14_cell2.2,matrixUpdate_read _ _ _ _ (by decide) (by decide)]
  exact updateBank_sound top14 (by decide) 0 2 _ (survives 0 2 (by decide) (by decide))

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan
