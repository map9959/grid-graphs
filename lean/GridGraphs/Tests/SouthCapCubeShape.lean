import GridGraphs.Tests.SouthCapAllPrices

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap

def cubeFits (width z : Nat) : Bool :=
  z%512 < 2^width && (z/512 &&& (z%512))==z/512

private theorem patchFits : ∀ i j : Fin 9, (patchCubes i j).all (cubeFits 9) := by
  native_decide
private theorem starFits : ∀ (i j : Fin 9) (o : Fin 5),
    (starCubes i j o).all (cubeFits ((compass (pricePoint starReps i j)).length+1)) := by
  native_decide

theorem patch_cube_shape (i j : Fin 9) (z : Nat) (hz : z∈patchCubes i j) :
    z%512 < 2^9 ∧ (z/512 &&& (z%512))=z/512 := by
  simpa only [cubeFits,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] using
    List.all_eq_true.mp (patchFits i j) z hz

theorem star_cube_shape (i j : Fin 9) (o : Fin 5) (z : Nat) (hz : z∈starCubes i j o) :
    z%512 < 2^((compass (pricePoint starReps i j)).length+1) ∧
      (z/512 &&& (z%512))=z/512 := by
  simpa only [cubeFits,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] using
    List.all_eq_true.mp (starFits i j o) z hz

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
