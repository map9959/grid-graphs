import GridGraphs.ResidueTwoUpper.OneGap.SouthCapEast15
import GridGraphs.ResidueTwoUpper.OneGap.SouthCapEast16
import GridGraphs.ResidueTwoUpper.OneGap.SouthCapEast17
import GridGraphs.ResidueTwoUpper.OneGap.SouthCapEast18
import GridGraphs.ResidueTwoUpper.OneGap.SouthCapEast19
import GridGraphs.ResidueTwoUpper.OneGap.SouthCapEast20

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan
open ResidueZero L7 BoundarySix.Connected

def eastBatchCell (i : Fin 23) : List Word :=
  let h := 21+i.val
  matrixRead (eastResult h (2*h-2) (by dsimp [h]; omega)) 0 (width h-2)

theorem eastRange_empty_of_batch (batch : ∀ i, eastBatchCell i=[])
    (h : Nat) (lo : 14≤h) (hi : h≤43) :
    ∃ rounds, matrixRead (eastResult h rounds lo) 0 (width h-2)=[] := by
  by_cases small : h≤20
  · interval_cases h
    · exact ⟨_,east14_empty⟩
    · exact ⟨_,east15_empty⟩
    · exact ⟨_,east16_empty⟩
    · exact ⟨_,east17_empty⟩
    · exact ⟨_,east18_empty⟩
    · exact ⟨_,east19_empty⟩
    · exact ⟨_,east20_empty⟩
  · let i : Fin 23 := ⟨h-21,by omega⟩
    have e : 21+i.val=h := by dsimp [i]; omega
    obtain ⟨r,hr⟩ : ∃ r, matrixRead (eastResult (21+i.val) r (by omega)) 0
        (width (21+i.val)-2)=[] := ⟨_,batch i⟩
    exact ⟨r,by simpa only [e] using hr⟩

theorem southEnd_excluded_of_east_batch (batch : ∀ i, eastBatchCell i=[])
    {u F v q} (H : PhysicalHalo u F v q (fanDirection u v))
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (score : F.card=440+1020*u+588*u^2) (big : 57≤q) (fit : q+2≤11+14*u) :
    ¬SouthEnd F v q := by
  intro south
  obtain ⟨h,lo,hi,_,_,top,line⟩ := physical_input big fit south
  obtain ⟨r,empty⟩ := eastRange_empty_of_batch batch h lo hi
  exact east_empty_excludes H acy one score (by omega) lo hi line top r empty

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan
