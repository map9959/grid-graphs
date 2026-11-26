import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStripSeams

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan
open ResidueZero L7 BoundarySix.Connected

/-- The certificate names a seam pass count and a single depth-two
vertical strip. The checked empty domain is its north-end plaquette. -/
def eastWindow (h : Nat) (lo : 14≤h) : Update h :=
  ⟨⟨.vertical,width h-2,2,by decide,by
    change width h-2+2 ≤ width h
    unfold width; omega⟩,true,by change 7≤16; decide⟩

def eastResult (h rounds : Nat) (lo : 14≤h) : MatrixBank :=
  matrixUpdate (eastWindow h lo) (seams h (matrixOf h (initialBank h)) rounds)

theorem east_empty_excludes {u h F v q} (H : PhysicalHalo u F v q (fanDirection u v))
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (score : F.card=440+1020*u+588*u^2) (hk : 59≤11+14*u)
    (lo : 14≤h) (hi : h≤43)
    (line : RootLine F v (11+14*u-1) (11+14*u-h))
    (top : ∀ i, 11+14*u-width h ≤ i → i < 11+14*u →
      FanSlab.square F v (firstRow (11+14*u) h) (1+3*i)=73)
    (rounds : Nat)
    (empty : matrixRead (eastResult h rounds lo) 0 (width h-2)=[]) : False := by
  let t := cropTiles F v (11+14*u) h
  let m := seams h (matrixOf h (initialBank h)) rounds
  let z := eastWindow h lo
  have room : width h≤11+14*u := by unfold width; omega
  have wide : 2≤width h := by unfold width; omega
  have fit : FitsTiles t := physical_tiles_fit F v _ _
  have initial := physical_initially_admitted F v _ h room top
    (physical_catalogue_admitted H acy score hk hi)
  have ok : MatrixAdmits h m t := by
    apply seams_sound
    intro r c hr hc
    change word t r c ∈ matrixRead (matrixOf h (initialBank h)) r c
    rw [matrixRead_of _ _ _ _ hr hc]
    exact initialBank_cover ⟨fit r c,fit r (c+1),fit (r+1) c,fit (r+1) (c+1)⟩
      (initial r c hr hc)
  have last := top (11+14*u-1) (by omega) (by omega)
  have tr := physical_tile_trace H acy one score z.window z.north hk lo hi line last z.packedWidth
  have survives := survives_update z.window _ ok (by
    simpa only [physical_tooth_replay _ _ _ _ room,physical_exits_replay] using tr)
  have mem := updateBank_sound z (length_ge2 lo _) 0 (width h-2) _
    (survives 0 (width h-2) (by omega) (by omega))
  change matrixRead (matrixUpdate z m) 0 (width h-2)=[] at empty
  rw [matrixUpdate_read _ _ _ _ (by omega) (by omega)] at empty
  rw [empty] at mem
  exact List.not_mem_nil mem

theorem east14_empty : matrixRead (eastResult 14 18 (by decide)) 0 (width 14-2)=[] := by
  native_decide

theorem east14_excludes {u F v q} (H : PhysicalHalo u F v q (fanDirection u v))
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (score : F.card=440+1020*u+588*u^2) (hk : 59≤11+14*u)
    (line : RootLine F v (11+14*u-1) (11+14*u-14))
    (top : ∀ i, 11+14*u-width 14 ≤ i → i < 11+14*u →
      FanSlab.square F v (firstRow (11+14*u) 14) (1+3*i)=73) : False :=
  east_empty_excludes H acy one score hk (by decide) (by decide) line top 18 east14_empty

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip.GridScan
