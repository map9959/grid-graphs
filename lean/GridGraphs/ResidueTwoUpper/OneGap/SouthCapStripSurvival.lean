import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStripTileTrace

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
open ResidueZero L7 BoundarySix.Connected
namespace GridScan

/-- Each window may have its own packed frontier width. The capacity
condition restricts the representation, not the tile marks. -/
structure Update (h : Nat) where
  window : Window h (width h)
  north : Bool
  packedWidth : 3*window.depth+1≤16

noncomputable def Update.prune {u h : Nat} (F : Finset (Site u)) (v : View)
    (z : Update h) (D : Domains) : Domains :=
  let p := physicalProgram z.window F v z.north
  z.window.prune (tileSweep (3*z.window.depth) z.window.axis p.tooth p.exits) D

noncomputable def pruneCap {u h : Nat} (F : Finset (Site u)) (v : View)
    (zs : List (Update h)) (D : Domains) : Domains :=
  zs.foldl (fun D z => z.prune F v D) D

/-- For the axis-free Lean projector, no update can discard the
actual cap. The remaining catalogue premise is the original
admission assertion, not a per-strip trace assumption. -/
theorem physical_cap_survives {u h F v q dir} (H : PhysicalHalo u F v q dir)
    (acy : (Bonds F).IsAcyclic) (one : (perimeterHoles F).card=1)
    (score : F.card=440+1020*u+588*u^2)
    (hk : 59≤11+14*u) (lo : 14≤h) (hi : h≤43)
    (line : RootLine F v (11+14*u-1) (11+14*u-h))
    (top : ∀ i, 11+14*u-width h ≤ i → i < 11+14*u →
      FanSlab.square F v (firstRow (11+14*u) h) (1+3*i)=73)
    (bank : OrdinaryCapAdmitted F v (11+14*u) h) (zs : List (Update h)) :
    Admitted h (width h) (pruneCap F v zs (initialDomains h)) (cropTiles F v (11+14*u) h) := by
  have w : width h≤11+14*u := by unfold width; omega
  have last := top (11+14*u-1) (by unfold width; omega) (by omega)
  have init := physical_initially_admitted F v _ h w top bank
  generalize initialDomains h = D at init ⊢
  induction zs generalizing D with
  | nil => exact init
  | cons z zs ih =>
    apply ih
    exact survives_update z.window _ init
      (physical_tile_trace H acy one score z.window z.north hk lo hi line last z.packedWidth)

end GridScan
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
