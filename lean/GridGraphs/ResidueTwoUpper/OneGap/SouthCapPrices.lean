import GridGraphs.ResidueTwoUpper.OneGap.FanSlabChart
import GridGraphs.ResidueTwoUpper.OneGap.SouthCapArithmetic

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
open L7 FanSlab ResidueZero Stencil

/-- Patch origins (and the interior stars at their centers) can be
transported from the physical southeast halo to the 119-wide atlas.
Either both points are in the periodic middle, or their distances to
the southeast rim agree. -/
def Align (u x b : Nat) : Prop :=
  6≤x ∧ 6≤b ∧ x<33+42*u ∧ b<117 ∧
    ((x+7≤33+42*u ∧ b+7≤117 ∧ x%3=b%3) ∨
     (111≤b ∧ 33+42*u-x=117-b))

private theorem align_common {u x b : Nat} (a : Align u x b) :
    ∃ j, related u x j ∧ related 2 b j := by
  obtain ⟨xlo,blo,xhi,bhi,h⟩ := a
  rcases h with ⟨hx,hb,eq⟩|⟨hb,eq⟩
  · refine ⟨6+b%3,.inr (.inr ?_),.inr (.inr ?_)⟩ <;> omega
  · exact ⟨b-84,.inr (.inl ⟨by omega,by omega⟩),.inr (.inl ⟨by omega,by omega⟩)⟩

/-- Transport checks *local prices*, not tile frequencies. The original
mask and arrow are unchanged. This covers every interior centre slot
for which the two halo coordinates satisfy `Align`. -/
theorem atlas_prices {u x y a b : Nat} (R : Align u x a) (C : Align u y b)
    (w : View) (m f nb o : Nat) :
    twoOrbitPatch (35+42*(u:Int)) (L7.view w (33+42*(u:Int)) x y) m =
      twoOrbitPatch 119 (L7.view w 117 a b) m ∧
    twoOrbitStar (35+42*(u:Int)) (L7.view w (35+42*(u:Int)) ((x:Int)+1) ((y:Int)+1)) f nb o =
      twoOrbitStar 119 (L7.view w 119 ((a:Int)+1) ((b:Int)+1)) f nb o := by
  obtain ⟨_,xr,ar⟩ := align_common R
  obtain ⟨_,yc,bc⟩ := align_common C
  have X := agreements xr yc w m f nb o
  have Y := agreements ar bc w m f nb o
  exact ⟨X.1.trans Y.1.symm,X.2.trans Y.2.symm⟩

/-- The *same* halo offset is used at both widths. Offsets run from
−6 through +9 for complete 3×3 patches in the halo. Membership in the
patch-origin range is preserved even in clipped halos. -/
theorem halo_origins {u k extent i d : Nat} (ke : k=11+14*u) (hk : 53≤k)
    (he : extent+4≤k) (hi : i+2≤extent) (hd : d≤15) :
    let x := (1+3*(k-extent+i))-6+d
    let b := (1+3*repTile (endTag extent i))-6+d
    (x<33+42*u ↔ b<117) ∧ (x<33+42*u → Align u x b) := by
  dsimp only
  unfold endTag repTile Align
  split_ifs <;> omega

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
