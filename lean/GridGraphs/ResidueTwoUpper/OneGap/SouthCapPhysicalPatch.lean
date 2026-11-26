import GridGraphs.ResidueTwoUpper.OneGap.SouthCapPatchOrientation
import GridGraphs.ResidueTwoUpper.OneGap.FanStep

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
open ResidueZero Stencil L7

private theorem lane_testBit (m i : Nat) : lane m i = (m.testBit i).toNat := by
  rw [←show i+0=i from rfl,←Nat.testBit_shiftRight]
  unfold lane
  rw [Nat.testBit_zero]
  have h := Nat.mod_lt (m >>> i) (by decide : 0<2)
  by_cases one : (m >>> i)%2=1 <;> simp [one]
  omega

private theorem bool_of_toNat (a b : Bool) (h : a.toNat=b.toNat) : a=b := by
  cases a <;> cases b <;> simp_all

theorem physical_patch_square {u k h w r c F v q dir} (pl : Placement u k h w r c)
    (H : PhysicalHalo u F v q dir) (p : Offset)
    (hr : p.1+2<18) (hc : p.2+2<18)
    (insidePatch : inside 117 (absAt (endTag h r) (endTag w c) p)) :
    packVars (numericField (windowField pl H)) (patchVars p)=
      FanSlab.square F v (haloSite k h r p.1) (haloSite k w c p.2) := by
  let x := haloSite k h r p.1
  let y := haloSite k w c p.2
  let f (i : Fin 9) := marked F (L7.view v (35+42*u:Nat) (x+i.val/3:Nat) (y+i.val%3:Nat))
  change packVars (numericField (windowField pl H)) (patchVars p)=FanSlab.bits f
  have len : (patchVars p).length=9 := by simp [patchVars]
  have lt := packVars_lt (numericField (windowField pl H)) (patchVars p)
  rw [len] at lt
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i<9
  · let j : Fin 9 := ⟨i,hi⟩
    have packed := physical_patch_bit pl H p hr hc insidePatch j
    have ar (extent idx d off : Nat) :
        haloSite k extent idx (d+off)=haloSite k extent idx d+off := by
      unfold haloSite
      omega
    rw [ar,ar] at packed
    change (packVars (numericField (windowField pl H)) (patchVars p)).testBit i=f j at packed
    rw [packed]
    have word := (FanSlab.unpack f).2 j
    rw [lane_testBit] at word
    change ((FanSlab.bits f).testBit i).toNat=(f j).toNat at word
    exact (bool_of_toNat _ _ word).symm
  · have le : 2^9≤2^i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le lt le),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (FanSlab.unpack f).1 le)]

theorem physical_patch_encode {u k h w r c F v q dir} (pl : Placement u k h w r c)
    (H : PhysicalHalo u F v q dir) (p : Offset)
    (hr : p.1+2<18) (hc : p.2+2<18)
    (insidePatch : inside 117 (absAt (endTag h r) (endTag w c) p))
    (origin : origins (35+42*u))
    (atOrigin : coord origin=L7.view v ((↑(35+42*u):Int)-2)
      (haloSite k h r p.1) (haloSite k w c p.2)) :
    packVars (numericField (windowField pl H)) (patchVars p)=encode (maskAt F origin) v :=
  (physical_patch_square pl H p hr hc insidePatch).trans
    (FanSlab.square_eq F v _ _ origin atOrigin)

set_option maxHeartbeats 1600000 in
/-- Every complete numeric patch has an admissible mask of price
zero. The physical mask is reoriented before applying the atlas table. -/
theorem physical_patch_readout {u k h w r c F v q dir} (pl : Placement u k h w r c)
    (H : PhysicalHalo u F v q dir) (acy : (Bonds F).IsAcyclic) (p : Offset)
    (hr : p.1+2<18) (hc : p.2+2<18)
    (insidePatch : inside 117 (absAt (endTag h r) (endTag w c) p)) :
    let m := packVars (numericField (windowField pl H)) (patchVars p)
    maskOK m ∧ twoOrbitPatch 119 (absAt (endTag h r) (endTag w c) p) m=0 := by
  let x := haloSite k h r p.1
  let y := haloSite k w c p.2
  let X := atlasSite h r p.1
  let Y := atlasSite w c p.2
  have xy : absAt (endTag h r) (endTag w c) p = ((X:Int),(Y:Int)) := by
    simp only [X,Y,absAt,baseAt,atlasSite,Nat.cast_add]
  have inside' := insidePatch
  rw [xy] at inside'
  simp only [inside,Bool.and_eq_true,decide_eq_true_eq] at inside'
  have Xlt : X<117 := by omega
  have Ylt : Y<117 := by omega
  have gx := halo_origins pl.size pl.wide pl.height pl.row (d:=p.1) (by omega)
  have gy := halo_origins pl.size pl.wide pl.width pl.col (d:=p.2) (by omega)
  have xl : x<33+42*u := gx.1.mpr Xlt
  have yl : y<33+42*u := gy.1.mpr Ylt
  let n := 35+42*u
  have nn : (n:Int)-2=33+42*(u:Int) := by dsimp [n]; ring
  have b : inside (n-2:Nat) (L7.view v ((n:Int)-2) x y) := by
    have size : n-2=33+42*u := by dsimp [n]; omega
    have cast : ((n-2:Nat):Int)=(n:Int)-2 := by dsimp [n]; omega
    rw [←cast,size]
    exact inside_view (n:=33+42*u) (r:=x) (j:=y) v xl yl
  let a : origins n := onSite _ b
  have origin : coord a=L7.view v ((n:Int)-2) x y := coord_onSite ..
  have packed := physical_patch_encode pl H p hr hc insidePatch a origin
  dsimp only
  rw [xy,packed]
  constructor
  · apply patch_encode_mark_ok
    exact physical_mask_ok (n:=35+42*u) F acy a.1.val a.2.val
      (by have := a.1.isLt; omega) (by have := a.2.isLt; omega)
  · rw [patch_encode_price v 119 ((X:Int),(Y:Int))]
    have z : twoOrbitPatch (n:Int) (coord a) (maskAt F a)=0 := H.patches a
    rw [origin, nn] at z
    have transport := (atlas_prices (gx.2 xl) (gy.2 yl) v (maskAt F a) 0 0 4).1
    have ncast : (n:Int)=35+42*(u:Int) := by dsimp [n]
    rw [ncast] at z
    exact transport.symm.trans z

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
