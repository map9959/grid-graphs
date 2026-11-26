import GridGraphs.ResidueTwoUpper.OneGap.SouthCapPhysicalRim
import GridGraphs.Tests.SouthCapCubeShape

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
open ResidueZero Stencil L7

theorem packVars_lt (a : Nat → Bool) (vs : List Nat) :
    packVars a vs < 2 ^ vs.length := by
  induction vs with
  | nil => simp [packVars]
  | cons x xs ih =>
    simp only [packVars,List.length_cons,pow_succ]
    cases a x <;> simp <;> omega

/-- Bit `i` of a complete patch reads the actual physical mark at its
row-major offset in the fan view. -/
theorem physical_patch_bit {u k h w r c F v q dir} (pl : Placement u k h w r c)
    (H : PhysicalHalo u F v q dir) (p : Offset)
    (hr : p.1+2<18) (hc : p.2+2<18)
    (insidePatch : inside 117 (absAt (endTag h r) (endTag w c) p)) (i : Fin 9) :
    (packVars (numericField (windowField pl H)) (patchVars p)).testBit i =
      marked F (L7.view v (35+42*u:Nat)
        (haloSite k h r (p.1+i.val/3)) (haloSite k w c (p.2+i.val%3))) := by
  let p' : Offset := (p.1+i.val/3,p.2+i.val%3)
  have ilt := i.isLt
  have fit : fits p' := by constructor <;> dsimp [p'] <;> omega
  have board : onBoard (endTag h r) (endTag w c) p' := by
    apply (onBoard_iff p').mpr
    simp only [inside,absAt,Bool.and_eq_true] at insidePatch
    have bx : (baseAt (endTag h r):Int)+p.1<117 :=
      of_decide_eq_true insidePatch.1.1.2
    have by' : (baseAt (endTag w c):Int)+p.2<117 :=
      of_decide_eq_true insidePatch.2
    change baseAt (endTag h r)+(p.1+i.val/3)<119 ∧
      baseAt (endTag w c)+(p.2+i.val%3)<119
    constructor <;> omega
  let s : Slots h w r c := slot p' fit board
  have idx : i.val < (patchVars p).length := by simp [patchVars]
  rw [packVars_bit _ _ _ idx]
  have varEq : (patchVars p)[i.val] = markVar p' := by
    simp [patchVars,p']
  rw [varEq]
  change numericField (windowField pl H) (wireNumber s.1.1.val s.1.2.val 0)=_
  rw [numeric_mark]
  have eq := pl.point_coord v s
  change coord (pl.point v s)=L7.view v (35+42*u:Nat)
    (haloSite k h r p'.1) (haloSite k w c p'.2) at eq
  change (windowField pl H).mark s=marked F (L7.view v (35+42*u:Nat)
    (haloSite k h r p'.1) (haloSite k w c p'.2))
  rw [←eq,marked_at]
  rfl

private theorem patchIndexCheck : ∀ x : Fin 29,
    let y : Int := ((88+x.val : Nat) : Int)
    patchIx y < 9 ∧ rep 21 32 y=(patchReps[patchIx y]! : Int) := by decide +kernel

private theorem patchIndex {x : Nat} (lo : 88≤x) (hi : x<117) :
    patchIx x < 9 ∧ rep 21 32 x=(patchReps[patchIx x]! : Int) := by
  have h := patchIndexCheck ⟨x-88,by omega⟩
  dsimp only at h
  rwa [show 88+(x-88)=x by omega] at h

/-- Apply the audited patch cubes at the precise indices used in
`clauseRows`. Its two inputs concern the packed numeric marks, not
an independently chosen patch mask. -/
theorem atlas_patch_row_law {h w r c : Nat} (hr : r+2≤h) (hc : c+2≤w)
    (p : Offset) (a : Nat → Bool) (insidePatch : inside 117 (absAt (endTag h r) (endTag w c) p))
    (ok : maskOK (packVars a (patchVars p)))
    (zero : twoOrbitPatch 119 (absAt (endTag h r) (endTag w c) p)
      (packVars a (patchVars p)) = 0) :
    let z := absAt (endTag h r) (endTag w c) p
    let row := patchCubes (patchIx z.1) (patchIx z.2)
    rejects row (packVars a (patchVars p))=false ∧
      (∀ b∈row, b%512<2^(patchVars p).length ∧ (b/512 &&& b%512)=b/512) := by
  let X := atlasSite h r p.1
  let Y := atlasSite w c p.2
  have xy : absAt (endTag h r) (endTag w c) p = ((X:Int),(Y:Int)) := by
    simp only [X,Y,absAt,baseAt,atlasSite,Nat.cast_add]
  rw [xy] at insidePatch zero ⊢
  have hx : X<117 := by
    simp only [ResidueZero.inside,Bool.and_eq_true,decide_eq_true_eq] at insidePatch
    omega
  have hy : Y<117 := by
    simp only [ResidueZero.inside,Bool.and_eq_true,decide_eq_true_eq] at insidePatch
    omega
  have ix := patchIndex (atlasSite_ge88 hr : 88≤X) hx
  have iy := patchIndex (atlasSite_ge88 hc : 88≤Y) hy
  let i : Fin 9 := ⟨patchIx X,ix.1⟩
  let j : Fin 9 := ⟨patchIx Y,iy.1⟩
  have rp : representative 21 32 ((X:Int),(Y:Int))=pricePoint patchReps i j :=
    Prod.ext ix.2 iy.2
  have len : (patchVars p).length=9 := by simp [patchVars]
  have lt := packVars_lt a (patchVars p)
  rw [len] at lt
  constructor
  · have h := atlas_patch_reject i j rp lt
    simpa [ok,zero] using h
  · intro b hb
    rw [len]
    exact patch_cube_shape i j b hb

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap
