import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStripPhysicalRun

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
open ResidueZero L7 FanSlab
namespace GridScan

private theorem toNat_one (b : Bool) : (b.toNat==1)=b := by cases b <;> rfl

/-- Tile line `line` is in untransposed catalogue coordinates. Extract
the bit in scan substep `phase` and transverse physical slot `i`. -/
def lineMark (axis : Axis) (line : Nat → Nat) (phase i : Nat) : Bool :=
  let b := match axis with
    | .horizontal => 3*(i%3)+phase
    | .vertical => 3*phase+i%3
  bit (line (i/3)) b==1

/-- The marks read by the packed run are exactly the bits of the same
four-word field used in catalogue admission. -/
theorem lineMark_physical {u h : Nat} (s : Window h (width h)) (F : Finset (Site u))
    (v : View) (north : Bool) (j : Nat) (i : Fin (3*s.depth)) :
    lineMark s.axis (band (cropTiles F v (11+14*u) h) s.axis s.start (j/3)) (j%3) i =
      (physicalProgram s F v north).mark j i := by
  let k := 11+14*u
  let n := 35+42*u
  cases ax : s.axis with
  | horizontal =>
    let r := firstRow k h+3*(s.start+i.val/3)
    let c := firstCol k h+3*(j/3)
    let f (b : Fin 9) := marked F (L7.view v (n:Nat) (r+b.val/3:Nat) (c+b.val%3:Nat))
    let b : Fin 9 := ⟨3*(i.val%3)+j%3,by omega⟩
    have eq := (unpack f).2 b
    change bit (bits f) b=(f b).toNat at eq
    simp only [lineMark,band,cropTiles,cell,physicalProgram,ax,scanPoint,prefixBox,
      FanBoot.Camera.bitAt]
    change (bit (bits f) b==1) = marked F (L7.view v (n:Nat)
      (((firstRow k h+3*s.start:Nat):Int)+i.val) ((firstCol k h:Int)+j))
    rw [eq]
    have row : (r+b.val/3:Nat)=firstRow k h+3*s.start+i.val := by dsimp [r,b]; omega
    have col : (c+b.val%3:Nat)=firstCol k h+j := by dsimp [c,b]; omega
    simp only [f,toNat_one]
    simpa only [Nat.cast_add] using
      congrArg₂ (fun x y : Nat => marked F (L7.view v (n:Nat) x y)) row col
  | vertical =>
    let r := firstRow k h+3*(j/3)
    let c := firstCol k h+3*(s.start+i.val/3)
    let f (b : Fin 9) := marked F (L7.view v (n:Nat) (r+b.val/3:Nat) (c+b.val%3:Nat))
    let b : Fin 9 := ⟨3*(j%3)+i.val%3,by omega⟩
    have eq := (unpack f).2 b
    change bit (bits f) b=(f b).toNat at eq
    simp only [lineMark,band,cropTiles,cell,physicalProgram,ax,scanPoint,prefixBox,
      FanBoot.Camera.bitAt]
    change (bit (bits f) b==1) = marked F (L7.view v (n:Nat)
      ((firstRow k h:Int)+j) (((firstCol k h+3*s.start:Nat):Int)+i.val))
    rw [eq]
    have row : (r+b.val/3:Nat)=firstRow k h+j := by dsimp [r,b]; omega
    have col : (c+b.val%3:Nat)=firstCol k h+3*s.start+i.val := by dsimp [c,b]; omega
    simp only [f,toNat_one]
    simpa only [Nat.cast_add] using
      congrArg₂ (fun x y : Nat => marked F (L7.view v (n:Nat) x y)) row col

end GridScan
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
