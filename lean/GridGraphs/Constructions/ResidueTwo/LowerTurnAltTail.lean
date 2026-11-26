import GridGraphs.Constructions.ResidueTwo.LowerTurnWireTail

namespace GridGraphs.ResidueTwoLower.Poly
local infixr:32 " ⋎ " => Region.either
local infixr:34 " ⋏ " => Region.both
local infix:50 " ≐ " => eqE
local infix:50 " ≺ " => ltE
local infix:50 " ≽ " => Region.ge

def altBandRegion (l ph whole dir j : Exp) :=
  let del := (dir ≐ 0 ⋏ j ≐ l+4) ⋎ (dir ≐ 1 ⋏ j ≐ l)
  let ins := (dir ≐ 0 ⋏ j ≐ l+5) ⋎ (dir ≐ 1 ⋏ j ≐ l-1)
  (regMask l j ⋏ (ph ≺ 5 ⋎ whole ≺ 0 ⋎ del.notR)) ⋎ (ph ≐ 2 ⋏ j ≐ l+2) ⋎
    (whole ≽ 0 ⋏ ((ph ≐ 5 ⋏ j ≐ l+2) ⋎ (ph ≐ 6 ⋏ ins)))

def altRegion :=
  let n := widthExpr 56
  let f := frontExpr 56
  let i := Exp.i
  let j := Exp.j
  let st := f+2
  let len := n-5-st
  let u := (3:ℤ)*(i-2)
  let b : Exp := (i-st)/7
  let pos : Exp := (3:ℤ)*(f-1)+(3:ℤ)*((b%2):Exp)
  let l : Exp := (3:ℤ)*(f-1)+(3:ℤ)*(((len/7:Exp)%2):Exp)
  (i ≐ 0 ⋏ (j ≽ 3 ⋎ j ≐ 0)) ⋎ (i ≐ 1 ⋏ j ≐ 0) ⋎
  (i ≽ 2 ⋏ i ≺ st ⋏ (j ≐ 0 ⋎ (j ≺ u ⋏ j%3 ≐ 0) ⋎
    (j ≽ u+2 ⋏ j ≺ n-5-u ⋏ j%3 ≐ 2) ⋎ (j ≽ n-1-u ⋏ j%3 ≐ 1))) ⋎
  (i ≽ st ⋏ i ≺ n-5 ⋏ altBandRegion pos ((i-st)%7) (len-(7:ℤ)*(b+1:Exp)) (b%2) j) ⋎
  (i ≽ n-5 ⋏ i ≺ n-2 ⋏ ((l ≽ j ⋏ j%3 ≐ 0) ⋎ j ≐ n-1 ⋎
    (i ≐ n-5 ⋏ j ≐ l+2) ⋎ (i ≐ n-4 ⋏ j ≽ l+5 ⋏ j ≺ n-2) ⋎
    (i ≐ n-3 ⋏ j ≐ l+3))) ⋎ (i ≐ n-2 ⋏ j ≐ 0) ⋎ (i ≐ n-1 ⋏ (j ≐ 1).notR)

private theorem altBand {l ph j b len : Nat} (md : l%3=0) (lo : 1≤l) (mx : ph<7)
    (h : band l ph j (7*(b+1)≤len) (b%2==0)=true) :
    (altBandRegion (.lit l) (.lit ph) (.lit ((len:ℤ)-7*(b+1:ℤ))) (.lit (b%2:Nat)) (.lit j)).eval
      0 0 0 := by
  simp only [altBandRegion,regMask,Region.eval,evalEq,evalLt,evalAdd,evalSub,evalMod,
    eval0,eval1,evalOfNat,Exp.eval,Region.eval_notR]
  simp only [band,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
  split_ifs at h <;> simp [regular,leftRail,rightRail,bne] at h <;> omega

set_option maxHeartbeats 800000 in
theorem alternating_covers (t i j : Nat) (hi : i<56+42*t) (hj : j<56+42*t)
    (h : marks (56+42*t) i j=true) : altRegion.eval t i j := by
  let n := 56+42*t
  let f := 9+7*t
  let st := f+2
  have sz : (n-2)/6=f := by dsimp [n,f]; omega
  have geom : marks n i j=alternating n i j := by
    simp [marks,show n≠26 by dsimp [n]; omega,show n≠29 by dsimp [n]; omega,
      show n≠32 by dsimp [n]; omega,show n%42=14 by dsimp [n]; omega]
  change marks n i j=true at h
  rw [geom] at h
  have N : (widthExpr 56).eval t i j=(n:ℤ) := by simp [widthExpr,Exp.eval,n]
  have F : (frontExpr 56).eval t i j=(f:ℤ) := by simp [frontExpr,Exp.eval,f]
  simp only [altRegion,Region.eval,evalEq,evalLt,evalAdd,evalSub,evalMul,evalDiv,evalMod,
    eval0,eval1,evalOfNat,Exp.eval,Region.eval_notR,N,F,Nat.cast_ofNat,Nat.cast_one,Nat.cast_zero]
  simp only [alternating,Id.run,pure,beq_iff_eq,sz] at h
  split at h <;> rename_i top
  · left; simp at h; omega
  split at h <;> rename_i one
  · right; left; simp at h; omega
  split at h <;> rename_i front
  · right; right; left
    simp [altFront,rightRail] at h; dsimp [f,n] at *; omega
  split at h <;> rename_i mid
  · right; right; right; left
    refine ⟨by omega,by omega,?_⟩
    let b := (i-st)/7
    let ph := (i-st)%7
    let l := 3*(f-1)+3*(b%2)
    let len := n-7-f
    have hmin : min i (n-5)=i := Nat.min_eq_left (by omega)
    rw [hmin] at h
    change band l ph j (7*(b+1)≤len) (b%2==0)=true at h
    have P := altBand (l := l) (ph := ph) (by dsimp [l]; omega)
      (by dsimp [l,f]; omega) (Nat.mod_lt _ (by decide)) h
    simp only [altBandRegion,regMask,Region.eval,evalEq,evalLt,evalAdd,evalSub,evalMul,
      evalDiv,evalMod,eval0,eval1,evalOfNat,Exp.eval,Region.eval_notR,N,F,Nat.cast_ofNat,
      Nat.cast_one,Nat.cast_zero]
    simp only [altBandRegion,regMask,Region.eval,evalEq,evalLt,evalAdd,evalSub,evalMul,
      evalMod,eval0,eval1,evalOfNat,Exp.eval,Region.eval_notR,Nat.cast_ofNat,Nat.cast_one,
      Nat.cast_zero] at P
    have be : (b:ℤ)=((i:ℤ)-(f+2:ℤ))/7 := by dsimp [b,st]; omega
    have le : (l:ℤ)=3*((f:ℤ)-1)+3*((b:ℤ)%2) := by dsimp [l,f]; omega
    have pe : (ph:ℤ)=((i:ℤ)-(f+2:ℤ))%7 := by dsimp [ph,st]; omega
    have ln : (len:ℤ)=(n:ℤ)-5-((f:ℤ)+2) := by dsimp [len,n,f]; omega
    simpa only [←be,←le,←pe,←ln,show ((b%2:Nat):ℤ)=(b:ℤ)%2 by omega] using P
  · right; right; right; right
    have hmin : min i (n-5)=n-5 := Nat.min_eq_right (by omega)
    rw [hmin] at h
    let b := (n-5-st)/7
    let l := 3*(f-1)+3*(b%2)
    let row := i-(n-5)
    change altCap n l row j=true at h
    have be : (b:ℤ)=((n:ℤ)-5-(f+2:ℤ))/7 := by dsimp [b,st,n,f]; omega
    have le : (l:ℤ)=3*((f:ℤ)-1)+3*((b:ℤ)%2) := by dsimp [l,f]; omega
    rw [←be,←le]
    have r : row≤4 := by dsimp [row,n]; omega
    have re : i=n-5+row := by dsimp [row]; omega
    have big : 7≤n := by dsimp [n]; omega
    interval_cases row <;> simp [altCap,leftRail,bne] at h <;> omega

end GridGraphs.ResidueTwoLower.Poly
