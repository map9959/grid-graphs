import GridGraphs.Constructions.ResidueTwo.LowerTurnChartSound
import GridGraphs.Constructions.ResidueTwo.LowerZipper
import GridGraphs.Constructions.ResidueTwo.LowerTurnBandCover

namespace GridGraphs.ResidueTwoLower.Poly

instance (n : Nat) : OfNat Exp n := ⟨.lit n⟩
instance : Add Exp := ⟨.add⟩
instance : _root_.Sub Exp := ⟨fun a b => .add a (.mul (-1) b)⟩
instance : HMul ℤ Exp Exp := ⟨Exp.mul⟩
instance : HDiv Exp Nat Exp := ⟨fun a k => .div a k⟩
instance : HMod Exp Nat Exp := ⟨fun a k => .mod a k⟩

def eqE (a b : Exp) := Region.both (.ge a b) (.ge b a)
def ltE (a b : Exp) := Region.ge b (a+1)

@[simp] theorem eval_lit (x : Nat) (t i j) : Exp.eval t i j (.lit (x:ℤ)) = x := rfl
@[simp] theorem evalOfNat (x : Nat) [x.AtLeastTwo] (t i j) :
    Exp.eval t i j (OfNat.ofNat x) = (x:ℤ) := rfl
@[simp] theorem eval0 (t i j) : Exp.eval t i j 0 = 0 := rfl
@[simp] theorem eval1 (t i j) : Exp.eval t i j 1 = 1 := rfl
@[simp] theorem evalAdd (a b : Exp) (t i j) :
    (a+b).eval t i j = a.eval t i j + b.eval t i j := rfl
@[simp] theorem evalSub (a b : Exp) (t i j) :
    (a-b).eval t i j = a.eval t i j - b.eval t i j := by
  change _+(-1)*_=_; ring
@[simp] theorem evalMul (a : ℤ) (b : Exp) (t i j) :
    (a*b).eval t i j = a*b.eval t i j := rfl
@[simp] theorem evalDiv (b : Exp) (a : Nat) (t i j) :
    (b/a).eval t i j = b.eval t i j/a := rfl
@[simp] theorem evalMod (b : Exp) (a : Nat) (t i j) :
    (b%a).eval t i j = b.eval t i j%a := rfl
@[simp] theorem evalEq (a b : Exp) (t i j) :
    (eqE a b).eval t i j ↔ a.eval t i j=b.eval t i j := by simp [eqE,Region.eval]; omega
@[simp] theorem evalLt (a b : Exp) (t i j) :
    (ltE a b).eval t i j ↔ a.eval t i j<b.eval t i j := by simp [ltE,Region.eval]

local infixr:32 " ⋎ " => Region.either
local infixr:34 " ⋏ " => Region.both
local infix:50 " ≐ " => eqE
local infix:50 " ≺ " => ltE
local infix:50 " ≽ " => Region.ge

def regMask (l j : Exp) : Region :=
  (l ≽ j ⋏ j%3 ≐ 0) ⋎ (j ≽ l+4 ⋏ j%3 ≐ 1)

/-- Row layout before wire repair. On the ordinary tails `s=3+f`,
while on waiting-row tails `s=3+f+extra`. The physical side is `n`. -/
def railMask (n f s i j : Exp) : Region :=
  let u := (3:ℤ)*(i-3)
  let r := n-1-u
  let b := (i-s)/7
  let len := n-5-s
  let l := (3:ℤ)*(f-b)
  let ph := (i-s)%7
  let M := (3:ℤ)*(f-len/7)
  (i ≐ 0 ⋏ (j ≺ n-3 ⋎ j ≐ n-1)) ⋎ (i ≐ 1 ⋏ j ≐ n-1) ⋎
    (i ≐ 2 ⋏ (j%3 ≐ 2 ⋎ j ≐ n-1)) ⋎
    (i ≽ 3 ⋏ i ≺ 3+f ⋏ ((u ≽ j ⋏ j%3 ≐ 0) ⋎ (j ≽ r ⋏ j%3 ≐ 1) ⋎
      (j%3 ≐ 2 ⋏ j ≽ u+5 ⋏ j ≺ r-4))) ⋎
    (i ≽ 3+f ⋏ i ≺ s ⋏ regMask ((3:ℤ)*f) j) ⋎
    (i ≽ s ⋏ i ≺ n-5 ⋏
      ((regMask l j ⋏ (ph ≺ 5 ⋎ len ≺ (7:ℤ)*(b+1) ⋎ j ≺ l ⋎ l ≺ j)) ⋎
       (ph ≐ 2 ⋏ j ≐ l+2) ⋎
       (len ≽ (7:ℤ)*(b+1) ⋏ ((ph ≐ 5 ⋏ j ≐ l+2) ⋎ (ph ≐ 6 ⋏ j ≐ l-1))))) ⋎
    (i ≽ n-5 ⋏ i ≺ n-2 ⋏ ((M-6 ≽ j ⋏ j%3 ≐ 0) ⋎ (j ≽ M+4 ⋏ j%3 ≐ 1) ⋎
      (i ≐ n-5 ⋏ j ≐ M+2) ⋎ (i ≐ n-4 ⋏ j ≽ M-4 ⋏ j ≺ M) ⋎
      (i ≐ n-3 ⋏ j ≐ M+1))) ⋎ i ≐ n-1

set_option maxHeartbeats 1000000 in
/-- Every marked site in the unrepaired layout is in the indicated integer
region. Bounds on the tip ensure natural subtraction agrees with integer
subtraction wherever the term occurs on an active row. -/
theorem railMask_covers {k i j extra : Nat} (hk : 6≤k) (he : extra≤2)
    (hi : i<3*k+2) (hj : j<3*k+2)
    (h : railLayout (3*k+2) (k/2) extra i j=true) :
    (railMask (.lit (3*k+2)) (.lit (k/2 : Nat)) (.lit (3+k/2+extra : Nat)) .i .j).eval
      0 i j := by
  let n := 3*k+2
  let f := k/2
  let st := 3+f+extra
  let len := n-5-st
  change railLayout n f extra i j=true at h
  simp only [railMask,regMask,Region.eval,evalEq,evalLt,evalAdd,evalSub,evalMul,evalDiv,evalMod,
    eval0,eval1,evalOfNat,Exp.eval,Nat.cast_add,Nat.cast_ofNat]
  rw [show ((k/2:Nat):ℤ)=(k:ℤ)/2 by omega]
  simp only [railLayout,Id.run,pure,beq_iff_eq] at h
  split at h <;> rename_i h0
  · left; simp at h; dsimp [n,f,st,len] at *; omega
  split at h <;> rename_i h1
  · right; left; simp at h; dsimp [n,f,st,len] at *; omega
  split at h <;> rename_i h2
  · right; right; left; simp at h; dsimp [n,f,st,len] at *; omega
  split at h <;> rename_i front
  · right; right; right; left; simp [leftRail,rightRail] at h
    dsimp [n,f,st,len] at *; omega
  split at h <;> rename_i wait
  · right; right; right; right; left; simp [regular,leftRail,rightRail] at h
    dsimp [n,f,st,len] at *; omega
  split at h <;> rename_i capRow
  · right; right; right; right; right; right
    have length : ((n-5-st:Nat):ℤ)=(3*(k:ℤ)+2-5)-(3+(k:ℤ)/2+extra) := by
      dsimp [n,st,f]; omega
    let M := 3*f-3*(len/7)
    have ML : 6 ≤ M := by dsimp [M,len,n,st,f]; omega
    have Me : (M:ℤ)=3*((k:ℤ)/2-(3*k+2-5-(3+(k:ℤ)/2+extra))/7) := by
      dsimp [M,len,n,st,f] at *; omega
    rw [←Me]
    change cap M (i-(n-5)) j=true at h
    let row := i-(n-5)
    have rowE : i=n-5+row := by dsimp [row]; omega
    have rle : row≤4 := by dsimp [row,n]; omega
    change cap M row j=true at h
    have md : M%3=0 := by dsimp [M]; omega
    dsimp [n] at rowE
    interval_cases row <;> simp [cap,leftRail,rightRail] at h <;> omega
  · right; right; right; right; right; left
    have shift : ((i-st:Nat):ℤ)=(i:ℤ)-(3+(k:ℤ)/2+extra) := by dsimp [st,f] at *; omega
    have length : ((n-5-st:Nat):ℤ)=(3*(k:ℤ)+2-5)-(3+(k:ℤ)/2+extra) := by
      dsimp [n,st,f]; omega
    let b := (i-st)/7
    let l := 3*f-3*b
    let ph := (i-st)%7
    have Le : (l:ℤ)=3*((k:ℤ)/2-((i:ℤ)-(3+(k:ℤ)/2+extra))/7) := by
      dsimp [l,b,f,st,n] at *; omega
    have Ph : (ph:ℤ)=((i:ℤ)-(3+(k:ℤ)/2+extra))%7 := by dsimp [ph]; omega
    have Be : (b:ℤ)=((i:ℤ)-(3+(k:ℤ)/2+extra))/7 := by dsimp [b]; omega
    have md : l%3=0 := by dsimp [l]; omega
    have mx : ph<7 := Nat.mod_lt _ (by decide)
    have lo : 1≤l := by dsimp [l,f,b,st,n] at *; omega
    rw [←Le,←Ph,←Be,←length]
    constructor
    · dsimp [f] at wait; omega
    constructor
    · dsimp [n] at capRow; omega
    change band l ph j (7*(b+1)≤len) false=true at h
    exact int_band_cover lo md mx h

end GridGraphs.ResidueTwoLower.Poly
