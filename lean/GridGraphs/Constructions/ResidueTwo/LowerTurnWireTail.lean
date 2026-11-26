import GridGraphs.Constructions.ResidueTwo.LowerTurnRailTail

namespace GridGraphs.ResidueTwoLower.Poly

def Region.notR : Region → Region
  | .yes => .no | .no => .yes | .ge a b => ltE a b
  | .both a b => .either a.notR b.notR | .either a b => .both a.notR b.notR

@[simp] theorem Region.eval_notR (p : Region) (t i j) :
    p.notR.eval t i j ↔ ¬p.eval t i j := by
  induction p <;> simp_all [notR,Region.eval] <;> tauto

def wireRegion (m i j : Exp) (old : Region) : Region :=
  let l := (3:ℤ)*(i-2)
  let ins := Region.either (.both (eqE i 1) (eqE j 0))
    (.both (.ge i 2) (.both (.ge m l) (eqE j l)))
  let del := Region.either (.both (eqE i 0) (eqE j 1))
    (.both (.ge i 2) (.both (ltE l m) (eqE j (l+2))))
  .either ins (.both old del.notR)

theorem wireRegion_covers {m i j : Nat} {old : Bool} (h : wireEdit m i j old = true)
    {r : Region} {t : ℤ} {M : Exp} (he : M.eval t i j=m)
    (hr : old=true → r.eval t i j) : (wireRegion M .i .j r).eval t i j := by
  simp only [wireRegion,Region.eval,evalEq,evalLt,Region.eval_notR,evalAdd,evalSub,evalMul,
    eval0,eval1,evalOfNat,Exp.eval,he]
  simp only [wireEdit,Id.run,pure,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
  split_ifs at h <;> simp_all <;> omega

def waits (base : Nat) : Nat :=
  if base=38 ∨ base=71 then 1 else if base=47 then 2 else 0

def repairTip (base : Nat) : Exp :=
  if base%6=2 then (3:ℤ)*frontExpr base
  else Exp.lit (if base=71 then 12 else 9)+(6:ℤ)*Exp.t

def repairedRegion (base : Nat) :=
  wireRegion (repairTip base) .i .j
    (railMask (widthExpr base) (frontExpr base)
      (3+frontExpr base+Exp.lit (waits base)) .i .j)

def repairedBase (base : Nat) : Prop :=
  base=38 ∨ base=44 ∨ base=47 ∨ base=50 ∨ base=53 ∨ base=62 ∨ base=68 ∨ base=71 ∨ base=74

theorem repaired_covers (base t i j : Nat) (b : repairedBase base)
    (hi : i<base+42*t) (hj : j<base+42*t)
    (h : marks (base+42*t) i j=true) :
    (repairedRegion base).eval t i j := by
  let n := base+42*t
  let k := (n-2)/3
  let stop := if base%6=2 then 3*(k/2) else if base=71 then 12+6*t else 9+6*t
  have B : 38≤base ∧ base≤74 ∧ base%3=2 := by unfold repairedBase at b; omega
  have side : n=3*k+2 := by dsimp [n,k]; omega
  have phase : n%42=base%42 := by dsimp [n]; omega
  have par : n%6=base%6 := by dsimp [n]; omega
  have wt : (widthExpr base).eval t i j = 3*(k:ℤ)+2 := by
    simp [widthExpr,Exp.eval]; dsimp [n] at side; omega
  have ff : (frontExpr base).eval t i j = ((k/2:Nat):ℤ) := by
    simp [frontExpr,Exp.eval]; dsimp [n,k]; omega
  have tip : (repairTip base).eval t i j=stop := by
    unfold repairTip stop
    split <;> simp [ff,Exp.eval] <;> split_ifs <;> omega
  have geom : marks n i j = wireEdit stop i j (railLayout n (k/2) (waits base) i j) := by
    have skip : n≠26 ∧ n≠29 ∧ n≠32 := by dsimp [n]; omega
    unfold repairedBase at b
    rcases b with b|b|b|b|b|b|b|b|b <;> subst base <;>
      simp [marks,zipper,skip.1,skip.2.1,skip.2.2,phase,par,stop,waits,
        show (n-2)/6=k/2 by omega] <;> congr 1 <;> dsimp [n] <;> omega
  change marks n i j=true at h
  rw [geom] at h
  apply wireRegion_covers h tip
  intro old
  have K : 6≤k := by dsimp [k,n]; omega
  have E : waits base≤2 := by unfold waits; split_ifs <;> omega
  rw [side] at old
  have S := railMask_covers K E (i := i) (j := j) (by change i<n at hi; omega)
    (by change j<n at hj; omega) old
  simpa only [railMask,regMask,Region.eval,evalEq,evalLt,evalAdd,evalSub,evalMul,evalDiv,evalMod,
    wt,ff,eval0,eval1,evalOfNat,Exp.eval,Nat.cast_add,Nat.cast_ofNat] using S

end GridGraphs.ResidueTwoLower.Poly
