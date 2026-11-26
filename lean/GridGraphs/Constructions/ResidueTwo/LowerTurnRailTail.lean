import GridGraphs.Constructions.ResidueTwo.LowerTurnCover

namespace GridGraphs.ResidueTwoLower.Poly

def widthExpr (base : Nat) : Exp := Exp.lit base+(42:ℤ)*Exp.t
def frontExpr (base : Nat) : Exp := Exp.lit ((base-2)/6 : Nat)+(7:ℤ)*Exp.t
def ordinaryRegion (base : Nat) :=
  railMask (widthExpr base) (frontExpr base) (3+frontExpr base) .i .j

theorem ordinary_covers (base t i j : Nat) (b : base=23 ∨ base=35 ∨ base=41 ∨ base=59)
    (hi : i<base+42*t) (hj : j<base+42*t)
    (h : marks (base+42*t) i j=true) :
    (ordinaryRegion base).eval t i j := by
  let n := base+42*t
  let k := (n-2)/3
  have side : n=3*k+2 := by dsimp [n,k]; rcases b with h|h|h|h <;> omega
  have phase : n%42 = base%42 := by dsimp [n]; omega
  have geom : marks n = railLayout n (k/2) 0 := by
    funext i j
    have skip : n≠26 ∧ n≠29 ∧ n≠32 := by dsimp [n]; rcases b with h|h|h|h <;> omega
    rcases b with h|h|h|h <;> subst base <;>
      simp [marks,zipper,skip.1,skip.2.1,skip.2.2,phase,show n%6=5 by dsimp [n]; omega,
        show (n-2)/6=k/2 by omega] <;> rfl
  change marks n i j=true at h
  rw [geom,side] at h
  have K : 6 ≤ k := by dsimp [k,n]; rcases b with h|h|h|h <;> omega
  have hi' : i<3*k+2 := by change i<n at hi; omega
  have hj' : j<3*k+2 := by change j<n at hj; omega
  have S := railMask_covers K (extra := 0) (by omega) hi' hj' h
  have wt : (widthExpr base).eval t i j = 3*(k:ℤ)+2 := by
    simp [widthExpr,Exp.eval]; dsimp [n] at side; omega
  have ff : (frontExpr base).eval t i j = ((k/2 : Nat):ℤ) := by
    simp [frontExpr,Exp.eval]; dsimp [n,k]; rcases b with h|h|h|h <;> omega
  -- All region operations depend only on the five evaluated coordinates.
  simpa only [ordinaryRegion,railMask,regMask,Region.eval,evalEq,evalLt,evalAdd,evalSub,
    evalMul,evalDiv,evalMod,wt,ff,eval0,eval1,evalOfNat,Exp.eval,Nat.cast_add,Nat.cast_ofNat,
    add_zero] using S

end GridGraphs.ResidueTwoLower.Poly
