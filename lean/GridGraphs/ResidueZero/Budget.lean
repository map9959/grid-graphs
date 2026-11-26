import GridGraphs.ResidueZero.Stencil

namespace GridGraphs.ResidueZero
open Finset

def axisSum (s d : Nat) (f : Int → Int) := ∑ i ∈ range s, f (axis s d i)
def extra (d : Nat) (f : Int → Int) := ∑ i ∈ range 3, f (axis 21 d (6+i:Nat))

private theorem insert_three {s d : Nat} (hs : 19≤s) (hd : 5≤d ∧ d≤6) (f : Int → Int) :
    axisSum (s+3) d f = axisSum s d f + extra d f := by
  let a := s-6
  have ha : s=6+a := by dsimp [a]; omega
  have hb : s+3=6+(3+a) := by omega
  unfold axisSum extra
  conv_lhs => arg 1; rw [hb]
  rw [sum_range_add]
  conv_rhs => lhs; arg 1; rw [ha]
  rw [sum_range_add, sum_range_add]
  have left : ∀ i∈range 6, axis (↑(s+3)) d (i:Nat)=axis s d i := by
    intro i hi; simp only [mem_range] at hi
    unfold axis; push_cast; split_ifs <;> omega
  have middle : ∀ i∈range 3, axis (↑(s+3)) d (6+i:Nat)=axis 21 d (6+i:Nat) := by
    intro i hi; simp only [mem_range] at hi
    unfold axis; push_cast; split_ifs <;> omega
  have right : ∀ i∈range a, axis (↑(s+3)) d (6+(3+i):Nat)=axis s d (6+i:Nat) := by
    intro i hi; simp only [mem_range] at hi
    unfold axis; push_cast; split_ifs <;> omega
  rw [sum_congr rfl (fun i hi => congrArg f (left i hi)),
      sum_congr rfl (fun i hi => congrArg f (middle i hi)),
      sum_congr rfl (fun i hi => congrArg f (right i hi))]
  ring

theorem axisSum_width {b d : Nat} (hb : 19≤b) (hd : 5≤d ∧ d≤6)
    (f : Int → Int) (j : Nat) :
    axisSum (b+3*j) d f = axisSum b d f + (j:Int)*extra d f := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.mul_succ,← Nat.add_assoc,insert_three (by omega) hd,ih]
    push_cast; ring

def plane (s d : Nat) (price : Int → Int → Int) :=
  axisSum s d fun i => axisSum s d (price i)

def charge (table : Std.HashMap Nat Int) (i t : Int) := table.getD (i.toNat*16+t.toNat) 0
def normBudget (n : Nat) :=
  plane n 6 (charge starNormPrices) + plane (n-2) 5 (charge patchNormPrices) +
    cornerPrices.getD 0 0

private theorem plane_width {b d : Nat} (hb : 19≤b) (hd : 5≤d ∧ d≤6)
    (f : Int → Int → Int) (j : Nat) :
    plane (b+3*j) d f = plane b d f +
      j*(axisSum b d (fun i => extra d (f i)) + extra d (fun i => axisSum b d (f i))) +
      (j:Int)^2*extra d (fun i => extra d (f i)) := by
  unfold plane
  simp_rw [axisSum_width hb hd]
  simp only [axisSum,extra,Finset.sum_add_distrib,← Finset.mul_sum]
  ring

private def linear (b d : Nat) (f : Int → Int → Int) :=
  axisSum b d (fun i => extra d (f i)) + extra d (fun i => axisSum b d (f i))
private def quadratic (d : Nat) (f : Int → Int → Int) := extra d (fun i => extra d (f i))

theorem budget_width (j : Nat) :
    normBudget (21+3*j) = scale*(166+45*(j:Int)+3*j^2) := by
  have c₀ : normBudget 21 = scale*166 := by native_decide
  have c₁ : linear 21 6 (charge starNormPrices)+linear 19 5 (charge patchNormPrices) =
      scale*45 := by native_decide
  have c₂ : quadratic 6 (charge starNormPrices)+quadratic 5 (charge patchNormPrices) =
      scale*3 := by native_decide
  unfold normBudget at c₀ ⊢
  rw [show 21+3*j-2=19+3*j by omega,plane_width (by decide) (by decide),
    plane_width (by decide) (by decide)]
  unfold linear at c₁; unfold quadratic at c₂
  linear_combination c₀ + (j:Int)*c₁ + (j:Int)^2*c₂

theorem smallBudgets : normBudget 12 = scale*58 ∧ normBudget 15 = scale*88 ∧
    normBudget 18 = scale*124 := by native_decide

end GridGraphs.ResidueZero
