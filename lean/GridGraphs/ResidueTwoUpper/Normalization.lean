import GridGraphs.ResidueTwoUpper.PhysicalCounts

/-! Count actual physical positions of each fine type. A three-site
insertion after the near collar adds exactly one of each bulk phase, so
the products below hold at every width without fitting a quadratic. -/
namespace GridGraphs.ResidueTwoUpper.Normalization
open Location Finset

def axisMass (d t z : Nat) : Int :=
  if z<d then 1 else if z<d+2 then 3+t else if z=d+2 then 2+t else if z<2*d+3 then 1 else 0

private theorem grow_near {d t i : Nat} (h : i<d) :
    axis (2*d+8+3*(t+1)) d i=axis (2*d+8+3*t) d i := by simp [axis,h]

private theorem grow_tail {d t i : Nat} (h : d ≤ i) :
    axis (2*d+8+3*(t+1)) d (i+3)=axis (2*d+8+3*t) d i := by
  simp only [axis]; split_ifs <;> omega

private theorem grow_new {d t j : Nat} (h : j<3) :
    axis (2*d+8+3*(t+1)) d (d+j)=d+j := by simp only [axis]; split_ifs <;> omega

def occurrences (d t z : Nat) : Int :=
  ∑ i ∈ range (2*d+8+3*t), if axis (2*d+8+3*t) d i=z then 1 else 0

private theorem recurrence (d t z : Nat) :
    occurrences d (t+1) z = occurrences d t z + if d≤z ∧ z<d+3 then 1 else 0 := by
  let h := d+8+3*t
  have big : 2*d+8+3*(t+1) = d+(3+h) := by dsimp [h]; omega
  have small : 2*d+8+3*t = d+h := by dsimp [h]; omega
  unfold occurrences
  conv_lhs => lhs; rw [big]
  conv_rhs => lhs; lhs; rw [small]
  simp only [sum_range_add]
  have near := sum_congr (s₁:=range d) rfl (fun i (hi : i ∈ range d) =>
    congrArg (fun a => if a=z then (1:Int) else 0) (grow_near (t:=t) (mem_range.mp hi)))
  rw [near]
  have tail (j : Nat) : axis (2*d+8+3*(t+1)) d (d+(3+j))=axis (2*d+8+3*t) d (d+j) := by
    rw [show d+(3+j)=d+j+3 by omega,grow_tail (by omega)]
  simp_rw [tail]
  have new := sum_congr (s₁:=range 3) rfl (fun j (hj : j ∈ range 3) =>
    congrArg (fun a => if a=z then (1:Int) else 0) (grow_new (d:=d) (t:=t) (mem_range.mp hj)))
  rw [new]
  simp only [sum_range_succ,sum_range_zero,zero_add,Nat.add_zero]
  split_ifs <;> omega

private theorem type_lt {d t i} (h : i<2*d+8+3*t) : axis (2*d+8+3*t) d i <2*d+3 := by
  unfold axis; split_ifs <;> omega

theorem count_axis {d} (hd : d=5 ∨ d=6) (t z) : occurrences d t z = axisMass d t z := by
  induction t with
  | zero =>
    by_cases hz : z<2*d+3
    · rcases hd with rfl|rfl <;> interval_cases z <;> decide
    · have empty (i) (mem : i ∈ range (2*d+8+3*0)) :
          (if axis (2*d+8+3*0) d i=z then (1:Int) else 0)=0 := by
        have := type_lt (mem_range.mp mem); split_ifs <;> omega
      rw [occurrences,sum_eq_zero empty]
      simp only [axisMass]; split_ifs <;> omega
  | succ t ih =>
    rw [recurrence,ih]; unfold axisMass; split_ifs <;> omega

theorem count_locations {d} (hd : d=5 ∨ d=6) (t u v) :
    (∑ p : GridVertex (2*d+8+3*t) (2*d+8+3*t),
      if axis (2*d+8+3*t) d p.1=u ∧ axis (2*d+8+3*t) d p.2=v then (1:Int) else 0) =
      axisMass d t u * axisMass d t v := by
  rw [←count_axis hd t u,←count_axis hd t v,Fintype.sum_prod_type]
  unfold occurrences
  rw [←Fin.sum_univ_eq_sum_range,←Fin.sum_univ_eq_sum_range,sum_mul]
  apply sum_congr rfl; intro i _; rw [mul_sum]; apply sum_congr rfl; intro j _
  split_ifs <;> simp_all

end GridGraphs.ResidueTwoUpper.Normalization
