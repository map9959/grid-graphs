import GridGraphs.NoPitch.Certificate

/-! The unrestricted period-three overlap dual of
`docs/UNRESTRICTED_PERIOD_THREE_UPPER.md`. This chart has neither fixed atoms
nor residual allowances. The score bound is for feasible chart counts;
constructing those counts from an arbitrary forced forest is a separate step. -/

namespace GridGraphs.ResidueTwoUpper
open NoPitch.Dual

def periodThree := decode (include_str "Data/periodThree.v32")

def chartCheck (D : Chart) :=
  let p := rhsSum D
  let s : Int := D.scale
  D.rows.size == 517 && D.cols.size == 3549 && 0 < D.scale &&
    D.rows.all signOK && D.cols.all (fun col => !col.fixed) && repair D == 0 &&
    7*p.a == 2111*s && 7*p.b == 600*s && p.c == 6*s

theorem periodThree_checked : chartCheck periodThree = true := by native_decide

/-- With `n = 20+3t`, the exact rational dual price is
`(2111+600t+42t²)/14`. The factor of eight in `obj` allows integer orbit
counts for an arbitrary (not necessarily symmetric) input. -/
theorem rational_upper {t M : Nat} {x cap}
    (h : Feasible periodThree x 8 t cap) (obj : score periodThree x = 8*(M:Int)) :
    14*(M:Int) ≤ 2111 + 600*(t:Int) + 42*(t:Int)^2 := by
  have ok := periodThree_checked
  simp only [chartCheck,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at ok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨_,_⟩,pos⟩,sgn⟩,_⟩,noErr⟩,a⟩,b⟩,c⟩ := ok
  have ub := replay_bound _ h sgn
  rw [obj,noErr,mul_zero,add_zero] at ub
  have eq : 7*(rhsSum periodThree).atStep t = (periodThree.scale:Int)*
      (2111+600*(t:Int)+42*(t:Int)^2) := by
    unfold Poly.atStep
    linear_combination a + (t:Int)*b + 7*(t:Int)^2*c
  apply le_of_mul_le_mul_left (a := (periodThree.scale:Int)) _ (by positivity)
  linarith only [eq,ub]

/-- In `n=3k+2` coordinates this loses one mark every seven steps,
starting at `k=12`. On the exceptional progression it leaves one extra. -/
theorem integer_upper {k M : Nat} (hk : 6 ≤ k) {x cap}
    (h : Feasible periodThree x 8 ((k-6 : Nat):Int) cap)
    (obj : score periodThree x = 8*(M:Int)) :
    M ≤ 3*k^2+7*k-(k-5)/7 := by
  have ub := rational_upper h obj
  have et : ((k-6 : Nat):Int) = (k:Int)-6 := by omega
  rw [et] at ub
  ring_nf at ub
  have divi : 7*((((k-5)/7 : Nat):Int)) ≤ (k:Int)-5 := by omega
  have goal : (M:Int)+((k-5)/7 : Nat) ≤ 3*(k:Int)^2+7*k := by omega
  have natGoal : M+(k-5)/7 ≤ 3*k^2+7*k := by exact_mod_cast goal
  omega

end GridGraphs.ResidueTwoUpper
