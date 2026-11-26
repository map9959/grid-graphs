import GridGraphs.NoPitch.Certificate

namespace GridGraphs.NoPitch.Dual

theorem verified58 : tailCheck chart58 19 = true := by native_decide
theorem verified61 : tailCheck chart61 20 = true := by native_decide
theorem verified19 : finiteCheck chart19 19 = true := by native_decide
theorem verified22 : finiteCheck chart22 22 = true := by native_decide
theorem verified25 : finiteCheck chart25 25 = true := by native_decide
theorem verified52 : finiteCheck chart52 52 = true := by native_decide

private theorem comb_round {k M : Nat} (hk : 5≤k)
    (price : 64*(M:Int) ≤ 192*(k:Int)^2+336*k-79) : M ≤ squareScore (3*k+1) := by
  rw [squareScore_three_mul_add_one k (by omega)]
  zify [show 13≤3*k by omega]
  omega

/-- Integer upper at every tail width for a chart-feasible orbit-count
vector. The row predicates in `Feasible` have not been postulated for trees. -/
theorem certified_tail {k M : Nat} (hk : 19≤k) (cap : Int)
    (physical : if k%2=1 then
      ∃ x, Feasible chart58 x 8 ((k-19)/2 : Nat) cap ∧ score chart58 x=8*(M:Int)
      else ∃ x, Feasible chart61 x 8 ((k-19)/2 : Nat) cap ∧ score chart61 x=8*(M:Int)) :
    M ≤ squareScore (3*k+1) := by
  apply comb_round (by omega)
  by_cases odd : k%2=1
  · simp only [if_pos odd] at physical
    obtain ⟨x,f,score⟩ := physical
    have h := tail_bound chart58 19 verified58 (t:=(k-19)/2) (cap:=cap) (M:=M) (x:=x) f score
    have eq : (19:ℤ)+2*((((k-19)/2 : Nat):Int))=k := by omega
    rw [eq] at h; exact h
  · simp only [if_neg odd] at physical
    obtain ⟨x,f,score⟩ := physical
    have h := tail_bound chart61 20 verified61 (t:=(k-19)/2) (cap:=cap) (M:=M) (x:=x) f score
    have eq : (20:ℤ)+2*((((k-19)/2 : Nat):Int))=k := by omega
    rw [eq] at h; exact h

end GridGraphs.NoPitch.Dual
