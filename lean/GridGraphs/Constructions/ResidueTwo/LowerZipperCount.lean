import GridGraphs.Constructions.ResidueTwo.LowerZipper

namespace GridGraphs.ResidueTwoLower

/-- Row ledger: a row in the middle has `k+1` marks, and the third
row of each band has one extra, including a sufficiently long partial band. -/
def zipperLedger (k : Nat) : Nat :=
  let n := 3*k+2
  let f := k/2
  let e := if n%42 = 38 ∨ n%42 = 29 then 1 else if n%42 = 5 then 2 else 0
  if n%42 = 14 then
    let len := n-7-f
    n-1 + (f*k+1) + len*(k+1) + (len+4)/7 + (2*n+1)
  else
    let len := n-8-f
    n+k + f*k + len*(k+1) + (len-e+4)/7 + (3*k+3+n) +
      (if n%6=2 ∨ n%42=5 ∨ n%42=11 ∨ n%42=29 then 1 else 0)

theorem zipperLedger_eq_squareScore (k : Nat) (hk : 39 ≤ k) :
    zipperLedger k = squareScore (3*k+2) := by
  rw [squareScore_three_mul_add_two k (by omega)]
  by_cases alt : (3*k+2)%42 = 14
  · simp only [zipperLedger,if_pos alt]
    have eq : (3*k+2-7-k/2)+k/2+7 = 3*k+2 := by omega
    have p := congrArg (· * k) eq
    ring_nf at p ⊢
    split <;> omega
  · simp only [zipperLedger,if_neg alt]
    have eq : (3*k+2-8-k/2)+k/2+8 = 3*k+2 := by omega
    have p := congrArg (· * k) eq
    let e := if (3*k+2)%42 = 38 ∨ (3*k+2)%42 = 29 then 1 else
      if (3*k+2)%42 = 5 then 2 else 0
    let repair := if (3*k+2)%6=2 ∨ (3*k+2)%42=5 ∨ (3*k+2)%42=11 ∨
      (3*k+2)%42=29 then 1 else 0
    have phase : 1+((3*k+2-8-k/2-e+4)/7)+repair+(k-5)/7+
        (if k%14=11 then 1 else 0) = k/2 := by
      let r := k%14
      have hr : r<14 := Nat.mod_lt _ (by decide)
      have ph : (3*k+2)%42=3*r+2 := by dsimp [r]; omega
      have parity : (3*k+2)%6=3*(r%2)+2 := by dsimp [r]; omega
      change 1+_+_+_+(if r=11 then 1 else 0)=_
      dsimp only [e,repair]
      rw [ph,parity]
      have key : k%14=r := rfl
      interval_cases r <;> norm_num at * <;> omega
    change 3*k+2+k+(k/2)*k+(3*k+2-8-k/2)*(k+1)+
      (3*k+2-8-k/2-e+4)/7+(3*k+3+(3*k+2))+repair=_
    generalize he : e = E at phase ⊢
    generalize hg : repair = R at phase ⊢
    ring_nf at p phase ⊢
    omega

end GridGraphs.ResidueTwoLower
