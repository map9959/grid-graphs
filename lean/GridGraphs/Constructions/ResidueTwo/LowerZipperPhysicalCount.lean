import GridGraphs.Constructions.ResidueTwo.LowerZipperWire
import GridGraphs.Constructions.ResidueTwo.LowerZipperAltLayout
import GridGraphs.Constructions.ResidueTwo.LowerZipperCount

namespace GridGraphs.ResidueTwoLower

/-- The physical mark set of every tail zipper has exactly the prescribed
cardinality. This statement uses the same mask as dual reachability. -/
theorem marks_card_eq_squareScore (k : Nat) (hk : 39≤k) :
    let n := 3*k+2
    (Finset.univ.filter (fun v : GridVertex n n => marks n v.1 v.2)).card = squareScore n := by
  let n := 3*k+2
  let f := k/2
  let e := if n%42=38 ∨ n%42=29 then 1 else if n%42=5 then 2 else 0
  change (Finset.univ.filter (fun v : GridVertex n n => marks n v.1 v.2)).card = _
  rw [← boardCount_eq_card,←zipperLedger_eq_squareScore k hk]
  have skip : marks n = if n%42=14 then alternating n else zipper n := by
    simp [marks,show n≠26 by dsimp [n]; omega,show n≠29 by dsimp [n]; omega,
      show n≠32 by dsimp [n]; omega]
  rw [skip]
  by_cases alt : n%42=14
  · rw [if_pos alt,alternating_count k hk]
    simp [zipperLedger,show (3*k+2)%42=14 from alt]
  · rw [if_neg alt]
    have ff : (n-2)/6=f := by dsimp [n,f]; omega
    let rep := n%6=2 ∨ n%42=5 ∨ n%42=11 ∨ n%42=29
    let t := if n%6=2 then f else if n%42=29 then 4+2*((n-71)/42)
      else if n%42=11 then 3+2*((n-53)/42) else 3+2*((n-47)/42)
    have ht : t≤f := by dsimp [t,n,f]; split_ifs <;> omega
    have he : e≤2 := by dsimp [e]; split_ifs <;> omega
    let old := railLayout n f e
    have eq : zipper n = if rep then (fun i j => wireEdit (3*t) i j (old i j)) else old := by
      funext i j
      simp only [zipper,beq_iff_eq,Bool.or_eq_true,ff,e,rep,t,old]
      split_ifs <;> first | rfl | congr 2 <;> omega
    have sum := railLayout_count k e hk he
    rw [eq]
    change boardCount n _ = _
    change boardCount n _ =
      (if n%42=14 then _ else n+k+f*k+(n-8-f)*(k+1)+(n-8-f-e+4)/7+
        (3*k+3+n)+(if rep then 1 else 0))
    rw [if_neg alt]
    by_cases r : rep
    · rw [if_pos r,if_pos r,wire_gain k e t hk ht,sum]
    · rw [if_neg r,if_neg r,sum,add_zero]

end GridGraphs.ResidueTwoLower
