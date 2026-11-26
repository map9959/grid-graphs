import GridGraphs.Constructions.ResidueTwo.LowerZipperLayout

namespace GridGraphs.ResidueTwoLower
open Finset

theorem altFront_count (k a : Nat) (h : 2*a+2≤k) :
    rowCount (altFront (3*k+2) a) (3*k+2) = k+(if a=0 then 1 else 0) := by
  let n := 3*k+2
  let p := advance k a
  have fresh : p (3*a+2) = false := by simp [p,advance,leftRail,rightRail]; omega
  have on : p (3*a) = true := by simp [p,advance,leftRail]
  let q := fun j => p j || j==3*a+2
  have base : rowCount q n = k+1 := by
    rw [rowCount_wire_add _ (by dsimp [n]; omega) fresh,advance_count h]
  have same (j : Nat) : altFront n a j = (q j && (a==0 || j != 3*a)) := by
    apply Bool.eq_iff_iff.mpr
    simp [altFront,q,p,advance,n,leftRail,rightRail]
    omega
  change rowCount (altFront n a) n = _
  rw [show altFront n a = fun j => q j && (a==0 || j != 3*a) from funext same]
  by_cases zero : a=0
  · simpa [zero] using base
  · have rem := rowCount_wire_remove q (show 3*a<n by dsimp [n]; omega)
      (show q (3*a)=true by simp [q,on])
    simp [zero,show (a==0)=false by simpa using zero]
    omega

theorem altCap_sum (k a : Nat) (h : a+3≤k) :
    (∑ r ∈ range 5, rowCount (altCap (3*k+2) (3*a) r) (3*k+2)) = 2*(3*k+2)+1 := by
  let n := 3*k+2
  let l := 3*a
  let p := leftRail l
  have left : rowCount p n = a+1 := by
    have e : rowCount p n = rowCount (fun j => 0≤j && j<l+1 && j%3==0) n := by
      apply rowCount_congr; intro j _
      simp [p,leftRail]
    rw [e,rowCount_pitch _ _ _ _ (by omega) (by omega)]
    dsimp [n,l]; omega
  have one (d : Nat) (hd : d=2 ∨ d=3) :
      rowCount (fun j => p j || j==l+d || j==n-1) n = a+3 := by
    have bd : l+d<n-1 := by dsimp [l,n]; omega
    rw [rowCount_wire_add _ (by dsimp [n]; omega) (by simp [p,leftRail]; dsimp [l,n] at *; omega),
      rowCount_wire_add _ (by omega) (by simp [p,leftRail]; omega),left]
  have mid : rowCount (altCap n l 1) n = (a+1)+(n-2-(l+5))+1 := by
    change rowCount (fun j => (p j || (decide (l+5 ≤ j) && decide (j<n-2))) || j==n-1) n=_
    rw [rowCount_wire_add _ (by dsimp [n]; omega) (by simp [p,leftRail]; dsimp [n,l]; omega),
      rowCount_or,left,rowCount_interval]
    · dsimp [n,l]; omega
    · intro j _ hj; simp [p,leftRail] at hj; simp; omega
  have single : rowCount (altCap n l 3) n = 1 := by
    simpa [altCap,rowCount] using rowCount_wire_add (fun _ => false) (show 0<n by dsimp [n]; omega) rfl
  have allBut : rowCount (altCap n l 4) n + 1 = n := by
    simpa [altCap,rowCount] using rowCount_wire_remove (fun _ => true) (show 1<n by dsimp [n]; omega) rfl
  change (∑ r ∈ range 5,rowCount (altCap n l r) n)=2*n+1
  simp only [sum_range_succ,sum_range_zero,zero_add,mid,single]
  change rowCount (fun j => p j || j==l+2 || j==n-1) n + _ +
    rowCount (fun j => p j || j==l+3 || j==n-1) n + _ + _ = _
  rw [one 2 (by omega),one 3 (by omega)]
  dsimp [l,n] at *; omega

end GridGraphs.ResidueTwoLower
