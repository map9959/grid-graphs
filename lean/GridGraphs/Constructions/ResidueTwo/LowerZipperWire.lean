import GridGraphs.Constructions.ResidueTwo.LowerZipperLayout

namespace GridGraphs.ResidueTwoLower
open Finset

private theorem diagCount {p : Nat → Bool} {n a t : Nat} (ha : a≤t) (b : 3*a+2<n)
    (off : p (3*a)=false) (on : a<t → p (3*a+2)=true) :
    rowCount (fun j => wireEdit (3*t) (2+a) j (p j)) n =
      rowCount p n + (if a=t then 1 else 0) := by
  by_cases h : a=t
  · subst t
    have eq : rowCount (fun j => wireEdit (3*a) (2+a) j (p j)) n =
        rowCount (fun j => p j || j==3*a) n := by
      apply rowCount_congr; intro j _
      simp [wireEdit,Id.run,pure,show 2+a≠1 by omega]
      grind
    rw [eq,rowCount_wire_add _ (by omega) off]; simp
  · have lt : a<t := by omega
    have eq : rowCount (fun j => wireEdit (3*t) (2+a) j (p j)) n =
        rowCount (fun j => (p j && j != 3*a+2) || j==3*a) n := by
      apply rowCount_congr; intro j _
      simp [wireEdit,Id.run,pure,show 2+a≠1 by omega,ha,lt]
      grind
    rw [eq,rowCount_wire_add _ (by omega) (by simp [off]),rowCount_wire_remove _ b (on lt)]
    simp [h]

theorem wire_gain (k e t : Nat) (hk : 39≤k) (ht : t≤k/2) :
    let n := 3*k+2
    let old := railLayout n (k/2) e
    boardCount n (fun i j => wireEdit (3*t) i j (old i j)) = boardCount n old+1 := by
  let n := 3*k+2
  let f := k/2
  let old := railLayout n f e
  let A := fun i => rowCount (fun j => wireEdit (3*t) i j (old i j)) n
  let B := fun i => rowCount (old i) n
  have z : A 0 + 1 = B 0 := by
    have eq : A 0 = rowCount (fun j => old 0 j && j != 1) n := by
      apply rowCount_congr; intro j _
      simp [wireEdit,Id.run,pure]; grind
    rw [eq]; apply rowCount_wire_remove
    · dsimp [n]; omega
    · simp [old,railLayout,Id.run,pure,n]; omega
  have o : A 1 = B 1+1 := by
    have eq : A 1 = rowCount (fun j => old 1 j || j==0) n := by
      apply rowCount_congr; intro j _
      simp [wireEdit,Id.run,pure]; grind
    rw [eq]; apply rowCount_wire_add
    · dsimp [n]; omega
    · simp [old,railLayout,Id.run,pure,n]
  have two (a : Nat) : A (2+a) = B (2+a)+(if a=t then 1 else 0) := by
    by_cases b : a≤t
    · apply diagCount b (by dsimp [n]; omega)
      · by_cases az : a=0
        · subst a; simp [old,railLayout,Id.run,pure,n]
        · have line : 2+a < 3+f := by dsimp [f]; omega
          simp [old,railLayout,Id.run,pure,line,az,show 2+a≠1 by omega,
            show 2+a≠2 by omega,leftRail,rightRail,n]
          omega
      · intro lt
        by_cases az : a=0
        · subst a; simp [old,railLayout,Id.run,pure]
        · have line : 2+a < 3+f := by dsimp [f]; omega
          simp [old,railLayout,Id.run,pure,line,az,show 2+a≠1 by omega,
            show 2+a≠2 by omega,leftRail,rightRail,n]
          omega
    · have ne : a≠t := by omega
      simp only [ne,if_false,add_zero]
      apply rowCount_congr; intro j _
      simp [wireEdit,Id.run,pure,show 2+a≠1 by omega,show ¬a<t by omega,b]
  change (∑ i ∈ range n,A i) = (∑ i ∈ range n,B i)+1
  let len := n-2
  have nn : n=2+len := by dsimp [n,len]; omega
  have mid : (∑ i ∈ range len,A (2+i)) = (∑ i ∈ range len,B (2+i))+1 := by
    simp_rw [two,sum_add_distrib]; simp [show t<len by dsimp [n,len]; omega]
  conv_lhs => rw [nn,sum_range_add]
  conv_rhs => rw [nn,sum_range_add]
  simp only [sum_range_succ,sum_range_zero,zero_add,mid]
  omega

end GridGraphs.ResidueTwoLower
