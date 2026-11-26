import GridGraphs.Constructions.ResidueTwo.LowerZipperAlternating

namespace GridGraphs.ResidueTwoLower
open Finset

theorem alternating_count (k : Nat) (hk : 39≤k) :
    let n := 3*k+2
    let f := k/2
    let len := n-7-f
    boardCount n (alternating n) =
      n-1+(f*k+1)+len*(k+1)+(len+4)/7+(2*n+1) := by
  let n := 3*k+2
  let f := k/2
  let len := n-7-f
  let st := f+2
  let tip := fun i : Nat => f-1+(i/7)%2
  let C := fun i => rowCount (fun j => alternating n i j) n
  have total : n=st+len+5 := by dsimp [n,st,len,f]; omega
  have ff : (n-2)/6=f := by dsimp [n,f]; omega
  have stpos : 2 ≤ st := by dsimp [st]; omega
  have top : (∑ i ∈ range 2,C i) = n-1 := by
    have first : C 0 = n-2 := by
      change rowCount (fun j => decide (j ≥ 3) || j==0) n = _
      have eq : rowCount (fun j => decide (j ≥ 3)) n =
          rowCount (fun j => 3 ≤ j && j<n) n :=
        rowCount_congr fun j hj => by simp [hj]
      rw [rowCount_wire_add _ (by dsimp [n]; omega) (by decide),eq,rowCount_interval]
      dsimp [n]; omega
    have second : C 1 = 1 := by
      change rowCount (fun j => j==0) n = 1
      simpa [rowCount] using rowCount_wire_add (fun _ => false) (show 0<n by dsimp [n]; omega) rfl
    simp only [sum_range_succ,sum_range_zero,zero_add,first,second]; dsimp [n]; omega
  have advancing : (∑ i ∈ range f,C (2+i)) = f*k+1 := by
    have row (i : Nat) (hi : i ∈ range f) : C (2+i)=k+(if i=0 then 1 else 0) := by
      have b := mem_range.mp hi
      rw [← altFront_count k i (by dsimp [f] at b; omega)]
      apply rowCount_congr; intro j _
      simp [alternating,Id.run,pure,ff,show 2+i≠1 by omega,show 2+i<f+2 by omega]
      rfl
    rw [sum_congr rfl row,sum_add_distrib]; simp [show 0<f by dsimp [f]; omega]
  have middle : (∑ i ∈ range len,C (st+i)) = len*(k+1)+(len+4)/7 := by
    rw [← band_sum (k := k) (len := len) tip (fun i => i/7%2==0)
      (fun i _ => by dsimp [tip,f]; omega)]
    apply sum_congr rfl; intro i hi
    have b := mem_range.mp hi
    have before : st+i<n-5 := by omega
    apply rowCount_congr; intro j _
    simp [alternating,Id.run,pure,ff,show st≠0 by omega,show st+i≠1 by omega,
      show f+2=st from rfl,before,Nat.min_eq_left (by omega : st+i≤n-5),
      tip,Nat.mul_add,show n-7-f=len from rfl]
  have last : (∑ i ∈ range 5,C (st+len+i)) = 2*n+1 := by
    rw [← altCap_sum k (tip len) (by dsimp [tip,f]; omega)]
    apply sum_congr rfl; intro i _
    apply rowCount_congr; intro j _
    have big : n-5 ≤ st+len+i := by omega
    simp [alternating,Id.run,pure,ff,show st≠0 by omega,show st+len+i≠1 by omega,
      show f+2=st from rfl,show ¬st+len+i<st by omega,Nat.not_lt.mpr big,
      Nat.min_eq_right big,show n-5-st=len by omega,show st+len+i-(n-5)=i by omega,tip,Nat.mul_add]
    rfl
  change (∑ i ∈ range n,C i)=_
  conv_lhs => rw [total,sum_range_add,sum_range_add,show st=2+f by dsimp [st]; omega,sum_range_add]
  rw [show 2+f=st by dsimp [st]; omega]
  rw [top,advancing,middle,last]
  change n-1+(f*k+1)+(len*(k+1)+(len+4)/7)+(2*n+1) =
    n-1+(f*k+1)+len*(k+1)+(len+4)/7+(2*n+1)
  omega

end GridGraphs.ResidueTwoLower
