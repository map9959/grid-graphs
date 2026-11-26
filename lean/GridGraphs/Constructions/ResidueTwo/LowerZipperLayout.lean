import GridGraphs.Constructions.ResidueTwo.LowerZipperFront
import GridGraphs.Constructions.ResidueTwo.LowerZipperBand
import GridGraphs.Constructions.ResidueTwo.LowerZipperCap

namespace GridGraphs.ResidueTwoLower
open Finset

def boardCount (n : Nat) (m : Mask) := ∑ i ∈ range n, rowCount (m i) n

theorem boardCount_eq_card (n : Nat) (m : Mask) :
    boardCount n m = (univ.filter (fun v : GridVertex n n => m v.1 v.2)).card := by
  rw [card_filter,Fintype.sum_prod_type]
  unfold boardCount
  rw [← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro i _
  rw [rowCount,card_filter,← Fin.sum_univ_eq_sum_range]

private theorem topCount (k : Nat) (hk : 2≤k) :
    let n := 3*k+2
    (rowCount (fun j => j<n-3 || j==n-1) n) +
    (rowCount (fun j => j==n-1) n) +
    (rowCount (fun j => j%3==2 || j==n-1) n) = n+k := by
  let n := 3*k+2
  have h0 : rowCount (fun j => decide (j<n-3)) n = n-3 := by
    simpa [Nat.min_def,show n-3≤n by omega] using rowCount_interval 0 (n-3) n
  have h1 : rowCount (fun j => j == n-1) n = 1 := by
    simpa [rowCount] using rowCount_wire_add (fun _ => false) (show n-1<n by dsimp [n]; omega) rfl
  have h2 : rowCount (fun j => j%3 == 2) n = k := by
    have e := rowCount_pitch 0 n 2 n (by omega) (by omega)
    have eq : rowCount (fun j => j%3 == 2) n =
      rowCount (fun j => 0≤j && j<n && j%3 == 2) n :=
      rowCount_congr fun j hj => by simp [hj]
    rw [eq,e]; dsimp [n]; omega
  change _+_+_=n+k
  rw [rowCount_wire_add _ (by dsimp [n]; omega) (by simp; omega),h0,h1,
    rowCount_wire_add _ (by dsimp [n]; omega) (by simp [n]),h2]; dsimp [n]; omega

/-- Sum the actual unrepaired zipper, including waiting rows, a final
partial band of any length, and its moving five-row cap. -/
theorem railLayout_count (k e : Nat) (hk : 39≤k) (he : e≤2) :
    let n := 3*k+2
    let f := k/2
    let len := n-8-f-e
    boardCount n (railLayout n f e) =
      n+k+f*k+(n-8-f)*(k+1)+(len+4)/7+(3*k+3+n) := by
  let n := 3*k+2
  let f := k/2
  let st := 3+f+e
  let len := n-8-f-e
  let C := fun i => rowCount (fun j => railLayout n f e i j) n
  have total : n = st+len+5 := by dsimp [n,st,len,f]; omega
  have bnd (i : Nat) (hi : i≤len) : 2 ≤ f-i/7 ∧ f-i/7+2 ≤ k := by
    dsimp [len,n,f] at *; omega
  have first : (∑ i ∈ range 3, C i) = n+k := by
    simpa [C,railLayout,sum_range_succ,Id.run,pure,add_assoc,n] using topCount k (by omega)
  have front : (∑ i ∈ range f, C (3+i)) = f*k := by
    apply Eq.trans (sum_congr rfl (g := fun _ => k) ?_) (by simp)
    intro i hi
    have b := mem_range.mp hi
    have p : 3+i<3+f := by omega
    rw [← advance_count (a := i) (k := k) (by dsimp [f] at b; omega)]
    apply rowCount_congr
    intro j _
    simp [C,railLayout,advance,Id.run,pure,p,n,show 3+i ≠ 0 by omega,
      show 3+i ≠ 1 by omega,show 3+i ≠ 2 by omega]
  have wait : (∑ i ∈ range e, C (3+f+i)) = e*(k+1) := by
    apply Eq.trans (sum_congr rfl (g := fun _ => k+1) ?_) (by simp)
    intro i hi
    have b := mem_range.mp hi
    have p : 3+f+i<3+f+e := by omega
    have eq : C (3+f+i) = rowCount (regular (3*f)) n := by
      apply rowCount_congr; intro j _
      simp [railLayout,Id.run,pure,p,show 3+f+i ≠ 0 by omega,show 3+f+i ≠ 1 by omega,
        show 3+f+i ≠ 2 by omega]
    rw [eq,regular_prefix]; dsimp [n,f]; omega
  have middle : (∑ i ∈ range len, C (st+i)) = len*(k+1)+(len+4)/7 := by
    rw [← band_sum (k := k) (len := len) (fun i => f-i/7) (fun _ => false)
      (fun i hi => by obtain ⟨a,b⟩ := bnd i (by omega); exact ⟨by omega,b⟩)]
    apply sum_congr rfl
    intro i hi
    have b := mem_range.mp hi
    have a : ¬ n-5 ≤ st+i := by omega
    have h0 : st+i ≠ 0 := by dsimp [st]; omega
    have h1 : st+i ≠ 1 := by dsimp [st]; omega
    have h2 : st+i ≠ 2 := by dsimp [st]; omega
    have p : ¬ st+i < 3+f := by dsimp [st]; omega
    apply rowCount_congr; intro j _
    simp [railLayout,Id.run,pure,show st≠0 by dsimp [st]; omega,h0,h1,h2,p,show 3+f+e=st from rfl,a,
      show n-5-st=len by omega,Nat.mul_sub]
  have last : (∑ i ∈ range 5, C (st+len+i)) = 3*k+3+n := by
    let l := 3*(f-len/7)
    have row (i : Nat) : C (st+len+i) = rowCount (cap l i) n := by
      have a : n-5 ≤ st+len+i := by omega
      have big : 3+f+e ≤ st+len+i := by dsimp [st]; omega
      have s : st+len+i-(n-5)=i := by omega
      apply rowCount_congr; intro j _
      simp [railLayout,Id.run,pure,show st≠0 by dsimp [st]; omega,show st+len+i ≠ 0 by omega,show st+len+i ≠ 1 by omega,
        show st+len+i ≠ 2 by omega,show ¬st+len+i < 3+f by omega, Nat.not_lt.mpr big,
        a,s,show n-5-(3+f+e)=len by dsimp [st] at total; omega,l,Nat.mul_sub]
    obtain ⟨v,w,x,y,z⟩ := cap_counts (bnd len le_rfl).1 (bnd len le_rfl).2
    dsimp only at v w x y z
    simp only [sum_range_succ,sum_range_zero,row]
    change _ = 3*k+3+(3*k+2)
    dsimp only [l,n]
    rw [v,w,x,y,z]; omega
  change (∑ i ∈ range n, C i) = _
  conv_lhs => rw [total,sum_range_add,sum_range_add,show st=3+f+e from rfl,sum_range_add,sum_range_add]
  change (∑ i ∈ range 3, C i) + _ + _ + (∑ i ∈ range len, C (st+i)) + _ = _
  rw [first,front,wait,middle,last]
  have rel : e+len=n-8-f := by dsimp [len,n,f]; omega
  have prod := congrArg (· * (k+1)) rel
  rw [Nat.add_mul] at prod
  change n+k+f*k+e*(k+1)+(len*(k+1)+(len+4)/7)+(3*k+3+n) =
    n+k+f*k+(n-8-f)*(k+1)+(len+4)/7+(3*k+3+n)
  omega

end GridGraphs.ResidueTwoLower
