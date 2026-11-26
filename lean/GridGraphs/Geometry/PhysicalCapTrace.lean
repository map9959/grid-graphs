import GridGraphs.Geometry.CapPhysicalTapes

namespace GridGraphs.CapSite
open GridGraphs.CapBill GridGraphs.PitchCut GridGraphs.Slit GridGraphs.Slit.Replay Finset

private def lookup [Zero M] (g : Fin r → M) (j : Nat) := if h : j<r then g ⟨j,h⟩ else 0

private theorem two_sums {M : Type*} [AddCommMonoid M] (g : Fin r → M) {a b : Nat}
    (hr : a+b=r) :
    (∑ j ∈ range a, lookup g j)+(∑ j ∈ range b, lookup g (r-1-j))=∑ t, g t := by
  let f := fun j => lookup g (a+j)
  have mid : (∑ j ∈ range b, lookup g (r-1-j))=∑ j ∈ range b, f j := by
    rw [←sum_range_reflect f b]
    apply sum_congr rfl; intro j hj
    dsimp [f]; congr 1; have := mem_range.mp hj; omega
  rw [mid]; change _+(∑ j ∈ range b, lookup g (a+j))=_
  rw [←sum_range_add,hr,←Fin.sum_univ_eq_sum_range (lookup g)]; simp [lookup]

private theorem tooth_one_to_one {r h} : Function.Injective (tooth (r:=r) (h:=h)) := by
  intro i j eq; apply Fin.ext
  have e := congrArg (fun v : Cell r h => v.2.val) eq; dsimp [tooth] at e; omega

variable {r h : Nat} (F : Finset (Cell r h))
private theorem total_kept (pad : Padded F) :
    (∑ t : Fin r, (1-one (dropBit F t))) +
      (waived (board r h) (terminalSet F) F).card = r := by
  classical
  let W := waived (board r h) (terminalSet F) F
  let T := terminalSet F
  have eq : (univ.filter (fun i : Fin r => tooth i ∈ W)).image tooth=W := by
    ext v; simp only [mem_image,mem_filter,mem_univ,true_and]
    constructor
    · rintro ⟨i,h,rfl⟩; exact h
    · intro hv
      have mem := (filter_subset _ _ hv : v∈T)
      rw [show T=univ.image tooth from terminal_eq pad] at mem
      obtain ⟨i,_,rfl⟩ := mem_image.mp mem; exact ⟨_,hv,rfl⟩
  have w := congrArg card eq
  rw [card_image_of_injective _ tooth_one_to_one] at w
  have c := card_filter_add_card_filter_not (s:=(univ : Finset (Fin r))) (p:=fun i => tooth i∈W)
  rw [card_univ,Fintype.card_fin,w] at c
  have complement : (∑ t : Fin r, (1-one (dropBit F t))) =
      (univ.filter (fun i : Fin r => tooth i ∉ W)).card := by
    rw [card_filter]; apply sum_congr rfl
    intro i _; by_cases b : tooth i∈W <;> simp [W] at b <;> simp [dropBit,one,b,W]
  change _ + W.card=r
  omega

private theorem some_kept (pad : Padded F) (hr : 0<r) :
    (waived (board r h) (terminalSet F) F).card < r := by
  classical
  let T := terminalSet F
  have tc : T.card=r := pad.teeth
  let e := (Fintype.equivFin ↥T).symm
  have eq := waived_eq_rank (board r h) T F
    ((finCongr (Fintype.card_coe T).symm).trans e)
  rw [PitchCut.rank,Fintype.card_fin] at eq
  have ne : (PitchCut.classes (bonds F) (fun i => ((finCongr (Fintype.card_coe T).symm).trans e i).val)).Nonempty :=
    ⟨_,mem_image_of_mem _ (mem_univ (⟨0,by omega⟩ : Fin T.card))⟩
  change (waived (board r h) T F).card=T.card-
    (PitchCut.classes (bonds F) (fun i => ((finCongr (Fintype.card_coe T).symm).trans e i).val)).card at eq
  change (waived (board r h) T F).card < r
  have := card_pos.mpr ne; omega

private theorem total_sites : (∑ t : Fin r, ∑ y, triplePrice F t false y) = ∑ v, charge F v := by
  unfold triplePrice
  rw [sum_comm]
  rw [Fintype.sum_prod_type]; apply sum_congr rfl; intro y _
  let E : Fin r × Fin 3 ≃ Fin (3*r) :=
    finProdFinEquiv.trans (finCongr (Nat.mul_comm r 3))
  rw [←Fintype.sum_prod_type (fun p : Fin r × Fin 3 => charge F (body p.1 false y p.2)),
    ← E.sum_comp (fun x => charge F ((y,x) : Cell r h))]
  apply sum_congr rfl; intro p _
  congr 1
  refine Prod.ext ?_ (Fin.ext ?_)
  · rfl
  · change 3*p.1.val+p.2.val=p.2.val+3*p.1.val; omega

private theorem reversal_price (t : Fin r) (y : Fin (h+2)) :
    triplePrice F t true y = triplePrice F t false y := by
  rw [triplePrice,triplePrice,Fin.sum_univ_three,Fin.sum_univ_three]
  change charge F (body t false y 2)+charge F (body t false y 1)+charge F (body t false y 0) = _
  ring

private theorem sum_charge : (∑ v, charge F v) =
    (∑ v, siteBill (board r h) F (outer r h) v)+
      2*((extraRoots (board r h) (terminalSet F) F).card : Int) := by
  classical
  simp [charge,one,Finset.sum_add_distrib,mul_comm]

private theorem physical_total (pad : Padded F) {a b : Nat} (split : a+b=r) :
    ((∑ j ∈ range a, sideBill F j false : Nat) : Int) + (∑ j ∈ range b, sideBill F j true : Nat) =
    (∑ v, charge F v)-2*r := by
  let p := fun t : Fin r => (∑ y, triplePrice F t false y)-2
  have side (j : Nat) (rev : Bool) (hj : j<r) :
      (sideBill F j rev : Int)=lookup p (columnIndex r j rev) := by
    have ht : columnIndex r j rev<r := by unfold columnIndex; split_ifs <;> omega
    simp only [sideBill,dif_pos hj,lookup,dif_pos ht,physical_column_price F pad]
    cases rev <;> simp [p,reversal_price]
  push_cast
  have l : (∑ j ∈ range a, (sideBill F j false : Int)) = ∑ j ∈ range a, lookup p j :=
    sum_congr rfl (fun j hj => side j false (by have := mem_range.mp hj; omega))
  have u : (∑ j ∈ range b, (sideBill F j true : Int)) = ∑ j ∈ range b, lookup p (r-1-j) :=
    sum_congr rfl (fun j hj => side j true (by have := mem_range.mp hj; omega))
  rw [l,u,two_sums p split]
  simp [p,sum_sub_distrib,total_sites,mul_comm]

/-- Construct both necessary languages, their common reflected slit, and
the *exact* colored bill directly from an acyclic padded mark set. No
orientation, words, prices or component partition supplied by the caller. -/
noncomputable def paddedCapTrace (ok : tablesOK) {k h : Nat} (hk : 5≤k)
    {F : Finset (Cell (k+1) h)} (pad : Padded F) :
    CapTrace k (waived (board (k+1) h) (terminalSet F) F).card
      ((F.card : Int)-(k+1)*((h:ℤ)+1)) := by
  have split : 2+(k-1)=k+1 := by omega
  let g := fun t : Fin (k+1) => 1-one (dropBit F t)
  have sides (n : Nat) (rev : Bool) (hn : n≤k+1) :
      (∑ j ∈ range n, (1-sideDrop F j rev)) = ∑ j ∈ range n, lookup g (columnIndex (k+1) j rev) := by
    apply sum_congr rfl; intro j hj
    have less := mem_range.mp hj
    have ht : columnIndex (k+1) j rev<k+1 := by unfold columnIndex; split_ifs <;> omega
    simp [sideDrop,lookup,g,ht,show j<k+1 by omega]
  have counts := total_kept F pad
  rw [←two_sums g split] at counts
  have cnt : (∑ j ∈ range 2, (1-sideDrop F j false))+
      (∑ j ∈ range (k-1), (1-sideDrop F j true))+
      (waived (board (k+1) h) (terminalSet F) F).card=k+1 := by
    rw [sides 2 false (by omega),sides (k-1) true (by omega)]
    exact counts
  have pos := some_kept F pad (by omega)
  refine ⟨_,_,_,_,_,_,cnt,by omega,?_,actual_prefix F ok pad false 2 (by omega),
    actual_prefix F ok pad true (k-1) (by omega),meet_slit F split⟩
  have sum := physical_total F pad split
  rw [sum_charge] at sum
  have b := oriented_bill (by omega) pad
  dsimp only at b
  push_cast at b sum ⊢
  linarith only [sum,b]

end GridGraphs.CapSite
