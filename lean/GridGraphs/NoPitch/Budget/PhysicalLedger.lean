import GridGraphs.NoPitch.Budget.Segments

namespace GridGraphs.NoPitch.Budget
open SimpleGraph Finset PitchCut
variable {k : Nat}

private theorem pair_sum (f : Nat → Letter) (a n : Nat) :
    pathsFrom (some (f a)) ((List.range' (a+1) n).map f) =
    ∑ j : Fin n, I (realized (f (a+j.val)) (f (a+j.val+1))) := by
  induction n generalizing a with
  | zero => simp [pathsFrom]
  | succ n ih =>
    rw [List.range'_succ,List.map_cons,pathsFrom,ih,Fin.sum_univ_succ]
    simp [Nat.add_left_comm,Nat.add_comm]

private def orient (F : Finset (Site k)) (b : Bool) := if b then trans F else F

private theorem live_real (F : Finset (Site k)) (b : Bool) (i : J k) (j : Fin k) :
    realized (letter (orient F b) (teeth k i) j.val)
      (letter (orient F b) (teeth k i) (j.val+1)) = decide (live F (b,i,j)) := by
  let s : Seg k := (b,i,j)
  have tooth (u : J k) : (teeth k u).val=3*u.val := rfl
  have rim (t : Fin 4) : onRim (point s t) := by
    cases b <;> simp [s,onRim,point,tooth]
  have step (u v : Fin 4) (h : u.val+1=v.val) :
      (gridGraph (N k) (N k)).Adj (point s u) (point s v) := by
    change adjacent _ _ _ _
    cases b <;> simp [s,point,adjacent,coord,Fin.ext_iff] <;> omega
  have bond (u v : Fin 4) (h : u.val+1=v.val) :
      (base F).Adj (point s u) (point s v) ↔ point s u∈F ∨ point s v∈F := by
    change (_ ∧ (_ ∈ skeleton F ∨ _ ∈ skeleton F)) ↔ _
    simp only [step _ _ h,true_and,skeleton,mem_filter]
    exact or_congr (and_iff_left (rim u)) (and_iff_left (rim v))
  have equiv : live F s ↔ _ := and_congr (bond 0 1 rfl) (and_congr (bond 1 2 rfl) (bond 2 3 rfl))
  simp only [show (b,i,j)=s from rfl,equiv]
  have bits (t : Fin 4) : bit (orient F b) (teeth k i) (3*j.val+t.val) =
      decide (point s t∈F) := by
    have bound := (coord j t).isLt
    change 3*j.val+t.val<N k at bound
    cases b <;> simp [orient,s,point,coord,bit,bound]
  have z := bits 0; have l := bits 1; have r := bits 2; have e := bits 3
  simp only [Fin.val_zero,Fin.val_one,Nat.add_zero] at z l
  change bit _ _ (3*j.val+2)=_ at r
  change bit _ _ (3*j.val+3)=_ at e
  simp only [letter,realized,show 3*j.val+3-1=3*j.val+2 by omega,
    show 3*(j.val+1)=3*j.val+3 by omega,decide_eq_true (by omega : 0<j.val+1),
    Bool.true_and,z,l,r,e]
  by_cases a : point s 0∈F <;> by_cases b : point s 1∈F <;>
    by_cases c : point s 2∈F <;> by_cases d : point s 3∈F <;> simp [a,b,c,d]

private theorem path_count (F : Finset (Site k)) (b : Bool) :
    axisPaths (orient F b) = ∑ i : J k, ∑ j : Fin k, I (decide (live F (b,i,j))) := by
  apply sum_congr rfl
  intro i _
  unfold word
  rw [List.range_eq_range',List.range'_succ,List.map_cons,pathsFrom]
  simp only [Option.any_none,I,Bool.toNat_false,Nat.cast_zero,zero_add]
  rw [pair_sum]
  simp only [Nat.zero_add,live_real,I]

theorem axisPaths_letters (F : Finset (Site k)) :
    axisPaths F=∑ i : J k, ∑ j : Fin k, I (realized (L F i j.castSucc) (L F i j.succ)) := by
  apply sum_congr rfl; intro i _
  unfold word
  rw [List.range_eq_range',List.range'_succ,List.map_cons,pathsFrom]
  simp only [Option.any_none,I,Bool.toNat_false,Nat.cast_zero,zero_add]
  rw [pair_sum]
  simp only [Nat.zero_add,L,Fin.val_castSucc,Fin.val_succ,I]

theorem paths_eq (F : Finset (Site k)) :
    axisPaths F+axisPaths (trans F)=((liveSegs F).card:Int) := by
  change axisPaths (orient F false)+axisPaths (orient F true)=_
  rw [path_count,path_count]
  change _=((univ.filter (live F)).card:Int)
  simp only [card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [Fintype.sum_prod_type]
  have ev (s : Seg k) : I (decide (live F s))=if live F s then 1 else 0 := by
    by_cases h : live F s <;> simp [h,I]
  simp only [Fintype.sum_bool,Fintype.sum_prod_type,ev]
  ac_rfl

theorem joints_card (k : Nat) : (joints k).card=(k+1)^2 := by
  let f (p : J k × J k) : Site k := (teeth k p.1,teeth k p.2)
  have inj : Function.Injective f := fun x y h => Prod.ext
    ((teeth k).injective (congrArg Prod.fst h)) ((teeth k).injective (congrArg Prod.snd h))
  have eq : joints k=univ.image f := by
    ext x; simp only [joints,mem_filter,mem_univ,true_and,mem_image]
    constructor
    · intro h; refine ⟨(owner x.1, owner x.2),?_⟩
      apply Prod.ext <;> apply Fin.ext <;> change 3*((_+1)/3)=_ <;> omega
    · rintro ⟨p,rfl⟩; change 3*_ %3=0 ∧ 3*_ %3=0; simp
  rw [eq,card_image_of_injective _ inj]; simp [sq]

theorem sinks_exits_le (F : Finset (Site k)) (acy : (G F).IsAcyclic) :
    ((sinks F).card:Int)+(exits F).card ≤ coarseDeficit F := by
  have e := exits_euler F acy
  have b := live_edge_budget F
  have sub : joints k ⊆ oldSites F := fun x h => mem_filter.mpr ⟨mem_univ _,.inl h⟩
  have c := card_sdiff_add_card_eq_card sub
  have h : (sinks F).card+(exits F).card+(liveSegs F).card ≤ (joints k).card := by omega
  rw [joints_card] at h
  have hi : ((sinks F).card:Int)+(exits F).card+(liveSegs F).card ≤ ((k:Int)+1)^2 := by exact_mod_cast h
  unfold coarseDeficit
  linarith only [hi,paths_eq F]

/-- Both accepting line families, all roots and all exits are evaluated
on one physical forest. No chart variables or feasibility premise. -/
theorem physical_debit_budget (F : Finset (Site k)) (acy : (G F).IsAcyclic)
    (rows : ∀ i, ¬Pitch F (teeth k i)) (cols : ∀ i, ¬Pitch (trans F) (teeth k i)) :
    axisDebit F + axisDebit (trans F) + (F.card:Int) + (sinks F).card + (exits F).card ≤
      (N k:Int)*(k+1) + (F \ skeleton F).card := by
  linarith only [physical_mark_budget F acy rows cols,sinks_exits_le F acy]

end GridGraphs.NoPitch.Budget
