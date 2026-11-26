import GridGraphs.NoPitch.Budget.LineAmounts

namespace GridGraphs.NoPitch.Budget
open PitchCut Finset Keys
variable {k : Nat}

private def flipJ (j : J k) : J k := ⟨k-j.val,by omega⟩
private def flipE (j : Fin k) : Fin k := ⟨k-1-j.val,by have := j.isLt; omega⟩
private def rwFlip (g : Fin 8) := decide (g.val=2 ∨ g.val=3 ∨ g.val=5 ∨ g.val=6)
private def colFlip (g : Fin 8) := decide (g.val=1 ∨ g.val=2 ∨ g.val=4 ∨ g.val=5)
private def swapAxis (g : Fin 8) := g.val%2==1
private def rMap (g : Fin 8) (j : J k) := if rwFlip g then flipJ j else j
private def cMap (g : Fin 8) (j : J k) := if colFlip g then flipJ j else j
private def eMap (g : Fin 8) (j : Fin k) := if colFlip g then flipE j else j
private def source (F : Finset (Site k)) (g : Fin 8) := if swapAxis g then trans F else F
private def rev (x : Letter) : Letter := ⟨x.r,x.z,x.l⟩

private theorem inv_small (g : Fin 8) (x : Site k) : small (N k) (invers g) (small (N k) g x)=x := by
  have a := x.1.isLt; have b := x.2.isLt; unfold N at a b
  fin_cases g <;> norm_num [small,transform,invers,N,Prod.ext_iff,Fin.ext_iff,Fin.ofNat] <;>
    (try simp (disch := omega) only [Nat.mod_eq_of_lt]) <;> omega

private theorem view_mem (F : Finset (Site k)) (g : Fin 8) (x : Site k) :
    x∈view F g ↔ small (N k) (invers g) x∈F := by
  have z : invers (invers g)=g := by revert g; decide +kernel
  constructor
  · intro m; obtain ⟨y,m,rfl⟩ := mem_image.mp m; rwa [inv_small]
  · intro m
    have p := mem_image_of_mem (small (N k) g) m
    have eq := inv_small (invers g) x
    rw [z] at eq
    rwa [eq] at p

private theorem coords (g : Fin 8) (x : Site k) :
    let r := if rwFlip g then 3*k-x.1.val else x.1.val
    let c := if colFlip g then 3*k-x.2.val else x.2.val
    let q := small (N k) (invers g) x
    (q.1.val,q.2.val)=if swapAxis g then (c,r) else (r,c) := by
  have a := x.1.isLt; have b := x.2.isLt; unfold N at a b
  fin_cases g <;> norm_num [rwFlip,colFlip,swapAxis,small,invers,transform,Fin.ofNat,N] <;>
    (try simp (disch := omega) only [Nat.mod_eq_of_lt]) <;> omega

private theorem bit_view (F : Finset (Site k)) (g : Fin 8) (i : J k) (c : Nat) (hc : c<N k) :
    bit (view F g) (teeth k i) c = bit (source F g) (teeth k (rMap g i))
      (if colFlip g then 3*k-c else c) := by
  let p : Site k := (teeth k i,⟨c,hc⟩)
  let y := small (N k) (invers g) p
  let z : Fin (N k) := ⟨if colFlip g then 3*k-c else c,by unfold N at *; split <;> omega⟩
  have e := coords g p
  change (y.1.val,y.2.val)=_ at e
  have te (i : J k) : (teeth k i).val=3*i.val := rfl
  have row : (teeth k (rMap g i)).val=if rwFlip g then 3*k-3*i.val else 3*i.val := by
    rw [te]; unfold rMap; split <;> simp_all [flipJ]; have := i.isLt; omega
  have q : y=if swapAxis g then (z,teeth k (rMap g i)) else (teeth k (rMap g i),z) := by
    dsimp only [p,te] at e
    split <;> rename_i b <;> simp only [b,ite_true,ite_false,Bool.false_eq_true] at e <;>
      apply Prod.ext <;> apply Fin.ext <;> simp_all [z,Prod.ext_iff]
  have hz : (if colFlip g then 3*k-c else c)<N k := z.isLt
  simp only [bit,dif_pos hc,dif_pos hz,view_mem]
  change decide (y∈F)=decide ((teeth k (rMap g i),z)∈source F g)
  rw [q]; unfold source; split <;> simp

private theorem letter_view (F : Finset (Site k)) (g : Fin 8) (i j : J k) :
    L (view F g) i j =
    let a := L (source F g) (rMap g i) (cMap g j)
    if colFlip g then rev a else a := by
  have jlt := j.isLt
  have br (c : Nat) (hc : ¬c<N k) (S : Finset (Site k)) (r : Fin (N k)) : bit S r c=false := by simp [bit,hc]
  have m := bit_view F g i
  cases b : colFlip g <;> simp only [b,Bool.false_eq_true,if_false,if_true] at m ⊢
  · have z : cMap g j=j := by simp [cMap,b]
    rw [z]; unfold L letter
    congr 1
    · rw [m _ (by unfold N; omega)]
    · rw [m _ (by unfold N; omega)]
    · by_cases h : 3*j.val+1<N k
      · rw [m _ h]
      · rw [br _ h,br _ h]
  · have z : (cMap g j).val=k-j.val := by simp [cMap,b,flipJ]
    unfold rev L letter
    simp only [z]
    congr 1
    · by_cases h : j.val=0
      · simp [h,br _ (by unfold N; omega : ¬3*k+1<N k)]
      · rw [m _ (by unfold N; omega)]
        simp [show 0<j.val by omega,show 3*k-(3*j.val-1)=3*(k-j.val)+1 by omega]
    · rw [m _ (by unfold N; omega),show 3*k-3*j.val=3*(k-j.val) by omega]
    · by_cases h : j.val=k
      · simp [h,br _ (by unfold N; omega : ¬3*k+1<N k)]
      · rw [m _ (by unfold N; omega)]
        simp [show 0<k-j.val by omega,show 3*k-(3*j.val+1)=3*(k-j.val)-1 by omega]

private theorem rev_credit : ∀ a, localCredit (rev a)=localCredit a := by decide +kernel
private theorem rev_real : ∀ a b, realized (rev a) (rev b)=realized b a := by decide +kernel

private theorem jSum (f : J k → Int) (b : Bool) :
    ∑ i, f (if b then flipJ i else i)=∑ i, f i := by
  cases b
  · rfl
  · let e : J k ≃ J k := ⟨flipJ,flipJ,fun i => Fin.ext (by have := i.isLt; change k-(k-i.val)=_; omega),
      fun i => Fin.ext (by have := i.isLt; change k-(k-i.val)=_; omega)⟩
    exact e.sum_comp f

private theorem eSum (g : Fin 8) (f : Fin k → Int) :
    ∑ j, f (eMap g j)=∑ j, f j := by
  unfold eMap; split
  · let e : Fin k ≃ Fin k := ⟨flipE,flipE,fun i => Fin.ext (by have := i.isLt; change k-1-(k-1-i.val)=_; omega),
      fun i => Fin.ext (by have := i.isLt; change k-1-(k-1-i.val)=_; omega)⟩
    exact e.sum_comp f
  · rfl

private theorem credit_view (F : Finset (Site k)) (g : Fin 8) :
    axisCredit (view F g)=axisCredit (source F g) := by
  have c (i j : J k) : localCredit (L (view F g) i j)=
      localCredit (L (source F g) (rMap g i) (cMap g j)) := by
    rw [letter_view]; split <;> simp [rev_credit]
  have inner (i : J k) := jSum (fun j => localCredit (L (source F g) (rMap g i) j)) (colFlip g)
  simp only [axisCredit,c,cMap,inner]
  exact jSum (fun i => ∑ j, localCredit (L (source F g) i j)) (rwFlip g)

private theorem paths_view (F : Finset (Site k)) (g : Fin 8) :
    axisPaths (view F g)=axisPaths (source F g) := by
  let f (S : Finset (Site k)) (i : J k) (j : Fin k) := I (realized (L S i j.castSucc) (L S i j.succ))
  have c (i : J k) (j : Fin k) : f (view F g) i j=f (source F g) (rMap g i) (eMap g j) := by
    unfold f; rw [letter_view,letter_view]
    cases z : colFlip g <;> simp only [z,Bool.false_eq_true,if_false,if_true,cMap,eMap,rev_real]
    have a : flipJ j.succ=(flipE j).castSucc := Fin.ext (by dsimp [flipJ,flipE]; omega)
    have b : flipJ j.castSucc=(flipE j).succ := Fin.ext (by have := j.isLt; dsimp [flipJ,flipE]; omega)
    rw [a,b]
  rw [axisPaths_letters,axisPaths_letters]
  change ∑ i, ∑ j, f (view F g) i j=∑ i, ∑ j, f (source F g) i j
  simp only [c,eSum]
  exact jSum (fun i => ∑ j, f (source F g) i j) (rwFlip g)

private theorem plain_iff (F : Finset (Site k)) (i : J k) :
    Pitch F (teeth k i) ↔ ∀ j, L F i j=⟨false,true,false⟩ := by
  constructor
  · intro pitch j
    have b (c : Nat) : bit F (teeth k i) c=decide (c<N k ∧ c%3=0) := by
      unfold bit
      split
      next hc =>
        have eq (q : Fin (N k)) : (teeth k i,q)∈F ↔ q.val%3=0 := by
          have t : (teeth k i,q)∈rowTeeth k (teeth k i) ↔ q.val%3=0 := by
            simp only [rowTeeth,mem_image,mem_univ,true_and,Prod.mk.injEq]
            constructor
            · rintro ⟨u,_,rfl⟩; change 3*_%3=0; simp
            · intro yes; refine ⟨owner q,Fin.ext ?_⟩; change 3*((q.val+1)/3)=q.val; omega
          rw [←pitch] at t; simpa using t
        simp [eq,hc]
      next hc => simp [hc]
    have := j.isLt
    by_cases z : j.val=0 <;> simp [L,letter,b,z,N,show 3*j.val<3*k+1 by omega] <;> omega
  · intro h
    by_contra np
    have no := nonpitch_word F (teeth k i) np
    have atSlot {a} (m : a∈word F (teeth k i)) : a=⟨false,true,false⟩ := by
      obtain ⟨t,ht,rfl⟩ := List.mem_map.mp m
      exact h ⟨_,List.mem_range.mp ht⟩
    simp only [containsActive,containsVac,List.any_eq_true] at no
    rcases no with ⟨a,m,eq⟩|⟨a,m,eq⟩ <;> rw [atSlot m] at eq <;> contradiction

private theorem source_np (F : Finset (Site k)) (g : Fin 8)
    (rows : ∀ i, ¬Pitch F (teeth k i)) (cols : ∀ i, ¬Pitch (trans F) (teeth k i)) :
    ∀ i, ¬Pitch (source F g) (teeth k i) := by unfold source; split <;> assumption

theorem all_views_np (F : Finset (Site k))
    (rows : ∀ i, ¬Pitch F (teeth k i)) (cols : ∀ i, ¬Pitch (trans F) (teeth k i)) :
    ∀ g i, ¬Pitch (view F g) (teeth k i) := by
  intro g i h
  apply source_np F g rows cols (rMap g i)
  apply (plain_iff ..).mpr
  intro j
  have e := (plain_iff ..).mp h (cMap g j)
  rw [letter_view] at e
  have inv : cMap g (cMap g j)=j := by unfold cMap; split <;> first | rfl | apply Fin.ext; dsimp [flipJ]; have := j.isLt; omega
  rw [inv] at e
  split at e
  · have z := congrArg rev e; exact z
  · exact e

theorem eight_views_two_axes (F : Finset (Site k))
    (rows : ∀ i, ¬Pitch F (teeth k i)) (cols : ∀ i, ¬Pitch (trans F) (teeth k i)) :
    ∑ g : Fin 8, axisDebit (view F g)=4*(axisDebit F+axisDebit (trans F)) := by
  have eq (g : Fin 8) : axisDebit (view F g)=axisDebit (source F g) := by
    rw [axis_identity _ (all_views_np F rows cols g),axis_identity _ (source_np F g rows cols),
      credit_view,paths_view]
  simp only [eq,Fin.sum_univ_succ,Finset.univ_unique,Finset.sum_singleton]
  simp [source,swapAxis]; ring

theorem packed_debit_budget (F : Finset (Site k)) (hk : 6≤k) (acy : (G F).IsAcyclic)
    (rows : ∀ i, ¬Pitch F (teeth k i)) (cols : ∀ i, ¬Pitch (trans F) (teeth k i)) :
    (∑ p : Fin 8 × J k × J k, (debitKey k (line F p.1 p.2.1 p.2.2):Int))+
      8*((F.card:Int)+(sinks F).card+(exits F).card) ≤
      8*((N k:Int)*(k+1)+(F \ skeleton F).card) := by
  rw [eightfold_key_debit F hk (all_views_np F rows cols),eight_views_two_axes F rows cols]
  have nn (S : Finset (Site k)) : 0≤axisDebit S := sum_nonneg fun _ _ => Nat.cast_nonneg _
  linarith only [physical_debit_budget F acy rows cols,nn F,nn (trans F)]

end GridGraphs.NoPitch.Budget
