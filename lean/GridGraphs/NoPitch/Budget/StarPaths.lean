import GridGraphs.NoPitch.Budget.StarEvents

namespace GridGraphs.NoPitch.Budget
open SimpleGraph PitchCut Finset Keys
variable {k : Nat}

private theorem score_pair : ∀ a b c d : Bool,
    c.toNat*(if b then 1 else 2*a.toNat)+b.toNat*(if c then 1 else 2*d.toNat) =
      2*((a || b) && (b || c) && (c || d)).toNat := by decide +kernel

private theorem segment_path (F : Finset (Site k)) (s : Seg k) :
    pathBit (point s 1) (decide (point s 1∈F)) (bitsAt F (point s 1)) +
    pathBit (point s 2) (decide (point s 2∈F)) (bitsAt F (point s 2)) =
      2*(decide (live F s)).toNat := by
  rcases s with ⟨b,i,j⟩
  let s : Seg k := (b,i,j)
  let m (t : Fin 4) := decide (point s t∈F)
  have tooth (i : J k) : (teeth k i).val=3*i.val := rfl
  have rim (t : Fin 4) : onRim (point s t) := by cases b <;> simp [point,s,onRim,tooth]
  have nj (t : Fin 4) (h : t=1 ∨ t=2) : ¬isJoint (point s t) := by
    rcases h with rfl|rfl <;> cases b <;> simp [isJoint,point,s,coord,tooth,Nat.add_mod]
  have conn (u v : Fin 4) (h : u.val+1=v.val) :
      (base F).Adj (point s u) (point s v) ↔ point s u∈F ∨ point s v∈F := by
    have a : (gridGraph (N k) (N k)).Adj (point s u) (point s v) := by
      change adjacent _ _ _ _; cases b <;> simp [point,s,adjacent,coord,Fin.ext_iff] <;> omega
    change (_ ∧ (_ ∈ skeleton F ∨ _ ∈ skeleton F)) ↔ _
    simp only [a,true_and,skeleton,mem_filter]
    exact or_congr (and_iff_left (rim u)) (and_iff_left (rim v))
  have eq : decide (live F s)=((m 0 || m 1) && (m 1 || m 2) && (m 2 || m 3)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq,m,Bool.and_eq_true,Bool.or_eq_true,and_assoc]
    exact and_congr (conn 0 1 rfl) (and_congr (conn 1 2 rfl) (conn 2 3 rfl))
  change pathBit (point s 1) (m 1) _+pathBit (point s 2) (m 2) _=2*_
  rw [eq]
  simp only [pathBit,if_pos (And.intro (rim 1) (nj 1 (.inl rfl))),
    if_pos (And.intro (rim 2) (nj 2 (.inr rfl)))]
  have mov (t u : Fin 4) (d : Fin 4) (a : (point s t).1.val+(if d.val=1 then 1 else if d.val=3 then -1 else 0 : Int)=(point s u).1.val)
      (c : (point s t).2.val+(if d.val=0 then 1 else if d.val=2 then -1 else 0 : Int)=(point s u).2.val) :
      bitsAt F (point s t) d=m u := by
    unfold bitsAt probe
    simp only [a,c,Int.natCast_nonneg,Int.toNat_natCast,Fin.is_lt,and_self,dif_pos,Option.any_some,m]
  have z (t u : Fin 4) (off : Fin 4) (h : (t,u,off)∈
      ([(1,0,0),(1,2,2),(2,3,0),(2,1,2)] : List (Fin 4 × Fin 4 × Fin 4))) :
      bitsAt F (point s t) (toward (point s t)+off)=m u := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩ <;> cases b <;>
      apply mov <;> norm_num [toward,point,s,coord,tooth,Nat.add_mod,Fin.add_def] <;> omega
  have a := z 1 0 0 (by decide); have d := z 2 3 0 (by decide)
  simp only [add_zero] at a d
  rw [a,d,z 1 2 2 (by decide),z 2 1 2 (by decide)]
  exact score_pair .. 

private def slotPoint (p : Seg k × Fin 2) := point p.1 (if p.2=0 then 1 else 2)
private theorem slot_inj : Function.Injective (slotPoint (k:=k)) := by
  rintro ⟨⟨a,i,j⟩,p⟩ ⟨⟨b,u,v⟩,q⟩ h
  have a₁ := congrArg (fun x : Site k => x.1.val) h
  have a₂ := congrArg (fun x : Site k => x.2.val) h
  have tooth (i : J k) : (teeth k i).val=3*i.val := rfl
  cases a <;> cases b <;> fin_cases p <;> fin_cases q <;>
    norm_num [slotPoint,point,tooth,coord,Prod.ext_iff,Fin.ext_iff] at a₁ a₂ ⊢ <;> omega

private theorem covered {x : Site k} (rim : onRim x) (nj : ¬isJoint x) :
    ∃ p, slotPoint p=x := by
  have a := x.1.isLt; have c := x.2.isLt; unfold N at a c
  rcases rim with h|h
  · have nc : x.2.val%3≠0 := fun z => nj ⟨h,z⟩
    let j : Fin k := ⟨x.2.val/3,by omega⟩
    refine ⟨((false,owner x.1,j),if x.2.val%3=1 then 0 else 1),?_⟩
    by_cases e : x.2.val%3=1 <;> apply Prod.ext <;> apply Fin.ext <;>
      simp [slotPoint,point,e,coord,owner,j,teeth] <;> first | omega | change 3*((_+1)/3)=_; omega
  · have nr : x.1.val%3≠0 := fun z => nj ⟨z,h⟩
    let j : Fin k := ⟨x.1.val/3,by omega⟩
    refine ⟨((true,owner x.2,j),if x.1.val%3=1 then 0 else 1),?_⟩
    by_cases e : x.1.val%3=1 <;> apply Prod.ext <;> apply Fin.ext <;>
      simp [slotPoint,point,e,coord,owner,j,teeth] <;> first | omega | change 3*((_+1)/3)=_; omega

theorem pathBit_sum (F : Finset (Site k)) :
    ∑ x, pathBit x (decide (x∈F)) (bitsAt F x)=2*(liveSegs F).card := by
  let f (x : Site k) := pathBit x (decide (x∈F)) (bitsAt F x)
  have z : ∑ x, f x=∑ x ∈ univ.image slotPoint, f x := by
    symm; apply sum_subset (subset_univ _)
    intro x _ no
    by_cases h : onRim x ∧ ¬isJoint x
    · obtain ⟨p,rfl⟩ := covered h.1 h.2; exact False.elim (no (mem_image_of_mem _ (mem_univ p)))
    · simp [f,pathBit,h]
  change ∑ x, f x=_
  rw [z,sum_image slot_inj.injOn,Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two,slotPoint,if_true,if_neg (by decide : (1:Fin 2)≠0),f,segment_path,
    ←mul_sum,liveSegs,card_filter]
  congr 1; apply sum_congr rfl; intro s _
  by_cases h : live F s <;> simp [h]

end GridGraphs.NoPitch.Budget
