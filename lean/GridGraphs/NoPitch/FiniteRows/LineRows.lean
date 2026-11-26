import GridGraphs.NoPitch.TailRows.Letters

namespace GridGraphs.NoPitch.FiniteRows
open PitchCut Keys Budget FaceRows LocalBoard19 GridGraphs.NoPitch.Dual Finset TailRows
variable {k : Nat}

private theorem directZero {k} {price A}
    (law : LocalLaw k price A) (F : Finset (Site k))
    (np : ∀ g r, ¬Pitch (view F g) (teeth k r)) :
    ∑ p : Fin 8 × J k × J k, price (line F p.1 p.2.1 p.2.2)=0 := by
  have one (g : Fin 8) (r : J k) : ∑ j : J k, price (line F g r j)=0 := by
    let s (n : Nat) := prefixState (view F g) (teeth k r) n
    let f (n : Nat) := if n=k+1 then 0 else before A k r n (s n)
    have eq (j : J k) : price (line F g r j)=f (j.val+1)-f j.val := by
      obtain ⟨hs,p⟩ := physical_step _ _ (np g r) j
      have h := law r j _ hs _ p
      have prev : 3*j.val-3=3*(j.val-1) := by omega
      change price (arcKey _ (if j.val=0 then 0 else axis (N k) 8 (3*j.val-3)+1) _ _ _)=_
      rw [prev]
      change price (arcKey (band k r) (prior k j) (band k j) _ _)=_
      change price (arcKey (band k r) (prior k j) (band k j) (s j) (advance (s j) (letter _ _ j)))=_
      rw [show price (arcKey (band k r) (prior k j) (band k j) (s j) (advance (s j) (letter _ _ j)))=_ from h]
      have := j.isLt
      by_cases l : j.val=k <;> simp [f,after,before,s,l,show j.val≠k+1 by omega,prefixState]
    simp only [eq]
    rw [Fin.sum_univ_eq_sum_range (fun n => f (n+1)-f n),sum_range_sub]
    simp [f,before]
  simp only [Fintype.sum_prod_type,one,sum_const_zero]

theorem flow {D : Chart} {k : Nat} {sel : Nat → Bool} (baseOK : certified D k sel)
    (hk : 7≤k) (F : Finset (Site k))
    (rows : ∀ r, ¬Pitch F (teeth k r)) (cols : ∀ r, ¬Pitch (trans F) (teeth k r))
    (o : Site k → Option (Fin 4)) (i : Fin D.rows.size) (h : sel i) (t : Int) :
    rowHolds D.rows[i].sense (2*lhs D (physicalVector D F o) i) (8*D.rows[i].rhs.atStep t) := by
  obtain ⟨first,test⟩ := Bool.and_eq_true_iff.mp baseOK
  obtain ⟨sup,metaInfo⟩ := Bool.and_eq_true_iff.mp first
  let A := node (table D sel)
  have law : LocalLaw k (lookupPrice D i (index D)) (fun y j s => coeff i (A y j s)) := by
    intro r j s hs l pass
    have eq := zero_of_balanced _ (of_decide_eq_true test r j s hs l pass) i
    rw [coeff_append,coeff_append,coeff_neg,sig_price D sel i h] at eq
    have zero : coeff i []=0 := rfl
    by_cases start : j.val=0 <;> by_cases last : j.val=k <;>
      simp only [before,after,start,last,if_true,if_false,zero,A,
        if_neg (by omega : k≠0),if_neg (by omega : 0≠k)] at eq ⊢ <;> omega
  have z := directZero law F (all_views_np F rows cols)
  have m := of_decide_eq_true metaInfo i h
  rw [line_only_lhs F o i sel h sup,z,m.1,m.2]; simp [rowHolds,Poly.atStep]

private theorem coeff_stamp {k} (A : Nat → Nat → Letter → Terms) (x : Site k) (g f bits i) :
    coeff i (stamp A x g f bits)=atView (fun r j a => coeff i (A r j a)) x g f bits := by
  unfold TailRows.stamp atView; dsimp only; split <;> rfl

theorem letters {k} (hk : 7≤k) (D : Chart) (sel : Nat → Bool)
    (ok : certLetters D k sel)
    (F : Finset (Site k)) (acy : (G F).IsAcyclic)
    (rows : ∀ r, ¬Pitch F (teeth k r)) (cols : ∀ r, ¬Pitch (trans F) (teeth k r))
    (i : Fin D.rows.size) (h : sel i) (t : Int) :
    rowHolds D.rows[i].sense (2*lhs D (physicalVector D F (out F)) i) (8*D.rows[i].rhs.atStep t) := by
  obtain ⟨p,stars⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨p,arcs⟩ := Bool.and_eq_true_iff.mp p
  obtain ⟨sup,metaInfo⟩ := Bool.and_eq_true_iff.mp p
  let w := lookupPrice D i (index D)
  let A := mark (ltable D sel)
  let value := fun r j a => coeff i (A r j a)
  have st (x : Site k) : w (Keys.star F (out F) x)=
      -(∑ g, atView value x g (decide (x∈F)) (bitsAt F x)) := by
    have z := of_decide_eq_true (of_decide_eq_true stars x) _ _ _ (physical_admissible F acy x)
    have eq := zero_of_balanced _ z i
    rw [coeff_append,sig_price D sel i h] at eq
    simp only [finCoeff,coeff_stamp] at eq
    rw [physical_sKey] at eq
    change w _+ (∑ g, atView value x g (decide (x∈F)) (bitsAt F x))=0 at eq
    exact eq_neg_of_add_eq_zero_left eq
  have ln (p : Fin 8 × J k × J k) : w (line F p.1 p.2.1 p.2.2)=
      value (band k p.2.1) (band k p.2.2) (L (view F p.1) p.2.1 p.2.2) := by
    obtain ⟨hs,pass⟩ := physical_step _ _ (all_views_np F rows cols p.1 p.2.1) p.2.2
    have z := of_decide_eq_true arcs p.2.1 p.2.2 _ hs _ pass
    have eq := zero_of_balanced _ z i
    rw [coeff_append,coeff_neg,sig_price D sel i h] at eq
    have prev : 3*p.2.2.val-3=3*(p.2.2.val-1) := by omega
    unfold line; dsimp only; rw [prev]
    exact eq_of_sub_eq_zero eq
  have kill {j : Fin D.cols.size} (n : 2≤D.cols[j].key%8) (p : D.cols[j].key%8≠3) : coeff i D.cols[j].terms=0 := by
    have z := Array.all_eq_true_iff_forall_mem.mp sup _ (Array.getElem_mem j.isLt)
    simp only [Bool.or_eq_true,decide_eq_true_eq,beq_iff_eq,List.all_eq_true,Bool.not_eq_true'] at z
    have absent := z.resolve_left (not_or.mpr ⟨not_lt.mpr n,p⟩)
    apply List.sum_eq_zero; intro t ht; obtain ⟨a,m,rfl⟩ := List.mem_map.mp ht
    have ne : a.1≠i.val := fun e => by have := absent a m; rw [e,h] at this; contradiction
    simp [ne]
  have no (key : Nat) (n : 2≤key%8) (p : key%8≠3) : w key=0 := by
    unfold w lookupPrice
    cases e : locate D (index D) key with
    | none => rfl
    | some j => change coeff i D.cols[j].terms*_=0; rw [kill (j:=j) ((locate_key e).symm ▸ n) ((locate_key e).symm ▸ p),zero_mul]
  have fa (p : FacePos k) : w (face F p)=0 := by apply no <;> unfold face faceCode keyAt <;> omega
  have pa (p : PatchPos k) : w (patch F p)=0 := by apply no <;> unfold patch patchCode <;> omega
  have add (u v : Fin D.cols.size → Int) : lhs D (fun j => u j+v j) i=lhs D u i+lhs D v i := by
    simp [lhs,mul_add,sum_add_distrib]
  have aux : lhs D (fun j : Fin D.cols.size =>
      if D.cols[j].key%8=5 then complete F (D.cols[j].key/8) else 0) i=0 := by
    apply sum_eq_zero; intro j _; dsimp only; split <;> rename_i q
    · rw [kill (j:=j) (by omega) (by omega),zero_mul]
    · simp
  have zero : lhs D (physicalVector D F (out F)) i=0 := by
    unfold physicalVector GridGraphs.NoPitch.Dual.counts; rw [add,add,add,add,aux]
    simp only [scatter_price]
    change (∑ x, w (Keys.star F (out F) x))+(∑ p, w (face F p))+
      (∑ p : Fin 8 × J k × J k, w (line F p.1 p.2.1 p.2.2))+(∑ p, w (patch F p))+0=0
    simp only [st,ln,fa,pa,sum_const_zero,add_zero,sum_neg_distrib]
    rw [sum_comm (s:=univ (α:=Site k)) (t:=univ (α:=Fin 8))]
    simp only [letter_frequencies F _ value]; simp only [Fintype.sum_prod_type,neg_add_cancel]
  have metaEq := of_decide_eq_true metaInfo i h
  rw [zero,metaEq.1,metaEq.2]; simp [rowHolds,Poly.atStep]


end GridGraphs.NoPitch.FiniteRows
