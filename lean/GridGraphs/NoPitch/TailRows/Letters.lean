import GridGraphs.NoPitch.TailRows.LetterChecks

namespace GridGraphs.NoPitch.TailRows
open PitchCut Keys Budget FaceRows LocalBoard19 GridGraphs.NoPitch.Dual TailCoverage Finset
attribute [local irreducible] chart58 chart61

private theorem arc_transport {b k} (hb : 19≤b) (hk : b≤k) {w A} (ok : arcCheck b w A)
    (r j : J k) (s : State) (hs : s∈layers (min j.val 4)) (a : Letter) (p : permit k j.val s a) :
    balanced (w (arcKey (band k r) (prior k j) (band k j) s (advance s a)) ++ negTerms (A (band k r) (band k j) a)) := by
  have R := rep_geometry hb hk (j:=r.val) (by omega)
  have C := rep_geometry hb hk (j:=j.val) (by omega)
  let u : J b := ⟨rep k b r,by have := R.1; omega⟩
  let v : J b := ⟨rep k b j,by have := C.1; omega⟩
  have ub : band b u=band k r := R.2.2.2.2.1
  have vb : band b v=band k j := C.2.2.2.2.1
  have vp : prior b v=prior k j := C.2.2.2.2.2
  have cl : min v.val 4=min j.val 4 := C.2.2.2.1
  have first : (v.val==0)=(j.val==0) := Bool.eq_iff_iff.mpr (by simpa only [beq_iff_eq] using C.2.1)
  have last : (v.val==b)=(j.val==k) := Bool.eq_iff_iff.mpr (by simpa only [beq_iff_eq] using C.2.2.1)
  have ps : permit b v.val s a := by simpa only [permit,bne,first,last] using p
  simpa only [ub,vp,vb] using of_decide_eq_true ok u v s (cl ▸ hs) a ps

private theorem coeff_stamp {k} (A : Nat → Nat → Letter → Terms) (x : Site k) (g f bits i) :
    coeff i (stamp A x g f bits)=atView (fun r j a => coeff i (A r j a)) x g f bits := by
  unfold stamp atView; dsimp only; split <;> rfl

theorem lifted_letters {k} (hk : 19≤k) (D : Chart) (sel : Nat → Bool)
    (ok : certLetters D (if k%2=1 then 19 else 20) sel)
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
    obtain ⟨y,hy⟩ := type_rep hk x
    have z := of_decide_eq_true (of_decide_eq_true stars y) _ _ _ (type_adm hy (physical_admissible F acy x))
    have eq := zero_of_balanced _ z i
    rw [coeff_append,sig_price D sel i h] at eq
    simp only [finCoeff,coeff_stamp] at eq
    rw [←type_key hy,physical_sKey] at eq
    change w _+ (∑ g, atView value y g (decide (x∈F)) (bitsAt F x))=0 at eq
    simp only [type_view hy value] 
    exact eq_neg_of_add_eq_zero_left eq
  have ln (p : Fin 8 × J k × J k) : w (line F p.1 p.2.1 p.2.2)=
      value (band k p.2.1) (band k p.2.2) (L (view F p.1) p.2.1 p.2.2) := by
    obtain ⟨hs,pass⟩ := physical_step _ _ (all_views_np F rows cols p.1 p.2.1) p.2.2
    have z := arc_transport (b:=if k%2=1 then 19 else 20)
      (by split <;> decide) (by split <;> omega) arcs p.2.1 p.2.2 _ hs _ pass
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

def letterSelected (k : Nat) := if k%2=1 then letters58 else letters61
theorem letters_tail {k : Nat} (hk : 19≤k) (F : Finset (Site k)) (acy : (G F).IsAcyclic)
    (rows : ∀ r, ¬Pitch F (teeth k r)) (cols : ∀ r, ¬Pitch (trans F) (teeth k r))
    (i : Fin (tailChart k).rows.size) (h : letterSelected k i) (t : Int) :
    rowHolds (tailChart k).rows[i].sense (2*lhs (tailChart k) (physicalVector (tailChart k) F (out F)) i)
      (8*(tailChart k).rows[i].rhs.atStep t) := by
  apply lifted_letters hk _ _ _ F acy rows cols i h t
  by_cases odd : k%2=1 <;> simp [tailChart,letterSelected,odd,lettersOK58,lettersOK61]

end GridGraphs.NoPitch.TailRows
