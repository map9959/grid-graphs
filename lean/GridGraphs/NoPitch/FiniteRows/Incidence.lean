import GridGraphs.NoPitch.FiniteRows.PatchLegal
import GridGraphs.NoPitch.FiniteRows.Conservation

namespace GridGraphs.NoPitch.FiniteRows
open PitchCut Keys Budget FaceRows LocalBoard19 GridGraphs.NoPitch.Dual Finset TailRows TailRows.Incidence
variable {k : Nat}

theorem starPatchLhs {k} (D : Chart) (s : Nat → Bool) (ok : supported D s)
    (F : Finset (Site k)) (i : Fin D.rows.size) (h : s i) :
    lhs D (physicalVector D F (out F)) i=
      (∑ x, lookupPrice D i (index D) (Keys.star F (out F) x))+∑ p, lookupPrice D i (index D) (patch F p) := by
  have kill {j : Fin D.cols.size} (n : 2≤D.cols[j].key%8) (p : D.cols[j].key%8≠4) :
      coeff i D.cols[j].terms=0 := by
    have z := Array.all_eq_true_iff_forall_mem.mp ok _ (Array.getElem_mem j.isLt)
    simp only [Bool.or_eq_true,decide_eq_true_eq,beq_iff_eq,List.all_eq_true,Bool.not_eq_true'] at z
    have absent := z.resolve_left (not_or.mpr ⟨not_lt.mpr n,p⟩)
    apply List.sum_eq_zero; intro t ht; obtain ⟨a,m,rfl⟩ := List.mem_map.mp ht
    have ne : a.1≠i.val := fun e => by have := absent a m; rw [e,h] at this; contradiction
    simp [ne]
  have no (key : Nat) (n : 2≤key%8) (p : key%8≠4) : lookupPrice D i (index D) key=0 := by
    unfold lookupPrice; cases e : locate D (index D) key with
    | none => rfl
    | some j => change coeff i D.cols[j].terms*_=0; rw [kill (j:=j) ((locate_key e).symm ▸ n) ((locate_key e).symm ▸ p),zero_mul]
  have fa (p : FacePos k) : lookupPrice D i (index D) (face F p)=0 := by apply no <;> unfold face faceCode keyAt <;> omega
  have ln (p : Fin 8 × J k × J k) : lookupPrice D i (index D) (line F p.1 p.2.1 p.2.2)=0 := by
    apply no <;> unfold line <;> dsimp only <;> omega
  have add (u v : Fin D.cols.size → Int) : lhs D (fun j => u j+v j) i=lhs D u i+lhs D v i := by
    simp [lhs,mul_add,sum_add_distrib]
  have aux : lhs D (fun j : Fin D.cols.size =>
      if D.cols[j].key%8=5 then complete F (D.cols[j].key/8) else 0) i=0 := by
    apply sum_eq_zero; intro j _; dsimp only; split <;> rename_i q
    · rw [kill (j:=j) (by omega) (by omega),zero_mul]
    · simp
  unfold physicalVector GridGraphs.NoPitch.Dual.counts; rw [add,add,add,add,aux]
  simp only [scatter_price,fa,ln,sum_const_zero,add_zero]

private theorem star_checked {b} {w : Nat → Terms} {B : Book} (x : Site b) (h : starCheck w B x)
    (bits f o) (ok : admissible x bits f o) :
    balanced (w (sKey x f bits o) ++ negTerms (stampStar B (starFine x) f bits o)) := by
  simpa only [Fin.getElem_fin,Vector.getElem_ofFn,Fin.eta,stampStar,edgeAt,socketAt] using of_decide_eq_true h bits f o ok
private theorem patch_checked {b} {w : Nat → Terms} {B : Book} (p : PatchPos b) (h : patchCheck w B p)
    (a) (ok : legal a) :
    balanced (w (patchCode p a) ++ negTerms (stampPatch B (patchFine p) a)) := by
  simpa only [Fin.getElem_fin,Vector.getElem_ofFn,Fin.eta,stampPatch,pairAt,plugAt] using of_decide_eq_true h a ok

private theorem offsets_coeff (i : Nat) (f : Q → Terms) :
    coeff i (offsets.flatMap f)=∑ q, coeff i (f q) := by
  have h : offsets.Nodup ∧ offsets.toFinset=univ := by decide +kernel
  rw [flatCoeff,←List.sum_toFinset _ h.1,h.2]

theorem incidence {k} (hk : 7≤k) (D : Chart) (B : Book)
    (ok : Incidence.cert D B k) (F : Finset (Site k)) (acy : (G F).IsAcyclic)
    (i : Fin D.rows.size) (hi : B.sel i) : lhs D (physicalVector D F (out F)) i=0 := by
  obtain ⟨z,ps⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨sup,st⟩ := Bool.and_eq_true_iff.mp z
  have star (x : Site k) : lookupPrice D i (index D) (Keys.star F (out F) x)=
      (∑ d, edgeAmt B F i x d)+∑ q, socketAmt B F i x q := by
    have eq := zero_of_balanced _ (star_checked x (of_decide_eq_true st x) _ _ _
      (physical_admissible F acy x)) i
    rw [coeff_append,coeff_neg,sig_price _ _ _ hi,physical_sKey] at eq
    simpa only [stampStar,coeff_append,finCoeff,offsets_coeff,viewSum,edgeAmt,socketAmt] using eq_of_sub_eq_zero eq
  have pa (p : PatchPos k) : lookupPrice D i (index D) (patch F p)=
      (∑ d, pairAmt B F i p d)-(∑ q, plugAmt B F i p q) := by
    have eq := zero_of_balanced _ (patch_checked p (of_decide_eq_true ps p) _ (legal_small F hk acy p)) i
    rw [coeff_append,coeff_neg,sig_price _ _ _ hi] at eq
    simpa only [patch,stampPatch,coeff_append,coeff_neg,finCoeff,offsets_coeff,viewSum,pairAmt,plugAmt,sub_eq_add_neg]
      using eq_of_sub_eq_zero eq
  rw [starPatchLhs D B.sel sup F i hi]
  simp only [star,pa,sum_add_distrib,sum_sub_distrib,edge_small hk B F acy,pair_small hk B F,cell_small hk B F]
  ring

end GridGraphs.NoPitch.FiniteRows
