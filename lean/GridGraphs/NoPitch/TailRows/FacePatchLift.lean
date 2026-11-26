import GridGraphs.NoPitch.TailRows.FacePatchChecks

namespace GridGraphs.NoPitch.TailRows.FacePatch
open PitchCut Keys Wired FaceRows Budget LocalBoard19 GridGraphs.NoPitch.Dual Finset
variable {k : Nat}

private abbrev baseK (k : Nat) := if k%2=1 then 19 else 20
private def price (D : Chart) := contribution D (index D) (prices D (selector D))

private theorem patch_local (hk : 19≤k) (D : Chart) (ok : cert D (baseK k))
    (F : Finset (Site k)) (acy : (Budget.G F).IsAcyclic) (p : PatchPos k) :
    (locate D (index D) (patch F p)).isSome ∧ balanced (price D (patch F p) ++ negTerms
      (stamp (price D) (baseK k) (patchBand p) (p.1.val%3) (p.2.val%3) (patchMask F p))) := by
  obtain ⟨q,v⟩ := patch_rep hk p
  have key (a : Nine) : patchCode p a=patchCode q a := by
    unfold patchCode; unfold patchFine at v; simp only [v]
  obtain ⟨eq,r,c⟩ := patch_class hk (by unfold baseK; split <;> decide : 19≤baseK k) v
  have h := of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp ok).1).2 q _ (legal_patch F hk acy p)
  simpa only [patch,key,eq,r,c,price,selector,Bool.and_eq_true] using h

private theorem face_local (hk : 19≤k) (D : Chart) (ok : cert D (baseK k))
    (F : Finset (Site k)) (acy : (Budget.G F).IsAcyclic) (p : FacePos k) :
    (locate D (index D) (face F p)).isSome ∧ balanced (price D (face F p) ++
      kids (price D) (baseK k) (faceBand p) (faceMask F p)) := by
  let m := faceMask F p; let q := (faceAtom F p).2
  obtain ⟨lt,mask⟩ := mask_roundtrip m
  obtain ⟨mem,part⟩ := partition_roundtrip q (physical_partition F p)
  obtain ⟨raw,wire⟩ := physical_wiring p F acy
  have cat : colorCode q∈catalog m := List.mem_filter.mpr ⟨mem,by rwa [part]⟩
  have all := of_decide_eq_true (Bool.and_eq_true_iff.mp ok).2 (⟨_,lt⟩ : Fin 65536)
  dsimp only at all; rw [mask] at all
  have sc := List.all_eq_true.mp (all raw) _ cat
  have z := of_decide_eq_true sc (faceBand p)
  have pos : ∀ p : FacePos 3, let j := (3*p.1.val+p.2.val)%9
    (Fin.ofNat 3 (j/3),Fin.ofNat 3 j)=p := by decide
  change (locate D (index D) (keyAt p (faceViews m q))).isSome ∧ balanced
    (price D (keyAt p (faceViews m q)) ++ kids (price D) (baseK k) (faceBand p) m)
  rw [face_key (by omega)]
  simpa only [Vector.getElem_ofFn,pos,part,Bool.and_eq_true,price,selector] using z

/-- Actual catalogue lookups, including the global skeleton partition on the face. -/
theorem catalogue_of_cert (hk : 19≤k) (D : Chart) (ok : cert D (baseK k))
    (F : Finset (Site k)) (acy : (Budget.G F).IsAcyclic) :
    (∀ p, (locate D (index D) (face F p)).isSome) ∧ (∀ p, (locate D (index D) (patch F p)).isSome) :=
  ⟨fun p => (face_local hk D ok F acy p).1,fun p => (patch_local hk D ok F acy p).1⟩

private theorem project (D : Chart) (s : Nat → Bool) (ok : support D s)
    (F : Finset (Site k)) (o : Site k → Option (Fin 4)) (i : Fin D.rows.size) (h : s i) :
    lhs D (physicalVector D F o) i=
      (∑ p, lookupPrice D i (index D) (face F p))+∑ p, lookupPrice D i (index D) (patch F p) := by
  have kill {j : Fin D.cols.size} (n : D.cols[j].key%8≠2) (p : D.cols[j].key%8≠4) :
      coeff i D.cols[j].terms=0 := by
    have z := Array.all_eq_true_iff_forall_mem.mp ok _ (Array.getElem_mem j.isLt)
    simp only [Bool.or_eq_true,beq_iff_eq,List.all_eq_true,Bool.not_eq_true'] at z
    have absent := z.resolve_left (not_or.mpr ⟨n,p⟩)
    apply List.sum_eq_zero; intro t ht; obtain ⟨a,m,rfl⟩ := List.mem_map.mp ht
    have ne : a.1≠i.val := fun e => by have := absent a m; rw [e,h] at this; contradiction
    simp [ne]
  have no (key : Nat) (n : key%8≠2) (p : key%8≠4) : lookupPrice D i (index D) key=0 := by
    unfold lookupPrice; cases e : locate D (index D) key with
    | none => rfl
    | some j => change coeff i D.cols[j].terms*_=0; rw [kill (j:=j) ((locate_key e).symm ▸ n) ((locate_key e).symm ▸ p),zero_mul]
  have st (x : Site k) : lookupPrice D i (index D) (Keys.star F o x)=0 := by
    apply no <;> unfold Keys.star <;> cases decide (x∈F) <;> simp
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
  simp only [scatter_price,st,ln,sum_const_zero,zero_add,add_zero]

/-- Histogram cancellation: all non-seam patches are in the injective
four-child image, all seam patches have zero price. -/
theorem lifted (hk : 19≤k) (D : Chart) (ok : cert D (baseK k))
    (F : Finset (Site k)) (acy : (Budget.G F).IsAcyclic) (o : Site k → Option (Fin 4))
    (i : Fin D.rows.size) (h : selector D i) : lhs D (physicalVector D F o) i=0 := by
  let w := price D
  let pw (p : PatchPos k) := lookupPrice D i (index D) (patch F p)
  have eq (key : Nat) : coeff i (w key)=lookupPrice D i (index D) key := sig_price _ _ _ h key
  have pc (p : PatchPos k) : pw p = coeff i (stamp w (baseK k) (patchBand p)
      (p.1.val%3) (p.2.val%3) (patchMask F p)) := by
    have z := zero_of_balanced _ (patch_local hk D ok F acy p).2 i
    rw [coeff_append,coeff_neg,←sub_eq_add_neg] at z; exact (eq _).symm.trans (sub_eq_zero.mp z)
  have pairs (p : FacePos k) : lookupPrice D i (index D) (face F p)+(∑ d : Corner, pw (child p d))=0 := by
    have kick (d : Corner) : pw (child p d)=coeff i
        (stamp w (baseK k) (faceBand p) d.1 d.2 (slice (faceMask F p) d)) := by
      rw [pc,child_band,slice_eq]; congr 2 <;> dsimp [child,childAx] <;>
        have := d.1.isLt <;> have := d.2.isLt <;> omega
    have z := zero_of_balanced _ (face_local hk D ok F acy p).2 i
    rw [←eq]; rw [coeff_append] at z
    simpa only [kids,show corners=[(0,0),(0,1),(1,0),(1,1)] from rfl,List.flatMap_cons,List.flatMap_nil,
      List.append_nil,coeff_append,Fintype.sum_prod_type,Fin.sum_univ_two,kick,add_assoc,w] using z
  have patchSum : (∑ p, pw p)=∑ p : FacePos k, ∑ d : Corner, pw (child p d) := by
    let g (t : FacePos k × Corner) := child t.1 t.2
    rw [←Fintype.sum_prod_type (fun t : FacePos k × Corner => pw (g t)),←sum_image (f:=pw) (s:=univ) (g:=g) child_inj.injOn]
    apply (sum_subset (subset_univ _) ?_).symm; intro x _ absent
    rcases child_or_missing x with m|⟨t,rfl⟩
    · rw [pc,stamp,if_pos (by simpa [missing] using m)]; rfl
    · exact (absent (mem_image_of_mem g (mem_univ t))).elim
  rw [project D _ (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp ok).1).1 F o i h]
  change _+(∑ p, pw p)=0; rw [patchSum,←sum_add_distrib]; exact sum_eq_zero fun p _ => pairs p

end GridGraphs.NoPitch.TailRows.FacePatch
