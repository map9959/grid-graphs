import GridGraphs.NoPitch.FaceLineIncidence

namespace GridGraphs.NoPitch.FaceLines
open GridGraphs.NoPitch.Dual Keys PitchCut Wired FaceRows Finset

private theorem entry_coeff (i : Nat) (sel : kept i) (c : Col) :
    coeff i (entries c)=coeff i c.terms*c.units := by
  unfold entries
  induction c.terms with
  | nil => simp [coeff]
  | cons t ts ih =>
    rcases t with ⟨j,v⟩
    by_cases e : j=i
    · subst j; simp [coeff,sel,add_mul] at ih ⊢; omega
    · cases h : kept j <;> simp [coeff,h,e] at ih ⊢ <;> exact ih

private theorem scatter_row {I : Type*} [Fintype I] (D : Chart) (i : Fin D.rows.size)
    (sel : kept i) (keys : I → Nat) : lhs D (scatter D (index D) keys) i =
      ∑ x, coeff i (FaceLines.charges D (keys x)) := by
  unfold lhs scatter; simp_rw [mul_sum]; rw [sum_comm]
  apply sum_congr rfl; intro x _
  cases h : locate D (index D) (keys x) with
  | none => simp [FaceLines.charges,contribution,h,coeff]
  | some j =>
    rw [sum_eq_single j]
    · simpa [FaceLines.charges,contribution,h,j.isLt] using (entry_coeff i sel D.cols[j]).symm
    · intro b _ ne; simp [Ne.symm ne]
    · simp

private theorem append_coeff (i : Nat) (a b : Terms) : coeff i (a++b)=coeff i a+coeff i b := by
  simp [coeff]

private theorem neg_coeff (i : Nat) (a : Terms) : coeff i (neg a) = -coeff i a := by
  induction a with
  | nil => simp [coeff,neg]
  | cons t ts ih =>
    rcases t with ⟨j,v⟩
    by_cases e : j=i <;> simp [coeff,neg,e] at ih ⊢ <;> omega

theorem tile_balance (D : Chart) (ok : tileCheck D) (m : Mask) (q : PartitionBits)
    (im : Fin 65536) (mask : maskOf im=m) (z : Nat) (part : partOf z=q) (cat : z∈catalog m)
    (raw : fresh initial (rawEdges m)) (p : Pos) :
    balanced (FaceLines.charges D (faceCode p m q) ++ neg (rotStamps m p)) := by
  unfold tileCheck at ok
  simp only [decide_eq_true_eq] at ok
  have all := ok im
  rw [mask] at all
  have h := all raw z cat p
  simp only [Vector.getElem_ofFn] at h
  rw [part] at h
  have pos : ∀ p : Pos, let j := (6*p.1.val+p.2.val)%36
    (Fin.ofNat 6 (j/6),Fin.ofNat 6 j)=p := by decide +kernel
  simpa only [faceCode,pos p] using h

theorem step_balance (D : Chart) (ok : stepCheck D) (F : Finset (Site 6))
    (np : ∀ v, ¬(Pitch F v ∨ Pitch (transpose F) v)) (t : Fin 8 × Slot) :
    balanced (FaceLines.charges D (line F t.1 t.2.1 t.2.2) ++
      lineStamps t.2 (startAt F t.1 t.2) (stopAt F t.1 t.2)) := by
  have h := LineKeys.physical_step _ _ (LineKeys.rotated_no_pitch F np t.1 (teeth 6 t.2.1)) t.2.2
  exact of_decide_eq_true ok t.2.1 t.2.2 _ h.1 _ h.2

theorem projected_line_rows (D : Chart) (F : Finset (Site 6)) (out : Site 6 → Option (Fin 4))
    (np : ∀ v, ¬(Pitch F v ∨ Pitch (transpose F) v)) (steps : stepCheck D)
    (other : otherCheck D) (metadata : metaCheck D) (positive : ∀ j : Fin D.cols.size, D.cols[j].units≠0)
    (tiles : ∀ p, balanced (FaceLines.charges D (face F p) ++ neg (rotStamps (faceMask F p) p)))
    (i : Fin D.rows.size) (sel : kept i) :
    rowHolds D.rows[i].sense (2*lhs D (physicalVector D F out) i) (8*D.rows[i].rhs.atStep 0) := by
  have outside (j : Fin D.cols.size) (nf : D.cols[j].key%8≠2) (nl : D.cols[j].key%8≠3) :
      entries D.cols[j]=[] := by
    have h := Array.all_eq_true_iff_forall_mem.mp other _ (Array.getElem_mem j.isLt)
    have : (D.cols[j].key%8==2 || D.cols[j].key%8==3 || (entries D.cols[j]).isEmpty)=true := h
    simpa only [beq_eq_false_iff_ne.mpr nf,beq_eq_false_iff_ne.mpr nl,Bool.false_or,List.isEmpty_iff] using this
  have no (key : Nat) (nf : key%8≠2) (nl : key%8≠3) : FaceLines.charges D key=[] := by
    unfold FaceLines.charges contribution
    cases h : locate D (index D) key with
    | none => rfl
    | some j =>
      have eq := locate_key h
      simpa [j.isLt] using outside j (eq ▸ nf) (eq ▸ nl)
  have stars (x : Site 6) : FaceLines.charges D (Keys.star F out x)=[] := by
    apply no <;> unfold Keys.star <;> cases decide (x∈F) <;> simp
  have patches (p : PatchPos 6) : FaceLines.charges D (patch F p)=[] := by
    apply no <;> unfold patch patchCode <;> omega
  have add (a b : Fin D.cols.size → Int) : lhs D (fun j => a j+b j) i=lhs D a i+lhs D b i := by
    simp [lhs,mul_add,sum_add_distrib]
  have aux : lhs D (fun j : Fin D.cols.size =>
      if D.cols[j].key%8=5 then complete F (D.cols[j].key/8) else 0) i=0 := by
    apply sum_eq_zero; intro j _
    by_cases h : D.cols[j].key%8=5
    · have hz := entry_coeff i sel D.cols[j]
      rw [outside j (by omega) (by omega)] at hz
      have prod : coeff i D.cols[j].terms*(D.cols[j].units:Int)=0 := hz.symm
      rw [(mul_eq_zero.mp prod).resolve_right (by exact_mod_cast positive j),zero_mul]
    · exact mul_eq_zero_of_right _ (if_neg h)
  have faces (p : Pos) : coeff i (FaceLines.charges D (face F p)) = coeff i (rotStamps (faceMask F p) p) := by
    have h := zero_of_balanced _ (tiles p) i
    rw [append_coeff,neg_coeff] at h; omega
  have lines (t : Fin 8 × Slot) : coeff i (FaceLines.charges D (line F t.1 t.2.1 t.2.2)) =
      -coeff i (lineStamps t.2 (startAt F t.1 t.2) (stopAt F t.1 t.2)) := by
    have h := zero_of_balanced _ (step_balance D steps F np t) i
    rw [append_coeff] at h; omega
  have total : lhs D (physicalVector D F out) i=0 := by
    unfold physicalVector counts
    rw [add,add,add,add,aux]
    have nil_coeff : coeff i []=0 := rfl
    simp only [scatter_row D i sel,stars,patches,nil_coeff,sum_const_zero,zero_add,add_zero]
    rw [sum_congr rfl (fun p _ => faces p), sum_congr rfl (fun t _ => lines t),
      sum_neg_distrib,physical_balance,add_neg_cancel]
  unfold metaCheck at metadata
  simp only [decide_eq_true_eq] at metadata
  have info := (metadata i).2 sel
  rw [total,info.1,info.2]; simp [rowHolds,Poly.atStep]

end GridGraphs.NoPitch.FaceLines
