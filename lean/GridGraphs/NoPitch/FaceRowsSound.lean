import GridGraphs.NoPitch.FaceRows

namespace GridGraphs.NoPitch.FaceRows
open GridGraphs.NoPitch.Dual Keys PitchCut Wired Finset

def charges (D : Chart) := contribution D (index D) (signatures D)

private theorem child_inj : Function.Injective (fun z : FacePos 6 × Corner => child z.1 z.2) := by
  intro ⟨⟨a,b⟩,r,c⟩ ⟨⟨u,v⟩,i,j⟩ e
  have h := congrArg (fun p : PatchPos 6 => p.1.val) e
  have g := congrArg (fun p : PatchPos 6 => p.2.val) e
  dsimp [child,childAx] at h g
  simp only [Prod.mk.injEq,Fin.ext_iff]
  have := r.isLt; have := c.isLt; have := i.isLt; have := j.isLt; omega

private theorem child_or_missing : ∀ p : PatchPos 6, missing p ∨
    ∃ t : FacePos 6 × Corner, child t.1 t.2=p := by decide +kernel

private theorem patch_sum (D : Chart) (F : Finset (Site 6)) (ok : unusedOK D) (i : Nat) :
    (∑ p : PatchPos 6, coeff i (charges D (patch F p))) =
      ∑ p : FacePos 6, ∑ d : Corner, coeff i (charges D (patch F (child p d))) := by
  let g (t : FacePos 6 × Corner) := child t.1 t.2
  rw [←Fintype.sum_prod_type (fun t : FacePos 6 × Corner => coeff i (charges D (patch F (g t))))]
  rw [←sum_image (f:=fun p => coeff i (charges D (patch F p))) (s:=univ) (g:=g) child_inj.injOn]
  apply (sum_subset (subset_univ _) ?_).symm
  intro x _ absent
  rcases child_or_missing x with h|⟨t,rfl⟩
  · have z := of_decide_eq_true ok x h (patchMask F x)
    change charges D (patch F x)=[] at z
    rw [z]; rfl
  · exact (absent (mem_image_of_mem g (mem_univ t))).elim

private theorem append_coeff (i : Nat) (a b : Terms) : coeff i (a++b)=coeff i a+coeff i b := by
  simp [coeff]
private theorem kids_coeff (D : Chart) (F : Finset (Site 6)) (p : FacePos 6) (i : Nat) :
    coeff i (children (charges D) p (faceMask F p)) =
      ∑ d : Corner, coeff i (charges D (patch F (child p d))) := by
  have c : corners=[(0,0),(0,1),(1,0),(1,1)] := rfl
  simp only [children,c,List.flatMap_cons,List.flatMap_nil,List.append_nil,append_coeff,
    slice_eq,patch,Fintype.sum_prod_type,Fin.sum_univ_two]; ring

theorem local_tile (D : Chart) (ok : tileOK D) (m : Mask) (q : PartitionBits)
    (im : Fin 65536) (mask : maskOf im=m) (z : Nat) (part : partOf z=q) (cat : z∈catalog m)
    (raw : fresh initial (rawEdges m)) (p : FacePos 6) :
    balanced (charges D (faceCode p m q) ++ children (charges D) p m) := by
  unfold tileOK at ok
  simp only [decide_eq_true_eq] at ok
  have all := ok im
  rw [mask] at all
  have h := all raw z cat p
  simp only [Vector.getElem_ofFn] at h
  rw [part] at h
  have pos : ∀ p : FacePos 6, let j := (6*p.1.val+p.2.val)%36
    (Fin.ofNat 6 (j/6),Fin.ofNat 6 j)=p := by decide +kernel
  simpa only [charges,faceCode,pos p] using h

theorem projected_rows (D : Chart) (F : Finset (Site 6)) (out : Site 6 → Option (Fin 4))
    (other : otherOK D) (unused : unusedOK D) (rows : rowOK D) (positive : ∀ j : Fin D.cols.size, D.cols[j].units≠0)
    (tiles : ∀ p, balanced (charges D (face F p) ++ children (charges D) p (faceMask F p)))
    (i : Fin D.rows.size) (sel : selected D i) :
    rowHolds D.rows[i].sense (2*lhs D (physicalVector D F out) i) (8*D.rows[i].rhs.atStep 0) := by
  have outside (j : Fin D.cols.size) (nf : D.cols[j].key%8≠2) (np : D.cols[j].key%8≠4) :
      terms D D.cols[j]=[] := by
    have h := Array.all_eq_true_iff_forall_mem.mp other _ (Array.getElem_mem j.isLt)
    have : (D.cols[j].key%8==2 || D.cols[j].key%8==4 || (terms D D.cols[j]).isEmpty)=true := h
    simpa only [beq_eq_false_iff_ne.mpr nf,beq_eq_false_iff_ne.mpr np,Bool.false_or,List.isEmpty_iff] using this
  have no (key : Nat) (nf : key%8≠2) (np : key%8≠4) : charges D key=[] := by
    unfold charges contribution
    cases h : locate D (index D) key with
    | none => rfl
    | some j =>
      have eq := locate_key h
      simpa [signatures,j.isLt] using outside j (eq ▸ nf) (eq ▸ np)
  have stars (x : Site 6) : charges D (Keys.star F out x)=[] := by
    apply no <;> unfold Keys.star <;> cases decide (x∈F) <;> simp
  have lines (t : Fin 8 × Fin 7 × Fin 7) : charges D (line F t.1 t.2.1 t.2.2)=[] := by
    apply no <;> unfold line <;> dsimp only <;> omega
  have add (a b : Fin D.cols.size → Int) : lhs D (fun j => a j+b j) i=lhs D a i+lhs D b i := by
    simp [lhs,mul_add,sum_add_distrib]
  have aux : lhs D (fun j : Fin D.cols.size =>
      if D.cols[j].key%8=5 then complete F (D.cols[j].key/8) else 0) i=0 := by
    apply sum_eq_zero; intro j _
    by_cases h : D.cols[j].key%8=5
    · have hz := terms_coeff D i sel D.cols[j]
      rw [outside j (by omega) (by omega)] at hz
      -- `units` is positive for every decoded column, but `otherOK`
      -- must also kill an auxiliary term which is not multiplied by units.
      have prod : coeff i D.cols[j].terms*(D.cols[j].units:Int)=0 := hz.symm
      rw [(mul_eq_zero.mp prod).resolve_right (by exact_mod_cast positive j),zero_mul]
    · exact mul_eq_zero_of_right _ (if_neg h)
  have pairs (p : FacePos 6) := zero_of_balanced _ (tiles p) i
  simp only [append_coeff,kids_coeff] at pairs
  have balance := sum_congr (s₁:=univ) rfl (fun p _ => pairs p)
  rw [sum_add_distrib,←patch_sum D F unused] at balance
  have total : lhs D (physicalVector D F out) i=0 := by
    unfold physicalVector counts
    rw [add,add,add,add,aux]
    unfold charges at stars lines
    simp only [scatter_lhs D i sel,stars,lines,coeff,List.map_nil,List.sum_nil,sum_const_zero,
      zero_add,add_zero] at balance ⊢
    exact balance
  have bounds : 4711≤D.rows[i].source ∧ D.rows[i].source≤5172 := by
    simpa [selected,i.isLt] using sel
  have h := Array.all_eq_true_iff_forall_mem.mp rows _ (Array.getElem_mem i.isLt)
  have info : D.rows[i].sense=0 ∧ D.rows[i].rhs=⟨0,0,0⟩ := by
    simp at h
    exact h.resolve_left (fun z => z.elim (not_lt_of_ge bounds.1) (not_lt_of_ge bounds.2))
  rw [total,info.1,info.2]; simp [rowHolds,Poly.atStep]

end GridGraphs.NoPitch.FaceRows
