import GridGraphs.NoPitch.TailRows.FaceLineReplay
import GridGraphs.NoPitch.TailRows.FaceLineTransport
import GridGraphs.NoPitch.TailRows.FaceLineGeometry

namespace GridGraphs.NoPitch.TailRows.FaceLine
open PitchCut Keys FaceRows Wired Budget LocalBoard19 GridGraphs.NoPitch.Dual TailCoverage Finset
attribute [local irreducible] chart58 chart61

private theorem lift {D : Chart} {B : Book} {k b : Nat} (ok : cert D B b)
    (hb : 19≤b) (hk : b≤k) (F : Finset (Site k)) (acy : (Budget.G F).IsAcyclic)
    (rows : ∀ r, ¬Pitch F (teeth k r)) (cols : ∀ r, ¬Pitch (trans F) (teeth k r))
    (o : Site k → Option (Fin 4)) (i : Fin D.rows.size) (h : (supportMasks D)[i]! = 12) :
    lhs D (physicalVector D F o) i=0 := by
  have : NeZero k := ⟨by omega⟩
  obtain ⟨u,tiles⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨u,arcs⟩ := Bool.and_eq_true_iff.mp u
  obtain ⟨m,sup⟩ := Bool.and_eq_true_iff.mp u
  have sel : B.sel i = true := (of_decide_eq_true m i).mp h
  have kill (j : Fin D.cols.size) (nf : D.cols[j].key%8≠2) (nl : D.cols[j].key%8≠3) :
      coeff i D.cols[j].terms=0 := by
    have q := Array.all_eq_true_iff_forall_mem.mp sup _ (Array.getElem_mem j.isLt)
    change (D.cols[j].key%8==2 || D.cols[j].key%8==3 || D.cols[j].terms.all fun t => !B.sel t.1)=true at q
    simp only [beq_eq_false_iff_ne.mpr nf,beq_eq_false_iff_ne.mpr nl,Bool.false_or,List.all_eq_true,
      Bool.not_eq_true'] at q
    apply List.sum_eq_zero; intro t ht; obtain ⟨a,mem,rfl⟩ := List.mem_map.mp ht
    have ne : a.1≠i.val := fun e => by
      have z : B.sel a.1=false := q a mem
      exact Bool.noConfusion ((e ▸ z : B.sel i=false).symm.trans sel)
    simp [ne]
  have no (key : Nat) (nf : key%8≠2) (nl : key%8≠3) : lookupPrice D i (index D) key=0 := by
    unfold lookupPrice; cases e : locate D (index D) key with
    | none => rfl
    | some j => change coeff i D.cols[j].terms*_=0; rw [kill j ((locate_key e).symm ▸ nf) ((locate_key e).symm ▸ nl),zero_mul]
  have st (x : Site k) : lookupPrice D i (index D) (Keys.star F o x)=0 := by
    apply no <;> unfold Keys.star <;> cases decide (x∈F) <;> simp
  have pa (p : PatchPos k) : lookupPrice D i (index D) (patch F p)=0 := by
    apply no <;> unfold patch patchCode <;> omega
  have add (u v : Fin D.cols.size → Int) : lhs D (fun j => u j+v j) i=lhs D u i+lhs D v i := by
    simp [lhs,mul_add,sum_add_distrib]
  have aux : lhs D (fun j : Fin D.cols.size =>
      if D.cols[j].key%8=5 then complete F (D.cols[j].key/8) else 0) i=0 := by
    apply sum_eq_zero; intro j _; dsimp only; split <;> rename_i q
    · rw [kill j (by omega) (by omega),zero_mul]
    · simp
  have fa (p : FacePos k) : lookupPrice D i (index D) (face F p)=coeff i (tile B.table p (faceMask F p)) := by
    have q := zero_of_balanced _ (physical_tile (by omega : 3≤k) _ _ tiles F acy p) i
    rw [coeff_append,coeff_neg,sig_price D B.sel i sel] at q; omega
  have ln (t : Fin 8 × J k × J k) : lookupPrice D i (index D) (line F t.1 t.2.1 t.2.2)=
      -coeff i (arc B.table k t.2.1 t.2.2 (stateAt F t.1 t.2.1 t.2.2)
        (stateAt F t.1 t.2.1 (t.2.2.val+1))) := by
    have q := zero_of_balanced _ (physical_arc hb hk _ _ arcs F t.1 t.2.1 t.2.2 (all_views_np F rows cols t.1 t.2.1)) i
    rw [coeff_append,sig_price D B.sel i sel] at q
    exact eq_neg_of_add_eq_zero_left q
  unfold physicalVector GridGraphs.NoPitch.Dual.counts; rw [add,add,add,add,aux]
  simp only [scatter_price,st,pa,sum_const_zero,add_zero,zero_add]
  rw [sum_congr rfl (fun p _ => fa p),sum_congr rfl (fun t _ => ln t),
    sum_neg_distrib,sum_balance,add_neg_cancel]

/-- The 84 (odd base) or 69 (even base) face–line overlaps cancel at
every tail width, on the original physical forest. -/
theorem face_line_tail {k} (hk : 19≤k) (F : Finset (Site k)) (acy : (Budget.G F).IsAcyclic)
    (rows : ∀ r, ¬Pitch F (teeth k r)) (cols : ∀ r, ¬Pitch (trans F) (teeth k r))
    (o : Site k → Option (Fin 4)) (i : Fin (tailChart k).rows.size)
    (h : (supportMasks (tailChart k))[i]! = 12) :
    lhs (tailChart k) (physicalVector (tailChart k) F o) i=0 := by
  let b := if k%2=1 then 19 else 20
  let B := if k%2=1 then oddBook else evenBook
  have ok : cert (tailChart k) B b := by
    by_cases odd : k%2=1 <;> simp [B,b,tailChart,odd,cert58,cert61]
  exact lift ok (by dsimp [b]; split <;> decide) (by dsimp [b]; split <;> omega) F acy rows cols o i h
end GridGraphs.NoPitch.TailRows.FaceLine
