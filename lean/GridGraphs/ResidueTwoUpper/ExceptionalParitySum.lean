import GridGraphs.ResidueTwoUpper.ExceptionalParity

namespace GridGraphs.ResidueTwoUpper.Exceptional.Parity
open ResidueZero Stencil Finset

private theorem grid_of_step {s} {v w : GridVertex s s} {d : Fin 2} (h : shift (coord v) d=coord w) :
    (gridGraph s s).Adj v w := by
  change adjacent _ _ _ _
  fin_cases d <;> simp [coord,shift,Prod.ext_iff,adjacent,Fin.ext_iff] at h ⊢ <;> omega

private theorem port_sum {n} (F : Finset (GridVertex n n)) (P : GridVertex n n → GridVertex n n)
    (step : ∀ v, P v≠v → (Bonds F).Adj v (P v))
    (covers : ∀ v w, (Bonds F).Adj v w → (P v=w ↔ P w≠v)) :
    (∑ v, ∑ d : Fin 4, port n (coord v) (decide (v∈F)).toNat
      (neighbours F (coord v)) (outDir v (P v)) d)=0 := by
  simp_rw [Fin.sum_univ_eq_sum_range]
  apply physical_ports_zero
  · intro v d bad; simp [port,bond,bad]
  · intro v w d next
    have rev : shift (coord w) (d.val+2)=coord v := by rw [←next]; exact (reverse_step _ d).1
    have key := physical_edge_key F P step covers v w d (grid_of_step next) next 0
    have turn0 (o : Nat) (ho : o<5) : turnOut 0 o=o := by interval_cases o <;> decide
    have t1 : turn 0 d=d := by have := d.isLt; simp [turn,Nat.mod_eq_of_lt (by omega : d.val<4)]
    have t2 : turn 0 (d+2)=d+2 := by have := d.isLt; simp [turn,Nat.mod_eq_of_lt (by omega : d.val+2<4)]
    simp only [Fin.val_zero] at key
    rw [turn0 _ (outDir_lt ..),turn0 _ (outDir_lt ..),t1,t2] at key
    have e1 := neighbours_bit F (coord v) ⟨d,by have := d.isLt; omega⟩
    have e2 := neighbours_bit F (coord w) ⟨d+2,by have := d.isLt; omega⟩
    change bit _ d=(marked F (shift (coord v) d)).toNat at e1
    change bit _ (d+2)=(marked F (shift (coord w) (d+2))).toNat at e2
    rw [next,marked_at] at e1; rw [rev,marked_at] at e2
    simp only [port,bond,e1,e2,next,rev,coord_inside,if_true,if_pos d.isLt,
      if_neg (show ¬d.val+2<2 by omega),Nat.add_sub_cancel,neg_neg,key]

private theorem strip_sum {n} (hn : 2≤n) (F : Finset (GridVertex n n)) :
    (∑ a : origins n, ∑ d : Fin 4, strip (n-2:Nat) (coord a) (maskAt F a) d)=0 := by
  simp_rw [Fin.sum_univ_eq_sum_range]
  apply physical_ports_zero
  · intro v d bad; simp [strip,bond,bad]
  · intro a b d next
    have rev : shift (coord b) (d.val+2)=coord a := by rw [←next]; exact (reverse_step _ d).1
    have eq := physical_overlap_key F (r:=a.1.val) (c:=a.2.val) (r':=b.1.val) (c':=b.2.val)
      (by have := a.1.isLt; omega) (by have := a.2.isLt; omega)
      (by have := b.1.isLt; omega) (by have := b.2.isLt; omega) d next.symm 0
    have ident : ∀ (m : Fin 512) (d : Fin 2),
        rotMask 0 m=m ∧ turn 0 d=d ∧ turn 0 (d+2)=d+2 := by native_decide
    obtain ⟨ma,t1,t2⟩ := ident (maskAt F a) d
    change overlapBits (rotMask 0 (maskAt F a)) _ = overlapBits (rotMask 0 (maskAt F b)) _ at eq
    simp only [Fin.val_zero] at eq
    rw [ma,(ident (maskAt F b) d).1,t1,t2] at eq
    simp only [strip,bond,next,rev,coord_inside,if_true,if_pos d.isLt,
      if_neg (show ¬d.val+2<2 by omega),Nat.add_sub_cancel,neg_neg,eq]

private theorem cover_sum {n} (hn : 2≤n) (F : Finset (GridVertex n n)) :
    (∑ v, ∑ q : Fin 9, cover n (coord v) (decide (v∈F)).toNat (neighbours F (coord v)) q) =
    ∑ a : origins n, ∑ q : Fin 9, slot n (coord a) (maskAt F a) q := by
  let f (v : GridVertex n n) (q : Nat) := cover n (coord v) (decide (v∈F)).toNat (neighbours F (coord v)) q
  let e (a : origins n) (q : Nat) := slot n (coord a) (maskAt F a) q
  have H := sum_cover_slots n (extend f) (extend e) (by
    intro p hp q bad
    obtain ⟨v,_,rfl⟩ := mem_image.mp hp
    rw [extend_coord]; unfold f cover
    rw [Nat.cast_sub hn] at bad; simp_all)
    (by
      intro a ha q
      obtain ⟨p,_,rfl⟩ := mem_image.mp ha
      have hr := p.1.isLt; have hc := p.2.isLt
      let v := place p.1 p.2 (by omega : p.1.val+3≤n) (by omega : p.2.val+3≤n)
        (⟨q.val/3,by have := q.isLt; omega⟩,⟨q.val%3,by omega⟩)
      have eq : coord v=coord p+offset q := by ext <;> simp [v,place,offset,coord]
      rw [←eq,extend_coord,extend_coord]
      have ev := physical_incidence_key F p.1 p.2 (by omega) (by omega) q 0
      have ident : ∀ (q : Fin 9) (nb : Fin 16) (m : Fin 512),
        patchQ 0 q=q ∧ rotBits 0 nb=nb ∧ rotMask 0 m=m := by native_decide
      obtain ⟨q0,nb0,m0⟩ := ident q ⟨neighbours F (coord v),code_lt _⟩ (maskAt F p)
      change localEvent _ (marked F (coord p+offset q)).toNat (rotBits 0 (neighbours F (coord p+offset q))) =
        localEvent _ (bit (rotMask 0 (maskAt F p)) _) (patchNbr (rotMask 0 (maskAt F p)) _) at ev
      simp only [Fin.val_zero] at ev
      rw [←eq,q0,marked_at,nb0,m0] at ev
      have back := sub_eq_iff_eq_add.mpr eq
      have hp := coord_inside p; rw [Nat.cast_sub hn] at hp; norm_num1 at hp
      unfold f e cover slot; rw [back,if_pos hp,ev])
  rw [physical_sum,physical_sum] at H
  simp only [extend_coord] at H
  simpa only [Fin.sum_univ_eq_sum_range,f,e] using H

private theorem special_sum (s : Nat) (hs : 12 ≤ s) : (∑ a : GridVertex s s, special s (coord a))=1 := by
  let endPos : GridVertex s s := (⟨s-1,by omega⟩,⟨s-1,by omega⟩)
  have bound (v : Fin s) : 0≤ax s v.val ∧ ax s v.val≤13 := by
    have := v.isLt; unfold ax; split_ifs <;> omega
  have last (v : Fin s) : ax s v.val=13 ↔ v.val=s-1 := by
    have := v.isLt; unfold ax; split_ifs <;> omega
  have test (a : GridVertex s s) : bucket s (coord a)=429 ↔ a=endPos := by
    simp only [bucket,coord,Prod.ext_iff,Fin.ext_iff,endPos]
    have A := bound a.1; have B := bound a.2
    have E := last a.1; have G := last a.2
    omega
  simp only [special,test]; simp

theorem physical_sum_one {n} (hn : 14≤n) (F : Finset (GridVertex n n)) (P : GridVertex n n → GridVertex n n)
    (step : ∀ v, P v≠v → (Bonds F).Adj v (P v))
    (covers : ∀ v w, (Bonds F).Adj v w → (P v=w ↔ P w≠v)) :
    (∑ v, starBill n (coord v) (decide (v∈F)).toNat (neighbours F (coord v)) (outDir v (P v)))+
      (∑ a : origins n, patchBill n (coord a) (maskAt F a))=1 := by
  unfold starBill patchBill
  have cast : (n:Int)-2=((n-2:Nat):Int) := by omega
  simp only [sum_add_distrib,sum_sub_distrib,port_sum F P step covers,cast,strip_sum (by omega) F,
    special_sum _ (by omega : 12≤n-2),cover_sum (by omega) F]
  ring

end GridGraphs.ResidueTwoUpper.Exceptional.Parity
