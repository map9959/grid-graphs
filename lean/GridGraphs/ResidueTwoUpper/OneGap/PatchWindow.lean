import GridGraphs.ResidueTwoUpper.OneGap.PatchFilter

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap
open ResidueZero Stencil PatchFilter

private theorem overlap {n : Nat} (F : Finset (GridVertex n n)) (a b : origins n) (d : Fin 2)
    (eq : shift (coord a) d=coord b) :
    overlapBits (maskAt F a) d=overlapBits (maskAt F b) (d.val+2) := by
  have h := physical_overlap_key F (r:=a.1.val) (c:=a.2.val) (r':=b.1.val) (c':=b.2.val)
    (by have := a.1.isLt; omega) (by have := a.2.isLt; omega)
    (by have := b.1.isLt; omega) (by have := b.2.isLt; omega) d eq.symm 0
  have id : ∀ (m : Fin 512) (d : Fin 2),
      rotMask 0 m=m ∧ turn 0 d=d ∧ turn 0 (d+2)=d+2 := by native_decide
  change overlapBits (rotMask 0 (maskAt F a)) _ = overlapBits (rotMask 0 (maskAt F b)) _ at h
  obtain ⟨ma,t1,t2⟩ := id (maskAt F a) d
  simp only [Fin.val_zero] at h
  rw [ma,(id (maskAt F b) d).1,t1,t2] at h
  exact h

/-- A charged patch at least eight layers from all four edges of the
patch-origin grid is aligned and has precisely one mark, at a corner.
Both conclusions concern its actual nine bits. -/
theorem bulk_patch (u : Nat) (F : Finset (GridVertex (35+42*u) (35+42*u)))
    (acy : (Bonds F).IsAcyclic)
    (P : GridVertex (35+42*u) (35+42*u) → GridVertex (35+42*u) (35+42*u))
    (step : ∀ x, P x≠x → (Bonds F).Adj x (P x))
    (a : origins (35+42*u)) (charge : patchSlack F a=full)
    (zero : ∀ x, x≠Sum.inr a → weightAt F P x=0)
    (hr : 8≤a.1.val ∧ a.1.val+9≤33+42*u)
    (hc : 8≤a.2.val ∧ a.2.val+9≤33+42*u) :
    a.1.val%3=1 ∧ a.2.val%3=1 ∧ singletonCorner (maskAt F a) := by
  let R := a.1.val-2
  let C := a.2.val-2
  have ra : R+2=a.1.val := by dsimp [R]; omega
  have ca : C+2=a.2.val := by dsimp [C]; omega
  let chart (p : Site) : origins (35+42*u) :=
    (⟨R+p.1.val,by have := p.1.isLt; omega⟩,⟨C+p.2.val,by have := p.2.isLt; omega⟩)
  have center : chart mid=a := Prod.ext (Fin.ext ra) (Fin.ext ca)
  let M (p : Site) := maskAt F (chart p)
  have hdom (p : Site) : valid (p==mid) ((R%3)+p.1.val) ((C%3)+p.2.val) (M p) := by
    have hp := p.1.isLt; have hq := p.2.isLt
    have ch : patchSlack F (chart p)=if (p==mid) then full else 0 := by
      by_cases he : p=mid
      · simpa [he,center] using charge
      · have ne : chart p≠a := by
          intro eq; apply he; apply Prod.ext <;> apply Fin.ext
          · have e := congrArg (fun a : origins (35+42*u) => a.1.val) eq
            change R+p.1.val=a.1.val at e; change p.1.val=2; omega
          · have e := congrArg (fun a : origins (35+42*u) => a.2.val) eq
            change C+p.2.val=a.2.val at e; change p.2.val=2; omega
        simpa [he] using (show patchSlack F (chart p)=0 from zero (.inr _) (fun e => ne (Sum.inr.inj e)))
    have chk := physical_atom (u:=u) (r:=R+p.1.val) (c:=C+p.2.val) F acy P step
      ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (p==mid)
      (fun v => zero (.inl v) (by simp)) (chart p) rfl rfl ch
    unfold valid at chk ⊢
    rwa [show (R%3+p.1.val)%3=(R+p.1.val)%3 by omega,
      show (C%3+p.2.val)%3=(C+p.2.val)%3 by omega]
  have go (p : Site) (d : Fin 4) (q : Site) (eq : shiftSite p d=some q) :
      overlapBits (M q) (opp d)=overlapBits (M p) d := by
    have geo : ∀ (p : Site) (d : Fin 4) (q : Site), shiftSite p d=some q →
        shift (coord p) d=coord q := by native_decide
    have disp := geo p d q eq
    fin_cases d
    · exact (overlap F _ _ 0 (by simp [coord,shift,Prod.ext_iff] at disp; ext <;> simp [chart,coord,shift] <;> omega)).symm
    · exact (overlap F _ _ 1 (by simp [coord,shift,Prod.ext_iff] at disp; ext <;> simp [chart,coord,shift] <;> omega)).symm
    · exact overlap F _ _ 0 (by simp [coord,shift,Prod.ext_iff] at disp; ext <;> simp [chart,coord,shift] <;> omega)
    · exact overlap F _ _ 1 (by simp [coord,shift,Prod.ext_iff] at disp; ext <;> simp [chart,coord,shift] <;> omega)
  have h := prune_sound ⟨R%3,by omega⟩ ⟨C%3,by omega⟩ M hdom go
  change (R%3+2)%3=1 ∧ (C%3+2)%3=1 ∧ singletonCorner (maskAt F (chart mid)) at h
  rw [center] at h
  exact ⟨by omega,by omega,h.2.2⟩

/-- Use the *same* parity-priced patch, not a separate choice of a
mask or an origin, to rule out equal checkerboard parities. -/
theorem odd_bulk_origin (u : Nat) (a : origins (35+42*u)) (m : Fin 512)
    (hr : 8≤a.1.val ∧ a.1.val+9≤33+42*u)
    (hc : 8≤a.2.val ∧ a.2.val+9≤33+42*u)
    (phase : a.1.val%3=1 ∧ a.2.val%3=1) (corner : singletonCorner m)
    (site : patchSite u a m) : (a.1.val+a.2.val)%2=1 := by
  have cert : ∀ i j : Fin 6, ∀ m : Fin 512, singletonCorner m →
      let r := 7+i.val; let c := 7+j.val
      r%3=1 → c%3=1 → Parity.patchBill 35 (r,c) m%2=1 → (r+c)%2=1 := by
    native_decide
  let i : Fin 6 := ⟨(a.1.val-7)%6,by omega⟩
  let j : Fin 6 := ⟨(a.2.val-7)%6,by omega⟩
  have e : Parity.project 33 u (coord a)=((7:Int)+i.val,(7:Int)+j.val) := by
    ext <;> simp [Parity.project,Parity.reduce,coord,i,j] <;> split_ifs <;> omega
  have odd := site.2.1
  change Parity.patchBill 35 (Parity.project 33 u (coord a)) m%2=1 at odd
  rw [e] at odd
  have s := cert i j m corner (by dsimp [i]; omega) (by dsimp [j]; omega) odd
  dsimp [i,j] at s
  omega

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap
