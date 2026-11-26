import GridGraphs.Geometry.CapWindowScan

namespace GridGraphs.CapSite
open GridGraphs.CapBill Finset

def camera {r} (t : Fin r) (rev : Bool) : Camera :=
  ⟨if rev then 3*(t.val:ℤ)+3 else 3*(t.val:ℤ)-1,rev⟩

private theorem camera_center {r h} (t : Fin r) (rev : Bool) :
    (camera t rev).atP 0 2 = coord (tooth (h:=h) t) := by
  cases rev <;> simp [camera,Camera.atP,coord,tooth] <;> omega

theorem at_tooth {r h} {F : Finset (Cell r h)} (pad : Padded F) (t : Fin r) (rev : Bool)
    (i : Nat) (hi : i<5) : markBit F (camera t rev) 0 i = decide (i=2) := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp only [markBit,decide_eq_true_eq]
  constructor
  · rintro ⟨w,wm,e⟩
    have y := (Prod.mk.inj e).1; have x := (Prod.mk.inj e).2
    have p := pad.top w wm (by exact_mod_cast y)
    cases rev <;> simp [camera] at x <;> omega
  · rintro rfl
    exact ⟨_,tooth_mark pad t,(camera_center t rev).symm⟩

private theorem send_at {r h} {F : Finset (Cell r h)} (v : Cell r h) (q : Pt) :
    sends F (coord v) q ↔ v≠arrow F v ∧ coord (arrow F v)=q := by
  constructor
  · rintro ⟨a,b,ha,rfl,e,out⟩
    cases coord_injective ha
    exact ⟨out ▸ e.ne,congrArg coord out⟩
  · rintro ⟨ne,rfl⟩
    have nf := mt (parent_fix (capDest F) (root_class _ _ _) v).mpr ne.symm
    exact ⟨_,_,rfl,rfl,(parent_step (capDest F) (root_class _ _ _) nf).1,rfl⟩

noncomputable def dropBit {r h} (F : Finset (Cell r h)) (t : Fin r) : Bool := by
  classical exact decide (tooth t ∈ waived (board r h) (terminalSet F) F)

private theorem tooth_toward {r h} {F : Finset (Cell r h)} (pad : Padded F)
    (t : Fin r) (rev : Bool) (dy dx : Int) : toward F (camera t rev) 0 2 dy dx =
      (dropBit F t && decide (dy=1 ∧ dx=0)) := by
  classical
  apply Bool.eq_iff_iff.mpr
  rw [toward_iff,camera_center,send_at]
  simp only [dropBit,Bool.and_eq_true,decide_eq_true_eq]
  by_cases d : tooth t ∈ waived (board r h) (terminalSet F) F
  · rw [tooth_sends_down pad t d]
    rw [and_iff_right d]
    cases rev <;> simp [camera,Camera.atP,coord,tooth] <;> omega
  · have kt : keeps (board r h) (terminalSet F) F (tooth t) := by
      by_contra fail
      exact d (mem_filter.mpr ⟨mem_filter.mpr ⟨tooth_mark pad t,rfl⟩,fail⟩)
    have eq := (parent_fix (capDest F) (root_class _ _ _) (tooth t)).mpr kt
    change arrow F (tooth t)=tooth t at eq; simp [eq,d]

private theorem leaf_toward {r h} {F : Finset (Cell r h)} (pad : Padded F)
    (t : Fin r) (rev : Bool) (x dy dx : Int) (leaf : x=1 ∨ x=3) :
    toward F (camera t rev) 0 x dy dx = decide (dy=0 ∧ x+dx=2) := by
  let col : Fin (3*r) := ⟨((camera t rev).atP 0 x).2.toNat, by
    have ht := t.isLt; cases rev <;> simp [camera,Camera.atP] <;> omega⟩
  have inside : ((camera t rev).atP 0 x).2 ≥ 0 := by
    cases rev <;> simp [camera,Camera.atP] <;> omega
  have pos : (camera t rev).atP 0 x = coord (rim (h:=h) col) := by
    refine Prod.ext ?_ ?_
    · rfl
    · exact (Int.toNat_of_nonneg inside).symm
  have phase : col.val%3≠1 := by dsimp [col,camera,Camera.atP]; split_ifs <;> omega
  have own : owner col=t := by apply Fin.ext; dsimp [owner,col,camera,Camera.atP]; split_ifs <;> omega
  have ne : rim (h:=h) col ≠ tooth t := by
    intro eq; have e := congrArg (fun v : Cell r h => v.2.val) eq
    change col.val=3*t.val+1 at e; omega
  apply Bool.eq_iff_iff.mpr
  rw [toward_iff,pos,send_at,pitch_leaf pad col phase,own,←camera_center t rev]
  simp [ne,Camera.atP,Prod.mk.injEq]; cases rev <;> simp [camera] <;> omega

theorem initial_state {r h} {F : Finset (Cell r h)} (pad : Padded F) (t : Fin r) (rev : Bool) :
    stateAt F (camera t rev) 0=initial := by
  have mask : maskAt F (camera t rev) 0 = 4 := by
    unfold maskAt; simp only [pack]
    rw [at_tooth pad t rev _ (by decide),at_tooth pad t rev _ (by decide),
      at_tooth pad t rev _ (by decide),at_tooth pad t rev _ (by decide),at_tooth pad t rev _ (by decide)]
    decide
  have above : maskAt F (camera t rev) (0-1) = 0 := by
    unfold maskAt; apply Nat.eq_of_testBit_eq
    intro i; change bit (pack 5 _) i = _
    rw [packed]; split_ifs
    · classical
      simp only [markBit,Nat.zero_testBit,decide_eq_false_iff_not]
      rintro ⟨w,_,e⟩; have := (Prod.mk.inj e).1
      change (w.1.val:ℤ)=0-1 at this; omega
    · simp
  have used : pack 3 (usedAt F (camera t rev) 0)=5 := by
    simp only [pack,usedAt]
    simp only [show ((0:Nat):ℤ)=0 by rfl,show ((1:Nat):ℤ)=1 by rfl,
      show ((2:Nat):ℤ)=2 by rfl]
    norm_num [leaf_toward pad t rev 1 _ _ (Or.inl rfl),leaf_toward pad t rev 3 _ _ (Or.inr rfl),
      tooth_toward pad t rev,Nat.bit_val]
  simp only [stateAt,Nat.cast_zero,mask,above,used]; rfl

theorem first_down {r h} {F : Finset (Cell r h)} (pad : Padded F) (t : Fin r) (rev : Bool) :
    (rowAt F (camera t rev) 0).down=2*one (dropBit F t) := by
  simp only [rowAt,pack]
  norm_num [leaf_toward pad t rev 1 _ _ (Or.inl rfl),leaf_toward pad t rev 3 _ _ (Or.inr rfl),
    tooth_toward pad t rev,Nat.bit_val,one]
  cases dropBit F t <;> decide

def outerEnd {r} (t : Fin r) (rev : Bool) : Prop := if rev then t.val+1=r else t.val=0
instance {r} (t : Fin r) (rev : Bool) : Decidable (outerEnd t rev) := by unfold outerEnd; infer_instance
noncomputable def windowKind {r h} (F : Finset (Cell r h)) (t : Fin r) (rev : Bool) :=
  (if outerEnd t rev then 0 else 2)+one (dropBit F t)

theorem guard_clear {r h} {F : Finset (Cell r h)} (pad : Padded F) (t : Fin r) (rev : Bool)
    (outer : outerEnd t rev) (y : Nat) : (rowAt F (camera t rev) y).mask%4=0 := by
  have clear (i : Nat) (hi : i<2) : markBit F (camera t rev) ((y:ℤ)+1) i=false := by
    classical
    simp only [markBit,decide_eq_false_iff_not]
    rintro ⟨w,wm,eq⟩; have x := (Prod.mk.inj eq).2; have := pad.sides w wm
    cases rev <;> simp [outerEnd,camera] at x outer <;> omega
  simp only [rowAt,maskAt,pack,Nat.bit_val,clear 0 (by decide),clear 1 (by decide)]
  simp; omega

/-- Unconditional local-language inclusion for every triple of an oriented
padded physical forest, in both reading directions at all heights. -/
theorem actual_strip {r h} {F : Finset (Cell r h)} (pad : Padded F) (t : Fin r) (rev : Bool) :
    PhysicalStrip (windowKind F t rev) initial (scanRows F (camera t rev) 0 h) := by
  rw [←initial_state pad t rev]
  apply scan_physical F _ pad _ _ _ 0 h (by omega)
  · intro y _ hk
    apply guard_clear pad
    unfold windowKind at hk; split_ifs at hk <;> omega
  · rw [first_down pad]
    unfold windowKind one; split_ifs <;> decide

end GridGraphs.CapSite
