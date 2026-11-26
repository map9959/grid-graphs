import GridGraphs.Results.SmallDiagonalExact.Eleven.Events

namespace GridGraphs.Eleven
open GridGraphs.ResidueZero hiding scale starNormPrices patchNormPrices edgePrices incidencePrices overlapPrices cornerPrices
open Finset

private theorem grid_of_step {s} {v w : GridVertex s s} {d : Fin 2} (h : shift (coord v) d=coord w) :
    (gridGraph s s).Adj v w := by
  change adjacent _ _ _ _
  fin_cases d <;> simp [coord,shift,Prod.ext_iff,adjacent,Fin.ext_iff] at h ⊢ <;> omega

def twoPortF {n : Nat} (F : Finset (GridVertex n n)) (P : GridVertex n n → GridVertex n n)
    (g : Fin 8) (v : GridVertex n n) (d : Nat) :=
  twoPort (starLoc n (image n g (coord v))) (decide (v∈F)).toNat (rotBits g (neighbours F (coord v)))
    (turnOut g (outDir v (P v))) (turn g d)

theorem twoPortF_zero {n} (F : Finset (GridVertex n n)) (P : GridVertex n n → GridVertex n n)
    (step : ∀ v, P v≠v → (Bonds F).Adj v (P v))
    (covers : ∀ v w, (Bonds F).Adj v w → (P v=w ↔ P w≠v)) (g : Fin 8) :
    (∑ v, ∑ d ∈ range 4, twoPortF F P g v d)=0 := by
  apply physical_ports_zero
  · intro v d bad
    simp only [twoPortF,twoPort,starLoc,here,←image_step,image_inside_iff,if_neg bad]
  · intro v w d h
    exact two_port_opposite F P step covers v w d (grid_of_step h) h g

def twoStripF {n : Nat} (F : Finset (GridVertex n n)) (g : Fin 8) (a : origins n) (d : Nat) :=
  twoStripTerm (patchLoc (n-2) (image (n-2) g (coord a))) (rotMask g (maskAt F a)) (turn g d)

theorem twoStripF_zero {n} (hn : 2≤n) (F : Finset (GridVertex n n)) (g : Fin 8) :
    (∑ a, ∑ d ∈ range 4, twoStripF F g a d)=0 := by
  apply physical_ports_zero
  · intro a d bad
    rw [Nat.cast_sub hn] at bad
    norm_num1 at bad
    simp only [twoStripF,twoStripTerm,patchLoc,here,←image_step,image_inside_iff,if_neg bad]
  · intro a b d eq
    exact two_strip_opposite F _ _ _ _ d eq.symm g

def twoCoverF {n : Nat} (F : Finset (GridVertex n n)) (g : Fin 8) (p : GridVertex n n) (q : Fin 9) :=
  twoCoverTerm (starLoc n (image n g (coord p))) (decide (p∈F)).toNat
    (rotBits g (neighbours F (coord p))) (patchQ g q)

def twoSlotF {n : Nat} (F : Finset (GridVertex n n)) (g : Fin 8) (a : origins n) (q : Fin 9) :=
  twoSlotTerm (patchLoc (n-2) (image (n-2) g (coord a))) (rotMask g (maskAt F a)) (patchQ g q)

theorem twoCoverF_eq_slotF {n : Nat} (hn : 2≤n) (F : Finset (GridVertex n n)) (g : Fin 8) :
    (∑ p, ∑ q : Fin 9, twoCoverF F g p q)=∑ a, ∑ q : Fin 9, twoSlotF F g a q := by
  let f (p : GridVertex n n) (q : Nat) := twoCoverF F g p (Fin.ofNat 9 q)
  let e (a : origins n) (q : Nat) := twoSlotF F g a (Fin.ofNat 9 q)
  have H := sum_cover_slots n (extend f) (extend e) (by
    intro p hp q bad
    obtain ⟨v,_,rfl⟩ := mem_image.mp hp
    rw [extend_coord]
    have geom := image_offset n g (coord v-offset q) (offset q)
    rw [sub_add_cancel,←patchQ_coord] at geom
    have back := sub_eq_iff_eq_add.mpr geom
    simp only [Fin.ofNat_eq_cast,Fin.cast_val_eq_self,f,twoCoverF,twoCoverTerm,starLoc,Fin.isLt,
      if_true,here,back,image_inside_iff]
    rw [Nat.cast_sub hn] at bad; simp_all)
    (by
      intro a ha q
      obtain ⟨p,_,rfl⟩ := mem_image.mp ha
      have hr := p.1.isLt; have hc := p.2.isLt
      let v := place p.1 p.2 (by omega : p.1.val+3≤n) (by omega : p.2.val+3≤n)
        (⟨q.val/3,by have := q.isLt; omega⟩,⟨q.val%3,by omega⟩)
      have eq : coord v=coord p+offset q := by ext <;> simp [v,place,offset,coord]
      rw [←eq,extend_coord,extend_coord]
      simp only [f,e,Fin.ofNat_eq_cast,Fin.cast_val_eq_self,twoCoverF,twoSlotF,←marked_at F v,eq]
      exact two_slot_opposite F _ _ _ _ q g)
  rw [physical_sum,physical_sum] at H
  simp only [extend_coord] at H
  simp_rw [←Fin.sum_univ_eq_sum_range] at H
  simpa [f,e] using H

end GridGraphs.Eleven
