import GridGraphs.ResidueZero.ViewTerms
import GridGraphs.ResidueZero.DoubleCount

namespace GridGraphs.ResidueZero
open Finset

def onSite {s : Nat} (x : Pos) (h : inside s x) : GridVertex s s := by
  simp [inside] at h
  exact (⟨x.1.toNat,by omega⟩,⟨x.2.toNat,by omega⟩)

@[simp] theorem coord_onSite {s : Nat} (x : Pos) (h : inside s x) : coord (onSite x h)=x := by
  simp [inside] at h
  ext <;> simp [coord,onSite] <;> omega

def extend {s : Nat} (f : GridVertex s s → Nat → Int) (x : Pos) (d : Nat) :=
  if h : inside s x then f (onSite x h) d else 0

@[simp] theorem extend_coord {s} (f : GridVertex s s → Nat → Int) (v : GridVertex s s) (d : Nat) :
    extend f (coord v) d=f v d := by
  simp only [extend,dif_pos (coord_inside v)]
  rw [coord_injective (coord_onSite (coord v) (coord_inside v))]

private theorem grid_of_step {s} {v w : GridVertex s s} {d : Fin 2} (h : shift (coord v) d=coord w) :
    (gridGraph s s).Adj v w := by
  change adjacent _ _ _ _
  fin_cases d <;> simp [coord,shift,Prod.ext_iff,adjacent,Fin.ext_iff] at h ⊢ <;> omega

theorem physical_ports_zero {s : Nat} (f : GridVertex s s → Nat → Int)
    (missing : ∀ v (d : Fin 4), ¬inside s (shift (coord v) d) → f v d=0)
    (paired : ∀ v w (d : Fin 2), shift (coord v) d=coord w → f v d= -f w (d+2)) :
    (∑ v : GridVertex s s, ∑ d ∈ range 4, f v d)=0 := by
  have h := sum_ports_zero s (extend f) (by
    intro p hp d hd bad
    obtain ⟨v,_,rfl⟩ := mem_image.mp hp
    rw [extend_coord]; exact missing v ⟨_,hd⟩ bad) (by
    intro p hp d hv
    obtain ⟨v,_,rfl⟩ := mem_image.mp hp
    let w := onSite (shift (coord v) d) hv
    have e : shift (coord v) d=coord w := (coord_onSite ..).symm
    rw [e,extend_coord,extend_coord]; exact paired _ _ _ e)
  rw [physical_sum] at h
  simpa only [extend_coord] using h

def portF {n : Nat} (F : Finset (GridVertex n n)) (P : GridVertex n n → GridVertex n n)
    (g : Fin 8) (v : GridVertex n n) (d : Nat) :=
  port (starLocation n (image n g (coord v))) (decide (v∈F)).toNat (rotBits g (neighbours F (coord v)))
    (turnOut g (outDir v (P v))) (turn g d)

theorem portF_zero {n} (F : Finset (GridVertex n n)) (P : GridVertex n n → GridVertex n n)
    (step : ∀ v, P v≠v → (Bonds F).Adj v (P v))
    (covers : ∀ v w, (Bonds F).Adj v w → (P v=w ↔ P w≠v)) (g : Fin 8) :
    (∑ v, ∑ d ∈ range 4, portF F P g v d)=0 := by
  apply physical_ports_zero
  · intro v d bad
    simp only [portF,port,starLocation,located,←image_step,image_inside_iff,if_neg bad]
  · intro v w d h
    exact physical_port_opposite F P step covers v w d (grid_of_step h) h g

abbrev origins (n : Nat) := GridVertex (n-2) (n-2)
def maskAt {n : Nat} (F : Finset (GridVertex n n)) (a : origins n) :=
  physicalMask F a.1 a.2 (by have := a.1.isLt; omega) (by have := a.2.isLt; omega)

def stripF {n : Nat} (F : Finset (GridVertex n n)) (g : Fin 8) (a : origins n) (d : Nat) :=
  stripTerm (patchLocation (n-2) (image (n-2) g (coord a))) (rotMask g (maskAt F a)) (turn g d)

theorem stripF_zero {n} (hn : 2≤n) (F : Finset (GridVertex n n)) (g : Fin 8) :
    (∑ a, ∑ d ∈ range 4, stripF F g a d)=0 := by
  apply physical_ports_zero
  · intro a d bad
    rw [Nat.cast_sub hn] at bad
    norm_num1 at bad
    simp only [stripF,stripTerm,patchLocation,located,←image_step,image_inside_iff,Nat.cast_ofNat,if_neg bad]
  · intro a b d eq
    exact physical_strip_opposite F _ _ _ _ d eq.symm g

def coverF {n : Nat} (F : Finset (GridVertex n n)) (g : Fin 8) (p : GridVertex n n) (q : Fin 9) :=
  coverTerm (starLocation n (image n g (coord p))) (decide (p∈F)).toNat
    (rotBits g (neighbours F (coord p))) (patchQ g q)

def slotF {n : Nat} (F : Finset (GridVertex n n)) (g : Fin 8) (a : origins n) (q : Fin 9) :=
  slotTerm (patchLocation (n-2) (image (n-2) g (coord a))) (rotMask g (maskAt F a)) (patchQ g q)

theorem coverF_eq_slotF {n : Nat} (hn : 2≤n) (F : Finset (GridVertex n n)) (g : Fin 8) :
    (∑ p, ∑ q : Fin 9, coverF F g p q)=∑ a, ∑ q : Fin 9, slotF F g a q := by
  let f (p : GridVertex n n) (q : Nat) := coverF F g p (Fin.ofNat 9 q)
  let e (a : origins n) (q : Nat) := slotF F g a (Fin.ofNat 9 q)
  have H := sum_cover_slots n (extend f) (extend e) (by
    intro p hp q bad
    obtain ⟨v,_,rfl⟩ := mem_image.mp hp
    rw [extend_coord]
    have geom := image_offset n g (coord v-offset q) (offset q)
    rw [sub_add_cancel,←patchQ_coord] at geom
    have back := sub_eq_iff_eq_add.mpr geom
    simp only [Fin.ofNat_eq_cast,Fin.cast_val_eq_self,f,coverF,coverTerm,starLocation,Fin.isLt,
      if_true,located,back,image_inside_iff]
    rw [Nat.cast_sub hn] at bad; simp_all)
    (by
      intro a ha q
      obtain ⟨p,_,rfl⟩ := mem_image.mp ha
      have hr := p.1.isLt; have hc := p.2.isLt
      let v := place p.1 p.2 (by omega : p.1.val+3≤n) (by omega : p.2.val+3≤n)
        (⟨q.val/3,by have := q.isLt; omega⟩,⟨q.val%3,by omega⟩)
      have eq : coord v=coord p+offset q := by ext <;> simp [v,place,offset,coord]
      rw [←eq,extend_coord,extend_coord]
      simp only [f,e,Fin.ofNat_eq_cast,Fin.cast_val_eq_self,coverF,slotF,←marked_at F v,eq]
      exact physical_slot_opposite F _ _ _ _ q g)
  rw [physical_sum,physical_sum] at H
  simp only [extend_coord] at H
  simp_rw [←Fin.sum_univ_eq_sum_range] at H
  simpa [f,e] using H

end GridGraphs.ResidueZero
