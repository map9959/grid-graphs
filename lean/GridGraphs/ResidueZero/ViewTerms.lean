import GridGraphs.ResidueZero.IncidenceGeometry
import GridGraphs.ResidueZero.MarginalKeys
import GridGraphs.ResidueZero.EdgeKeys

namespace GridGraphs.ResidueZero
open Finset

theorem image_inside_iff (n : Int) (g : Fin 8) (p : Pos) :
    inside n (image n g p) = inside n p := by
  apply Bool.eq_iff_iff.mpr
  fin_cases g <;> simp [image,inside] <;> omega

theorem opposite_turn (g : Fin 8) (d : Fin 2) :
    (turn g d < 2 ∧ turn g (d+2)=turn g d+2) ∨
    (turn g (d+2)<2 ∧ turn g d=turn g (d+2)+2) := by
  have all : ∀ (g : Fin 8) (d : Fin 2), (turn g d < 2 ∧ turn g (d+2)=turn g d+2) ∨
    (turn g (d+2)<2 ∧ turn g d=turn g (d+2)+2) := by native_decide
  exact all g d

private theorem rot_bit : ∀ (g : Fin 8) (d : Fin 4) (m : Fin 16),
    bit (rotBits g m) (turn g d) = bit m d := by native_decide

private def price (t u d e : Nat) := if d<2 then edgePrices.getD (key t u d e) 0
  else -(edgePrices.getD (key u t (d-2) e) 0)

private theorem port_eq {l : StarLocation} {u : Nat} (f nb o d : Nat) (h : l.neighbour d=some u) :
    port l f nb o d=price l.t u d (edgeEvent f (bit nb d) o d) := by simp [port,h,price]

private theorem neighbour_eq {n : Nat} (v w : GridVertex n n) (d : Fin 4) (g : Fin 8)
    (h : shift (coord v) d=coord w) :
    (starLocation n (image n g (coord v))).neighbour (turn g d) =
      some (atPos n 2 (image n g (coord w))) := by
  simp only [starLocation,located,←image_step,h,image_inside_iff,coord_inside,if_true]

private theorem nb_eq {n : Nat} (F : Finset (GridVertex n n)) (v w : GridVertex n n)
    (d : Fin 4) (g : Fin 8) (h : shift (coord v) d=coord w) :
    bit (rotBits g (neighbours F (coord v))) (turn g d) = (decide (w∈F)).toNat := by
  rw [rot_bit g d ⟨neighbours F (coord v),code_lt _⟩,neighbours_bit F _ d,h,marked_at]

private theorem price_opp (t u e : Nat) (d : Fin 2) (g : Fin 8) :
    price t u (turn g d) e = -price u t (turn g (d+2)) e := by
  unfold price
  rcases opposite_turn g d with ⟨h,h'⟩|⟨h,h'⟩ <;>
    simp only [h',show ∀ t : Nat, ¬t+2<2 by omega,if_false,Nat.add_sub_cancel,if_pos h,neg_neg]

theorem physical_port_opposite {n : Nat} (F : Finset (GridVertex n n))
    (P : GridVertex n n → GridVertex n n) (step : ∀ v, P v≠v → (Bonds F).Adj v (P v))
    (covers : ∀ v w, (Bonds F).Adj v w → (P v=w ↔ P w≠v)) (v w : GridVertex n n)
    (d : Fin 2) (grid : (gridGraph n n).Adj v w) (next : shift (coord v) d=coord w) (g : Fin 8) :
    let bill (v : GridVertex n n) (e : Nat) :=
      port (starLocation n (image n g (coord v))) (decide (v∈F)).toNat
        (rotBits g (neighbours F (coord v))) (turnOut g (outDir v (P v))) (turn g e)
    bill v d = -bill w (d+2) := by
  let a : Fin 4 := ⟨d,by have := d.isLt; omega⟩
  let b : Fin 4 := ⟨d+2,by have := d.isLt; omega⟩
  have rev : shift (coord w) b=coord v := by rw [←next]; exact (reverse_step _ d).1
  dsimp only
  rw [port_eq _ _ _ _ (neighbour_eq v w a g next), port_eq _ _ _ _ (neighbour_eq w v b g rev),
    nb_eq F v w a g next,nb_eq F w v b g rev,physical_edge_key F P step covers v w d grid next g]
  exact price_opp _ _ _ d g

theorem patchQ_coord (g : Fin 8) (q : Fin 9) :
    offset (patchQ g q) = image 3 g (offset q) := by
  have H : ∀ (g : Fin 8) (q : Fin 9), offset (patchQ g q)=image 3 g (offset q) := by native_decide
  exact H g q

theorem physical_slot_opposite {n : Nat} (F : Finset (GridVertex n n)) (r c : Nat)
    (hr : r+3≤n) (hc : c+3≤n) (q : Fin 9) (g : Fin 8) :
    let a : Pos := (r,c)
    let p := a+offset q
    coverTerm (starLocation n (image n g p)) (marked F p).toNat (rotBits g (neighbours F p)) (patchQ g q) =
      slotTerm (patchLocation (n-2) (image (n-2) g a)) (rotMask g (physicalMask F r c hr hc)) (patchQ g q) := by
  let a : Pos := (r,c)
  have geom := image_offset n g a (offset q)
  rw [←patchQ_coord] at geom
  have back : image n g (a+offset q)-offset (patchQ g q)=image (n-2) g a := by rw [geom]; simp
  have ia : inside ((n:Int)-2) a := by simp [inside,a]; omega
  dsimp only
  change coverTerm (starLocation n (image n g (a+offset q))) _ _ _ = slotTerm _ _ _
  simp only [coverTerm,starLocation,located,Fin.isLt,if_true,back,image_inside_iff,ia,
    slotTerm,patchLocation,sub_add_cancel]
  rw [physical_incidence_key F r c hr hc q g]
  rw [geom]

theorem physical_strip_opposite {n : Nat} (F : Finset (GridVertex n n))
    {r c r' c' : Nat} (hr : r+3≤n) (hc : c+3≤n) (hr' : r'+3≤n) (hc' : c'+3≤n)
    (d : Fin 2) (next : ((r':Int),(c':Int))=shift ((r:Int),(c:Int)) d) (g : Fin 8) :
    stripTerm (patchLocation (n-2) (image (n-2) g (r,c))) (rotMask g (physicalMask F r c hr hc)) (turn g d) =
    -stripTerm (patchLocation (n-2) (image (n-2) g (r',c'))) (rotMask g (physicalMask F r' c' hr' hc'))
      (turn g (d+2)) := by
  let a : Pos := (r,c)
  let b : Pos := (r',c')
  have next' : shift a d=b := next.symm
  have rev : shift b (d.val+2)=a := by rw [←next']; exact (reverse_step _ d).1
  let d₁ : Fin 4 := ⟨d,by have := d.isLt; omega⟩
  let d₂ : Fin 4 := ⟨d+2,by have := d.isLt; omega⟩
  have A := image_step ((n:Int)-2) g d₁ a
  have B := image_step ((n:Int)-2) g d₂ b
  dsimp [d₁,d₂] at A B
  rw [next'] at A; rw [rev] at B
  have ia : inside ((n:Int)-2) a := by simp [inside,a]; omega
  have ib : inside ((n:Int)-2) b := by simp [inside,b]; omega
  change stripTerm (patchLocation _ (image _ _ a)) _ _ = -stripTerm (patchLocation _ (image _ _ b)) _ _
  simp only [stripTerm,patchLocation,located,←A,←B,image_inside_iff,ia,ib,if_true,
    physical_overlap_key F hr hc hr' hc' d next g]
  rcases opposite_turn g d with ⟨h,h'⟩|⟨h,h'⟩ <;>
    simp only [h',show ∀ t : Nat, ¬t+2<2 by omega,if_false,Nat.add_sub_cancel,if_pos h,neg_neg]

end GridGraphs.ResidueZero
