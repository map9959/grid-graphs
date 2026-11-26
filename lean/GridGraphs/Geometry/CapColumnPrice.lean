import GridGraphs.Geometry.CapCellCharge

namespace GridGraphs.CapSite
open GridGraphs.CapBill Finset

def body {r h} (t : Fin r) (rev : Bool) (y : Fin (h+2)) (i : Fin 3) : Cell r h :=
  (y,⟨3*t.val+(if rev then 2-i.val else i.val),by have := t.isLt; split_ifs <;> omega⟩)

theorem body_coord {r h} (t : Fin r) (rev : Bool) (y : Fin (h+2)) (i : Fin 3) :
    coord (body t rev y i)=(camera t rev).atP y ((i:ℤ)+1) := by
  have := i.isLt
  cases rev <;> simp [coord,body,camera,Camera.atP]; omega

variable {r h : Nat} (F : Finset (Cell r h))
noncomputable def charge (v : Cell r h) : Int :=
  siteBill (board r h) F (outer r h) v +
    2*one (decide (v∈extraRoots (board r h) (terminalSet F) F))
noncomputable def triplePrice (t : Fin r) (rev : Bool) (y : Fin (h+2)) :=
  ∑ i : Fin 3, charge F (body t rev y i)

private theorem body_geom (t : Fin r) (rev : Bool) (y : Nat) (hy : y<h+2) (i : Fin 3) :
    geometry (decide (i.val=1)) (stencil (stateAt F (camera t rev) y)
      (rowAt F (camera t rev) y) i) =
    siteBill (board r h) F (outer r h) (body t rev ⟨y,hy⟩ i) := by
  rw [stencil_eq _ _ _ _ i.isLt]
  have hg := physical_geom F _ _ _ _ (body_coord t rev (⟨y,hy⟩ : Fin (h+2)) i)
  have test : (body t rev (⟨y,hy⟩ : Fin (h+2)) i).2.val%3=1 ↔ i.val=1 := by
    change (3*t.val+_)%3=1 ↔ _
    have := i.isLt; cases rev <;> dsimp [body] <;> omega
  simpa only [test] using hg

private theorem row_price (t : Fin r) (rev : Bool) (y : Nat) (hy : y<h+2) :
    let c := camera t rev; let s := stateAt F c y; let a := rowAt F c y
    rowGeom s a + 2*sinks s a = triplePrice F t rev ⟨y,hy⟩ := by
  dsimp only
  have g := body_geom F t rev y hy
  have f (i : Fin 3) := physical_sink F _ y i.val i.isLt _ (body_coord t rev (⟨y,hy⟩ : Fin (h+2)) i)
  unfold rowGeom sinks triplePrice charge
  rw [Fin.sum_univ_three]
  have g₀ := g 0; have g₁ := g 1; have g₂ := g 2
  simp only [Fin.val_zero,Fin.val_one,show ((2:Fin 3):Nat)=2 by decide,
    show decide ((0:Nat)=1)=false by decide,
    show decide ((2:Nat)=1)=false by decide,decide_true] at g₀ g₁ g₂
  have f₀ := f 0; have f₁ := f 1; have f₂ := f 2
  simp only [Fin.val_zero,Fin.val_one,show ((2:Fin 3):Nat)=2 by decide] at f₀ f₁ f₂
  rw [g₀,g₁,g₂,f₀,f₁,f₂]; push_cast; ring

private theorem far_price (pad : Padded F) (t : Fin r) (rev : Bool) :
    (endPadding (stateAt F (camera t rev) h) : Int)=triplePrice F t rev ⟨h+1,by omega⟩ := by
  let c := camera t rev
  have cell (i : Fin 3) : charge F (body t rev (⟨h+1,by omega⟩ : Fin (h+2)) i) =
      (if i.val=1 then 2 else 1)*one (!markBit F c h (i.val+1)) := by
    let v := body t rev (⟨h+1,by omega⟩ : Fin (h+2)) i
    have vm : v∉F := by intro m; have := pad.bottom v m; change h+1+1<h+2 at this; omega
    have geom := physical_geom F c _ _ _ (body_coord t rev (⟨h+1,by omega⟩ : Fin (h+2)) i)
    have iffC : v.2.val%3=1 ↔ i.val=1 := by
      have := i.isLt; dsimp [v,body]; split_ifs <;> omega
    change geometry (decide (v.2.val%3=1)) _ = siteBill (board r h) F (outer r h) v at geom
    change charge F v=_
    simp only [charge,extraRoots,mem_filter,vm,false_and,decide_false,one,←geom,propext iffC]
    simp [geometry,atStencil,touches,no_after F c pad _ _ (by omega : (h:ℤ)+1 ≤ h+1),
      no_after F c pad _ _ (by omega : (h:ℤ)+1 ≤ h+1+1),one]
    split_ifs <;> simp_all
  simp only [endPadding,old_state,maskAt,packed,show 1<5 by decide,show 2<5 by decide,
    show 3<5 by decide,if_pos,triplePrice,Fin.sum_univ_three,cell]
  push_cast; simp [c]

private theorem strip_total (pad : Padded F) (t : Fin r) (rev : Bool)
    (y n : Nat) (endAt : y+n=h) :
    let c := camera t rev; let s := stateAt F c y; let as := scanRows F c y n
    stripGeom s as + 2*stripSinks s as =
      ∑ i : Fin (n+2), triplePrice F t rev ⟨y+i.val,by omega⟩ := by
  dsimp only
  induction n generalizing y with
  | zero =>
    simp at endAt; subst y
    simp only [scanRows,stripGeom,stripSinks]
    rw [Fin.sum_univ_two]
    change _ = triplePrice F t rev ⟨h,_⟩+triplePrice F t rev ⟨h+1,_⟩
    rw [←row_price F t rev h (by omega),←far_price F pad t rev]
    simp only [stop_blank F _ pad]
    ring
  | succ n ih =>
    simp only [scanRows,stripGeom,stripSinks,state_advance _ _ pad,Nat.cast_add]
    rw [Fin.sum_univ_succ]
    have tail := ih (y+1) (by omega)
    rw [show (∑ i : Fin (n+2), triplePrice F t rev ⟨y+i.succ.val,_⟩) =
      ∑ i : Fin (n+2), triplePrice F t rev ⟨y+1+i.val,by omega⟩ by
        apply sum_congr rfl; intro i _; congr 2; simp; omega]
    simp only [Fin.val_zero,Nat.add_zero]
    rw [←tail,←row_price F t rev y (by omega)]
    ring

theorem physical_column_price (pad : Padded F) (t : Fin r) (rev : Bool) :
    (stripCost initial (scanRows F (camera t rev) 0 h) : Int) =
      (∑ y, triplePrice F t rev y)-2 := by
  have geom := strip_total F pad t rev 0 h (by omega)
  dsimp only at geom
  rw [initial_state pad] at geom
  have sumEq : (∑ i : Fin (h+2), triplePrice F t rev ⟨0+i.val,by omega⟩) =
      ∑ y, triplePrice F t rev y := by simp
  rw [sumEq] at geom
  have b := strip_conservation (actual_strip pad t rev)
  have : phi initial=2 := by decide
  omega

end GridGraphs.CapSite
