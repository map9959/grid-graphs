import GridGraphs.Geometry.CapColumnPrice
import GridGraphs.Geometry.CapStripAssembly

namespace GridGraphs.CapSite
open GridGraphs.CapBill GridGraphs.Slit GridGraphs.Slit.Replay GridGraphs.Slit.Data Finset
variable {r h : Nat} (F : Finset (Cell r h))

def flat : Camera := ⟨0,false⟩
noncomputable def cutFace (y j : Nat) : Face :=
  let x := 3*(j:ℤ)-1
  ⟨markBit F flat y x,markBit F flat y (x+1),toward F flat y x 0 1⟩
noncomputable def edgeFace (rev : Bool) (y j : Nat) :=
  if rev then (cutFace F y (r-j)).flip else cutFace F y j
noncomputable def slit (rev : Bool) (j : Nat) : List Nat :=
  (List.range h).map fun y => (edgeFace F rev (y+1) j).code

private theorem pair_read (c : Camera) (y j : Nat) (valid : j=0 ∨ j=3) :
    letter (rowAt F c y) j =
    one (markBit F c (y+1) j)+2*one (markBit F c (y+1) (j+1))+
      4*one (toward F c (y+1) j 0 1) := by
  have head : ∀ m : Fin 32, ∀ j : Fin 4,
      m.val / 2^j.val % 4 = one (bit m.val j.val)+2*one (bit m.val (j.val+1)) := by decide
  have less : j<4 := by omega
  have eq := head ⟨(rowAt F c y).mask,pack_lt ..⟩ ⟨j,less⟩
  unfold letter
  rw [eq]
  simp only [rowAt,maskAt,packed,if_pos less,if_pos (show j<5 by omega),
    if_pos (show j+1<5 by omega),Nat.cast_add,Nat.cast_one]

private theorem normalized_dir (c : Camera) (y x : Int) :
    ((markBit F c y x || markBit F c y (x+1)) && toward F c y x 0 1)=toward F c y x 0 1 := by
  cases e : toward F c y x 0 1
  · simp
  have m := (sends_forced ((toward_iff ..).mp e)).2
  simpa [markBit] using m

private theorem lower_letter (x : Int) (y : Nat) (rev : Bool) (c : Camera)
    (j : Nat) (valid : j=0 ∨ j=3) (dir : c.mirror=rev)
    (base : (c.atP (y+1) j).2 = if rev then x+1 else x)
    (pad : Padded F) :
    let f : Face := ⟨markBit F flat (y+1) x,markBit F flat (y+1) (x+1),toward F flat (y+1) x 0 1⟩
    letter (rowAt F c y) j = (if rev then f.flip else f).code := by
  rw [pair_read _ _ _ _ valid]
  dsimp only
  cases rev with
  | false =>
    simp only [Bool.false_eq_true,if_false] at base ⊢
    simp [Camera.atP,dir] at base
    unfold Face.code Face.dir; rw [normalized_dir]
    have b : c.base+((j:ℤ)+1)=x+1 := by omega
    have point (z : Int) : c.atP z j=flat.atP z x := by simp [Camera.atP,flat,dir,base]
    have next (z : Int) : c.atP z ((j:ℤ)+1)=flat.atP z (x+1) := by simp [Camera.atP,flat,dir,b]
    classical
    let M := fun p => decide (onBoard F p)
    let S := fun p q => decide (sends F p q)
    change one (M _)+2*one (M _)+4*one (S _ _) = one (M _)+2*one (M _)+4*one (S _ _)
    simp only [point,next]
  | true =>
    simp [Camera.atP,dir] at base
    have inv := opposite F flat (y:=(y:ℤ)+1) (x:=x) (dy:=0) (dx:=1) pad (by omega) (by omega) (by simp)
    simp only [add_zero,Int.neg_zero] at inv
    simp only [if_true,Face.flip,Face.code,Face.dir,Bool.or_comm (markBit F flat _ (x+1))]
    rw [inv]
    have a : c.base-(j:ℤ)=x+1 := base
    have b : c.base-((j:ℤ)+1)=x := by omega
    have point (z : Int) : c.atP z j=flat.atP z (x+1) := by simp [Camera.atP,flat,dir,a]
    have next (z : Int) : c.atP z ((j:ℤ)+1)=flat.atP z x := by simp [Camera.atP,flat,dir,b]
    classical
    let M := fun p => decide (onBoard F p)
    let S := fun p q => decide (sends F p q)
    change one (M _)+2*one (M _)+4*one (S _ _) = one (M _)+2*one (M _)+4*one (S _ _)
    simp only [point,next,show x+1+ -1=x by omega]

def columnIndex (r j : Nat) (rev : Bool) := if rev then r-1-j else j
private theorem row_letters (pad : Padded F) (j : Nat) (hj : j<r) (rev : Bool) (y : Nat) :
    let t : Fin r := ⟨columnIndex r j rev,by unfold columnIndex; split_ifs <;> omega⟩
    let a := rowAt F (camera t rev) y
    letter a 0=(edgeFace F rev (y+1) j).code ∧ letter a 3=(edgeFace F rev (y+1) (j+1)).code := by
  dsimp only
  cases rev <;> constructor
  all_goals
    first
      | apply lower_letter F (3*(j:ℤ)-1) y false _ 0 (by decide) rfl _ pad
      | apply lower_letter F (3*((j:ℤ)+1)-1) y false _ 3 (by decide) rfl _ pad
      | apply lower_letter F (3*((r-j:Nat):ℤ)-1) y true _ 0 (by decide) rfl _ pad
      | apply lower_letter F (3*((r-(j+1):Nat):ℤ)-1) y true _ 3 (by decide) rfl _ pad
    simp [columnIndex,camera,Camera.atP] <;> omega

private theorem scan_map (c : Camera) (y n d : Nat) :
    (scanRows F c y n).map (letter · d) =
      (List.range n).map (fun i => letter (rowAt F c (y+i)) d) := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih =>
    rw [scanRows,List.range_succ_eq_map,List.map_cons,List.map_cons,ih]
    simp [List.map_map,Function.comp_def,Nat.add_left_comm,Nat.add_comm]

noncomputable def sideDrop (j : Nat) (rev : Bool) :=
  if hj : j<r then one (dropBit F ⟨columnIndex r j rev,by unfold columnIndex; split_ifs <;> omega⟩) else 0
noncomputable def sideBill (j : Nat) (rev : Bool) :=
  if hj : j<r then stripCost initial (scanRows F (camera
    (⟨columnIndex r j rev,by unfold columnIndex; split_ifs <;> omega⟩ : Fin r) rev) 0 h) else 0

private theorem guard_tape (pad : Padded F) (rev : Bool) (a : Nat) (ha : a∈slit F rev 0) : a=0 := by
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
  have blank (x : Int) (ext : x≤0 ∨ 3*(r:ℤ)-1≤x) : markBit F flat (i+1) x=false := by
    classical
    simp only [markBit,decide_eq_false_iff_not]
    rintro ⟨v,m,eq⟩
    have := pad.sides v m; have ex := (Prod.mk.inj eq).2
    change (v.2.val:ℤ)=0+x at ex; omega
  cases rev <;> simp [edgeFace,cutFace,Face.flip,Face.code,Face.dir,one,blank (-1) (by omega),
    blank 0 (by omega),blank (3*r) (by omega),blank (3*r-1) (by omega)]

/-- Actual synchronized half-cap computed from one parent function. -/
theorem actual_prefix (ok : tablesOK) (pad : Padded F) (rev : Bool) (n : Nat) (hn : n≤r) :
    Prefix n (∑ j ∈ range n, (1-sideDrop F j rev)) (∑ j ∈ range n, sideBill F j rev) (slit F rev n) := by
  induction n with
  | zero => simp only [range_zero,sum_empty]; exact .guard _ (guard_tape F pad rev)
  | succ j ih =>
    have hj : j<r := by omega
    let t : Fin r := ⟨columnIndex r j rev,by unfold columnIndex; split_ifs <;> omega⟩
    have eq : windowKind F t rev = (if j=0 then 0 else 2)+one (dropBit F t) := by
      have iff : outerEnd t rev ↔ j=0 := by
        cases rev <;> simp [t,columnIndex,outerEnd]; omega
      simp only [windowKind,iff]
    rw [sum_range_succ,sum_range_succ,sideDrop,sideBill,dif_pos hj,dif_pos hj]
    apply Prefix.extend _ (by unfold one; split_ifs <;> decide) (ih (by omega))
    have T := (physical_strip_trace ok (show windowKind F t rev<4 by
      rw [eq]; unfold one; split_ifs <;> decide) (actual_strip pad t rev)).1
    rw [trans,eq,scan_map,scan_map] at T
    simp only [Nat.zero_add] at T
    have l (y : Nat) := (row_letters F pad j hj rev y).1
    have b (y : Nat) := (row_letters F pad j hj rev y).2
    simpa only [t,l,b,slit] using T

theorem meet_slit {n m : Nat} (split : n+m=r) :
    Trace reflect 0 0 (slit F false n) (slit F true m) := by
  have h := face_word ((List.range h).map fun y => cutFace F (y+1) n)
  simpa [slit,edgeFace,List.map_map,Function.comp_def,show r-m=n by omega] using h

end GridGraphs.CapSite
