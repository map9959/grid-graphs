import GridGraphs.ResidueTwoUpper.TwoGapFrontierLedger

namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.ExitReplay
open SimpleGraph Finset ResidueZero Stencil BoundarySix.Connected Catalogue Words

variable {u : Nat}
def wordRow (F : Finset (Board u)) (l t : Nat) := packed9 (fun i => decide (rowSite u l t i∈F))
def pinMask (d l t : Nat) := packed9 fun i =>
  decide ((t=2 ∧ l+i.val≠d) ∨ t=high u-2)

theorem packed_bits : ∀ (f : Fin 9 → Bool) (i : Fin 9),
    (packed9 f).testBit i=f i := by native_decide

theorem wordRow_bit (F : Finset (Board u)) (l t : Nat) (i : Fin 9) :
    (wordRow F l t).testBit i=decide (rowSite u l t i∈F) := packed_bits .. 

theorem row_rc (l t : Nat) (ht : t<Size u) (hl : l+8<Size u) (i : Fin 9) :
    North.rc (rowSite u l t i)=(t,l+i.val) := by
  simp [North.rc,rowSite,Fin.val_ofNat,Nat.mod_eq_of_lt ht,Nat.mod_eq_of_lt (by omega : l+i.val<Size u)]

theorem rowRoot (l t : Nat) (i : Fin 9) :
    rootPort u l t ⟨i.val,by omega⟩=rowSite u l t i := by
  simp [rootPort,i.isLt]
theorem oldPort (l t : Nat) (i : Fin 9) :
    rowPort u l t ⟨i.val,by omega⟩=rowSite u l t i := by
  simp [rowPort,rootPort,i.isLt,show i.val<10 by omega,Fin.ofNat_eq_cast,
    Fin.val_natCast,Nat.mod_eq_of_lt (show i.val<10 by omega)]
theorem newPort (l t : Nat) (i : Fin 9) : rowPort u l t (newSlot i)=rowSite u l (t+1) i := by
  simp [rowPort,newSlot]
theorem centerPort (l t : Nat) : rowPort u l t 9=nw u := by rfl

theorem row_inj {l t : Nat} (hl : 0<l ∧ l+8<Size u) (ht : t+1<Size u) :
    Function.Injective (rowPort u l t) := by
  have desc (i : Fin 19) : North.rc (rowPort u l t i)=
      if i.val<9 then (t,l+i.val) else if i.val=9 then (0,0) else (t+1,l+(i.val-10)) := by
    by_cases a : i.val<9
    · rw [if_pos a,show rowPort u l t i=rowSite u l t ⟨i.val,a⟩ from oldPort l t ⟨i.val,a⟩,row_rc _ _ (by omega) hl.2]
    · rw [if_neg a]; by_cases b : i.val=9
      · have eq : i=9 := Fin.ext b; subst i; rfl
      · rw [if_neg b]
        let j : Fin 9 := ⟨i.val-10,by omega⟩
        have eq : i=newSlot j := Fin.ext (by dsimp [newSlot,j]; omega)
        rw [eq,newPort,row_rc _ _ ht hl.2]; simp [newSlot]
  intro i j e
  have eq := congrArg North.rc e
  rw [desc,desc] at eq
  apply Fin.ext; split_ifs at eq <;> simp_all [Prod.mk.injEq] <;> omega

theorem slot_flags (F : Finset (Board u)) (l t : Nat) (hl : 0<l ∧ l+8<Size u) (ht : t+1<Size u)
    (i : Fin 9) (d : Fin 2) :
    (flag (wordRow F l (t+1)) i).testBit d ↔ events F l d (rowPort u l t (newSlot i)) := by
  rw [newPort]
  have eq := row_rc l (t+1) ht hl.2 i
  have rr := congrArg Prod.fst eq; have cc := congrArg Prod.snd eq
  change (rowSite u l (t+1) i).1.val=t+1 at rr
  change (rowSite u l (t+1) i).2.val=l+i.val at cc
  have ne : rowSite u l (t+1) i≠nw u := by intro h; rw [h] at rr; change 0=t+1 at rr; omega
  unfold flag
  rw [wordRow_bit]
  have Q : ∀ (b : Bool) (j : Fin 9) (a : Fin 2),
      ((if b then 2 else 0) + (if j.val=0 ∨ j.val=8 then 1 else 0):Nat).testBit a =
      (if a=0 then decide (j.val=0 ∨ j.val=8) else b) := by native_decide
  rw [Q]; unfold events; split_ifs <;> simp only [decide_eq_true_eq,rr,cc,ne,false_or] <;> grind

theorem row_iso (F : Finset (Board u)) (d l t : Nat) (hl : l+8<Size u) (ht : t+1<Size u) :
    ∀ i y, ¬(built F d l t).Adj (rowPort u l t (newSlot i)) y := by
  intro i y e
  have h := (built_box e).1
  rw [newPort] at h
  have rr := congrArg Prod.fst (row_rc l (t+1) ht hl i)
  change (rowSite u l (t+1) i).1.val=t+1 at rr
  rcases h with box|eq
  · exact (by have := box.2.1; omega : False)
  · rw [eq] at rr; change 0=t+1 at rr; omega

abbrev U := Fin 19
def directed (i : Fin 9) : Fin 3 → Pair :=
  ![(⟨i.val,by omega⟩,newSlot i),(⟨9+i.val,by omega⟩,newSlot i),(newSlot i,9)]
def enabled (old m teeth : Nat) (i : Fin 9) : Fin 3 → Bool :=
  ![old<512 && (old ||| m).testBit i, i.val>0 && (m.testBit (i.val-1) || m.testBit i),
    (m &&& teeth).testBit i]

theorem row_mem {e : Pair} (old m teeth : Nat) :
    e∈rowEdges old m teeth ↔ ∃ i : Fin 9, ∃ k : Fin 3, enabled old m teeth i k ∧ e=directed i k := by
  unfold rowEdges
  rw [List.mem_flatMap]
  have aux (i : Fin 9) : e∈rowEdgesAt old m teeth i ↔ ∃ k : Fin 3, enabled old m teeth i k ∧ e=directed i k := by
    unfold rowEdgesAt
    rw [Fin.exists_fin_succ,Fin.exists_fin_succ,Fin.exists_fin_succ]
    simp only [Fin.exists_fin_zero,or_false,enabled,directed,Matrix.cons_val_zero,Matrix.cons_val_succ,
      Matrix.cons_val_fin_one,Fin.val_succ,Fin.val_zero]
    have a : Fin.ofNat 19 i.val=(⟨i.val,by omega⟩ : U) := Fin.ext (Nat.mod_eq_of_lt (by omega))
    have b : Fin.ofNat 19 (10+i.val)=newSlot i := Fin.ext (Nat.mod_eq_of_lt (by omega))
    have c : Fin.ofNat 19 (9+i.val)=(⟨9+i.val,by omega⟩ : U) := Fin.ext (Nat.mod_eq_of_lt (by omega))
    split_ifs <;> simp_all [a,b,c] <;> grind
  constructor
  · rintro ⟨i,hi,h⟩; exact ⟨⟨i,List.mem_range.mp hi⟩,(aux _).mp h⟩
  · rintro ⟨i,h⟩; exact ⟨i,List.mem_range.mpr i.isLt,(aux _).mpr h⟩

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.ExitReplay
