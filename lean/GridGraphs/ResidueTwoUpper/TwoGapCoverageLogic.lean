import GridGraphs.ResidueTwoUpper.TwoGapExitProjection
import Std.Sat.CNF.Dimacs

namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Coverage
open Catalogue ResidueZero Std.Sat

-- A mark, four outgoing arc bits, and the compass sheet at a labelled site.
abbrev Wire := Pos × Fin 6
def mark (p : Pos) : Wire := (p,0)
def arrow (p : Pos) (d : Fin 4) : Wire := (p,⟨1+d,by omega⟩)
def sheet (p : Pos) : Wire := (p,5)
def value (l : Field) (w : Wire) : Bool :=
  if w.2=0 then l.mark w.1 else if w.2=5 then l.sheet w.1 else decide (l.dir w.1=w.2.val-1)
@[simp] theorem val_mark (l p) : value l (mark p)=l.mark p := rfl
@[simp] theorem val_sheet (l p) : value l (sheet p)=l.sheet p := rfl
@[simp] theorem val_arrow (l p d) : value l (arrow p d)=decide (l.dir p=d.val) := by
  fin_cases d <;> rfl

abbrev Rows := List (CNF.Clause Wire)
def Holds (a : Wire → Bool) (r : Rows) := ∀ c ∈ r, c.eval a=true
def lit (w : Wire) (v : Bool) : Rows := [[(w,v)]]
def guarded (w : Wire) (v : Bool) (r : Rows) : Rows := r.map ((w,!v)::·)
def branch (w : Wire) (lo hi : Rows) : Rows :=
  if lo=hi then lo else guarded w false lo ++ guarded w true hi
@[simp] theorem holds_append (a x y) : Holds a (x++y) ↔ Holds a x ∧ Holds a y := by
  simp [Holds]; aesop
@[simp] theorem holds_lit (a w v) : Holds a (lit w v) ↔ a w=v := by simp [Holds,lit]
@[simp] theorem holds_guarded (a w v r) : Holds a (guarded w v r) ↔ (a w=v → Holds a r) := by
  cases h : a w <;> cases v <;> simp [Holds,guarded,h]
theorem holds_branch (a w lo hi) : Holds a (branch w lo hi) ↔ Holds a (if a w then hi else lo) := by
  unfold branch; split_ifs with eq <;> cases h : a w <;> simp_all
@[simp] theorem holds_nil (a) : Holds a [] := by simp [Holds]
@[simp] theorem holds_flat {α} (a) (xs : List α) (f : α → Rows) :
    Holds a (xs.flatMap f) ↔ ∀ x ∈ xs, Holds a (f x) := by simp [Holds]; aesop

def bits (a : Wire → Bool) : List Wire → Nat
  | [] => 0
  | w::ws => (a w).toNat+2*bits a ws
def truth : List Wire → (Nat → Bool) → Rows
  | [],f => if f 0 then [] else [[]]
  | w::ws,f => branch w (truth ws (fun m => f (2*m))) (truth ws (fun m => f (1+2*m)))
theorem holds_truth (a ws f) : Holds a (truth ws f) ↔ f (bits a ws)=true := by
  induction ws generalizing f with
  | nil => simp only [truth,bits]; split <;> simp_all [Holds]
  | cons w ws ih => rw [truth,holds_branch]; cases h : a w <;> simp [ih,bits,h]

def number (w : Wire) := 6*Nat.pair (Equiv.intEquivNat w.1.1) (Equiv.intEquivNat w.1.2)+w.2.val
theorem number_inj : Function.Injective number := by
  rintro ⟨⟨r,c⟩,i⟩ ⟨⟨s,t⟩,j⟩ h
  change 6*Nat.pair (Equiv.intEquivNat r) (Equiv.intEquivNat c)+i.val=6*Nat.pair (Equiv.intEquivNat s) (Equiv.intEquivNat t)+j.val at h
  have eq : Nat.pair (Equiv.intEquivNat r) (Equiv.intEquivNat c)=Nat.pair (Equiv.intEquivNat s) (Equiv.intEquivNat t) := by omega
  have ⟨u,v⟩ := Nat.pair_eq_pair.mp eq
  have hi : i=j := Fin.ext (by omega)
  rw [Equiv.intEquivNat.injective u,Equiv.intEquivNat.injective v,hi]
def formula (r : Rows) := (⟨r.toArray⟩ : CNF Wire).relabel number
theorem impossible (r : Rows) (unsat : (formula r).Unsat) (a : Wire → Bool) (h : Holds a r) : False := by
  have u := (CNF.unsat_relabel_iff (fun _ _ eq => number_inj eq)).mp unsat a
  have e : (⟨r.toArray⟩ : CNF Wire).eval a=true := by simpa [Holds,CNF.eval,Array.all_eq_true] using h
  exact Bool.noConfusion (e.symm.trans u)

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.Coverage
