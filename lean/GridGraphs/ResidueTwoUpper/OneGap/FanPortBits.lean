import GridGraphs.ResidueTwoUpper.OneGap.FanPortQuad
namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.Port
open L7 FanSlab

abbrev Dir := Fin 9 → Fin 4
abbrev Ink := Fin 9 → Bool
def lift (f : Dir) (i : Nat) := (f (Fin.ofNat 9 i)).val
def digit (f : Dir) (i j : Nat) := ((field (lift f) i).1 >>> (2*j))%4
def label (m : Nat) (f : Dir) := (m <<< 12)+(field (lift f) 9).2
def idx (d : Fin 4) (k : Fin 3) : Fin 9 := ⟨if d.val=0 then 3*k.val+2 else if d.val=1 then 6+k.val else if d.val=2 then 3*k.val else k.val,by split_ifs <;> omega⟩
def three (f : Fin 3 → Bool) := (f 0).toNat+2*(f 1).toNat+4*(f 2).toNat

def Own (a b m n : Bool) := ((a != b) == (m || n)) && !(a && b)
private theorem order (a b m n : Bool) : Own a b m n = Own b a n m := by cases a <;> cases b <;> cases m <;> cases n <;> rfl
theorem maskbits : ∀ f : Ink, ∀ i : Fin 9, (bits f).testBit i.val=f i := by native_decide
theorem digits : ∀ (f : Dir) (i : Fin 9),
    (i.val%3≠0 → digit f i.val (i.val-1)=lift f (i.val-1)) ∧ (3≤ i.val → digit f i.val (i.val-3)=lift f (i.val-3)) := by native_decide
theorem portBits : ∀ f : Dir, (field (lift f) 9).2<4096 ∧ ∀ d : Fin 4,
    out (field (lift f) 9).2 d.val=three (fun k => f (idx d k)==d) := by native_decide

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.Port
