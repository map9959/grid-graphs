import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStripPartition

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip

/-- Little-endian digits: radix 16 for partition representatives and
radix 2 for the two component flag words. -/
def digits (b : Nat) : (n : Nat) → (Fin n → Nat) → Nat
  | 0,_ => 0
  | n+1,f => f 0+b*digits b n (f ∘ Fin.succ)

def digit (b w i : Nat) : Nat := w / b^i % b

theorem digit_digits (b : Nat) (hb : 0<b) (n : Nat) (f : Fin n → Nat)
    (fit : ∀ j, f j<b) (i : Fin n) :
    digit b (digits b n f) i=f i := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [digit,digits,Fin.val_zero,pow_zero,Nat.div_one,Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt (fit 0)
    · simp only [digit,digits,Fin.val_succ,Nat.pow_succ',←Nat.div_div_eq_div_mul,
        Nat.add_mul_div_left _ _ hb,Nat.div_eq_of_lt (fit 0),Nat.zero_add]
      exact ih (f ∘ Fin.succ) (fun i => fit i.succ) j

structure PackedPartition where
  part : Nat
  mark : Nat
  openBits : Nat
deriving DecidableEq, Repr

namespace Partition

def Canonical {n : Nat} (p : Partition n) : Prop :=
  ∀ x, p.label (p.label x)=p.label x ∧
    p.marked (p.label x)=p.marked x ∧ p.opened (p.label x)=p.opened x

theorem forget_canonical {n m : Nat} {V : Type} {p : Partition n}
    {G : SimpleGraph V} {f : Fin n → V} {mark openSite : V → Prop}
    (inv : p.Reflects G f mark openSite) (keep : Fin m → Fin n) :
    (p.forget keep).Canonical := by
  intro x
  have rel := p.representative_in_class keep x
  have reaches := (inv.1 _ _).mp rel
  refine ⟨(p.representative_eq keep (p.representative keep x) x).mpr rel,?_,?_⟩
  all_goals
    apply Bool.eq_iff_iff.mpr
  · rw [show (p.forget keep).marked ((p.forget keep).label x)=p.marked (keep (p.representative keep x)) from rfl]
    rw [show (p.forget keep).marked x=p.marked (keep x) from rfl,inv.2.1,inv.2.1]
    exact ⟨fun ⟨z,r,h⟩ => ⟨z,reaches.symm.trans r,h⟩,fun ⟨z,r,h⟩ => ⟨z,reaches.trans r,h⟩⟩
  · rw [show (p.forget keep).opened ((p.forget keep).label x)=p.opened (keep (p.representative keep x)) from rfl]
    rw [show (p.forget keep).opened x=p.opened (keep x) from rfl,inv.2.2,inv.2.2]
    exact ⟨fun ⟨z,r,h⟩ => ⟨z,reaches.symm.trans r,h⟩,fun ⟨z,r,h⟩ => ⟨z,reaches.trans r,h⟩⟩

def pack {n : Nat} (p : Partition n) : PackedPartition where
  part := digits 16 n (fun i => (p.label i).val)
  mark := digits 2 n (fun i => (p.label i == i && p.marked i).toNat)
  openBits := digits 2 n (fun i => (p.label i == i && p.opened i).toNat)

def readLabel (b : PackedPartition) {n : Nat} (i : Fin n) : Fin n :=
  ⟨digit 16 b.part i % n, Nat.mod_lt _ (by have := i.isLt; omega)⟩

def unpack (n : Nat) (b : PackedPartition) : Partition n where
  label := readLabel b
  marked i := digit 2 b.mark (readLabel b i) == 1
  opened i := digit 2 b.openBits (readLabel b i) == 1

/-- The representation used by a 6- or 9-site frontier plus the
virtual root is lossless. Each nibble is an in-range slot index; the
two bit words are read only at the corresponding representative. -/
theorem unpack_pack {n : Nat} (p : Partition n) (width : n≤16) (hp : p.Canonical) :
    unpack n p.pack = p := by
  have labels (i : Fin n) : readLabel p.pack i=p.label i := by
    apply Fin.ext
    change digit 16 (digits 16 n fun j => (p.label j).val) i % n=(p.label i).val
    rw [digit_digits 16 (by decide) n _ (fun j => Nat.lt_of_lt_of_le (p.label j).isLt width) i]
    exact Nat.mod_eq_of_lt (p.label i).isLt
  have bits (flag : Fin n → Bool) (same : ∀ i, flag (p.label i)=flag i) (i : Fin n) :
      (digit 2 (digits 2 n fun j => (p.label j==j && flag j).toNat) (readLabel p.pack i) == 1) =
        flag i := by
    rw [labels,digit_digits 2 (by decide) n _ (fun j => by cases (p.label j==j && flag j) <;> decide)]
    simp [(hp i).1,same i]
  have m := funext (bits p.marked (fun i => (hp i).2.1))
  have o := funext (bits p.opened (fun i => (hp i).2.2))
  cases p with
  | mk label marked opened =>
    change Partition.mk _ _ _ = Partition.mk _ _ _
    congr 1
    exact funext labels

end Partition
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
