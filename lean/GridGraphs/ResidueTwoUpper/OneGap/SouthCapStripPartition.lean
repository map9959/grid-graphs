import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStripUnion

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
open SimpleGraph

/-- A frontier partition with the two component flags expanded onto
each slot. The packed format subsequently stores flags just at the
canonical representatives. -/
structure Partition (n : Nat) where
  label : Fin n → Fin n
  marked : Fin n → Bool
  opened : Fin n → Bool

namespace Partition
variable {n m : Nat}

def Reflects {V : Type} (p : Partition n) (G : SimpleGraph V) (f : Fin n → V)
    (mark openSite : V → Prop) : Prop :=
  (∀ x y, p.label x=p.label y ↔ G.Reachable (f x) (f y)) ∧
  (∀ x, p.marked x=true ↔ ComponentFlag G mark (f x)) ∧
  (∀ x, p.opened x=true ↔ ComponentFlag G openSite (f x))

def joinFlag (p : Partition n) (flag : Fin n → Bool) (a b x : Fin n) : Bool :=
  flag x || ((p.label x==p.label a) && flag b) || ((p.label x==p.label b) && flag a)

/-- The non-failing part of union-find. Replacing the old left label
everywhere has the same component effect as redirecting its root. -/
def merge (p : Partition n) (a b : Fin n) : Partition n where
  label x := if p.label x=p.label a then p.label b else p.label x
  marked := joinFlag p p.marked a b
  opened := joinFlag p p.opened a b

def insert (p : Partition n) (a b : Fin n) : Option (Partition n) :=
  if p.label a=p.label b then none else some (p.merge a b)

theorem merge_label (p : Partition n) (a b x y : Fin n) :
    (p.merge a b).label x=(p.merge a b).label y ↔
      p.label x=p.label y ∨ (p.label x=p.label a ∧ p.label b=p.label y) ∨
        (p.label x=p.label b ∧ p.label a=p.label y) := by
  by_cases xA : p.label x=p.label a <;> by_cases yA : p.label y=p.label a <;>
    simp [merge,xA,yA,eq_comm] <;> grind

theorem merge_reflects {V : Type} {p : Partition n} {G : SimpleGraph V} {f : Fin n → V}
    {mark openSite : V → Prop} (inv : p.Reflects G f mark openSite)
    {a b : Fin n} (ne : f a≠f b) :
    (p.merge a b).Reflects (G ⊔ SimpleGraph.edge (f a) (f b)) f mark openSite := by
  obtain ⟨part,hm,ho⟩ := inv
  refine ⟨?_,?_,?_⟩
  · intro x y
    simp only [merge_label,reachable_after_union ne,Merged,part]
  · intro x
    simp only [merge,joinFlag,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,part,hm,flag_after_union ne]
    tauto
  · intro x
    simp only [merge,joinFlag,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,part,ho,flag_after_union ne]
    tauto

/-- A fresh edge of the physical acyclic graph performs a successful
merge and produces the exact next partition and flags. -/
theorem insert_reflects {V : Type} {p : Partition n} {G W : SimpleGraph V} {f : Fin n → V}
    {mark openSite : V → Prop} (inv : p.Reflects G f mark openSite)
    (acy : W.IsAcyclic) (sub : G ≤ W) {a b : Fin n} (edge : W.Adj (f a) (f b))
    (fresh : ¬G.Adj (f a) (f b)) :
    p.insert a b=some (p.merge a b) ∧
      (p.merge a b).Reflects (G ⊔ SimpleGraph.edge (f a) (f b)) f mark openSite := by
  have no := fun h => union_does_not_reject acy sub edge fresh ((inv.1 a b).mp h)
  exact ⟨if_neg no,merge_reflects inv edge.ne⟩

/-- Rescan the retained slots in their output order. The first
occurrence of each old label becomes its new representative. -/
def representative (p : Partition n) (keep : Fin m → Fin n) (x : Fin m) : Fin m :=
  ((List.finRange m).find? fun y => p.label (keep y)==p.label (keep x)).getD x

theorem representative_in_class (p : Partition n) (keep : Fin m → Fin n) (x : Fin m) :
    p.label (keep (p.representative keep x))=p.label (keep x) := by
  unfold representative
  cases eq : (List.finRange m).find? (fun y => p.label (keep y)==p.label (keep x)) with
  | none => rfl
  | some _ =>
    have h := List.find?_some eq
    exact beq_iff_eq.mp h

theorem representative_eq (p : Partition n) (keep : Fin m → Fin n) (x y : Fin m) :
    p.representative keep x=p.representative keep y ↔ p.label (keep x)=p.label (keep y) := by
  constructor
  · intro h
    rw [←p.representative_in_class keep x,←p.representative_in_class keep y,h]
  · intro h
    unfold representative
    have existsX : ((List.finRange m).find? fun z => p.label (keep z)==p.label (keep x)).isSome := by
      apply List.find?_isSome.mpr
      exact ⟨x,List.mem_finRange _,beq_self_eq_true _⟩
    simp only [h] at existsX ⊢
    cases e : (List.finRange m).find? (fun z => p.label (keep z)==p.label (keep y)) with
    | none => simp [e] at existsX
    | some _ => rfl

def forget (p : Partition n) (keep : Fin m → Fin n) : Partition m where
  label := p.representative keep
  marked := p.marked ∘ keep
  opened := p.opened ∘ keep

/-- Retiring a line does not mean taking an induced graph on the
frontier. Paths through retired sites still determine its classes. -/
theorem forget_reflects {V : Type} {p : Partition n} {G : SimpleGraph V} {f : Fin n → V}
    {mark openSite : V → Prop} (inv : p.Reflects G f mark openSite)
    (keep : Fin m → Fin n) : (p.forget keep).Reflects G (f ∘ keep) mark openSite :=
  ⟨fun x y => (p.representative_eq keep x y).trans (inv.1 _ _),
    fun x => inv.2.1 (keep x),fun x => inv.2.2 (keep x)⟩

def rejectsForgotten (p : Partition n) (old : List (Fin n)) (keep : Fin m → Fin n) : Bool :=
  old.any fun x => p.marked x && !p.opened x &&
    !((List.finRange m).any fun y => p.label (keep y)==p.label x)

/-- Forgetting is safe exactly when no disappearing class is both
marked and closed. Scanning all old slots is equivalent to scanning
only representatives, since membership and both flags are class data. -/
theorem rejectsForgotten_iff {V : Type} {p : Partition n} {G : SimpleGraph V} {f : Fin n → V}
    {mark openSite : V → Prop} (inv : p.Reflects G f mark openSite)
    (old : List (Fin n)) (keep : Fin m → Fin n) :
    p.rejectsForgotten old keep=true ↔ ∃ x∈old,
      ComponentFlag G mark (f x) ∧ ¬ComponentFlag G openSite (f x) ∧
        ∀ y, ¬G.Reachable (f (keep y)) (f x) := by
  simp only [rejectsForgotten,List.any_eq_true,Bool.and_eq_true,Bool.not_eq_true',
    List.any_eq_false,List.mem_finRange,true_implies,beq_iff_eq,inv.1,inv.2.1]
  constructor
  · rintro ⟨x,hx,⟨hm,no⟩,gone⟩
    exact ⟨x,hx,hm,fun h => Bool.noConfusion (no.symm.trans ((inv.2.2 x).mpr h)),gone⟩
  · rintro ⟨x,hx,hm,no,gone⟩
    exact ⟨x,hx,⟨hm,Bool.eq_false_iff.mpr (fun h => no ((inv.2.2 x).mp h))⟩,gone⟩

end Partition
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
