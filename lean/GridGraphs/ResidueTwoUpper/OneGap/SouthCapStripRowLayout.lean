import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStripRow

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
open SimpleGraph

namespace Row

abbrev oldSlot {n : Nat} (i : Fin (n+1)) : Fin (n+1+n) := Fin.castAdd n i
abbrev newSlot {n : Nat} (i : Fin n) : Fin (n+1+n) := Fin.natAdd (n+1) i
def keep {n : Nat} : Fin (n+1) → Fin (n+1+n) :=
  Fin.lastCases (oldSlot (Fin.last n)) newSlot
def drop (n : Nat) : List (Fin (n+1+n)) :=
  (List.finRange n).map (fun i => oldSlot i.castSucc)

/-- Old row first, then the apex, then the new row. This is the
temporary union-find layout of `row` before taking representatives
in the new-row-then-apex order. -/
def extend {n : Nat} (p : Partition (n+1)) (mark opened : Fin n → Bool) :
    Partition (n+1+n) where
  label := Fin.addCases (oldSlot ∘ p.label) newSlot
  marked := Fin.addCases p.marked mark
  opened := Fin.addCases p.opened opened

private theorem isolated_reach {V : Type} {G : SimpleGraph V} {x y : V}
    (iso : G.IsIsolated x) (reach : G.Reachable x y) : x=y := by
  obtain ⟨p⟩ := reach
  cases p with
  | nil => rfl
  | cons e _ => exact (iso _ e).elim

theorem extend_reflects {V : Type} {n : Nat} {p : Partition (n+1)} {G : SimpleGraph V}
    {f : Fin (n+1+n) → V} {mark openSite : V → Prop} (inj : Function.Injective f)
    (old : p.Reflects G (f ∘ oldSlot) mark openSite) (isolated : ∀ i, G.IsIsolated (f (newSlot i)))
    (bMark bOpen : Fin n → Bool)
    (marks : ∀ i, bMark i=true ↔ mark (f (newSlot i)))
    (opens : ∀ i, bOpen i=true ↔ openSite (f (newSlot i))) :
    (extend p bMark bOpen).Reflects G f mark openSite := by
  have disj (a : Fin (n+1)) (b : Fin n) : oldSlot a≠newSlot b := by
    intro eq
    have h := congrArg Fin.val eq
    have l := a.isLt
    change a.val=n+1+b.val at h
    omega
  have sep (a : Fin (n+1)) (b : Fin n) : ¬G.Reachable (f (oldSlot a)) (f (newSlot b)) :=
    fun r => disj a b (inj (isolated_reach (isolated b) r.symm).symm)
  refine ⟨?_,?_,?_⟩
  · intro a b
    refine Fin.addCases (fun x => ?_) (fun x => ?_) a <;>
      refine Fin.addCases (fun y => ?_) (fun y => ?_) b
    · simp only [extend,Fin.addCases_left,Function.comp_apply,Fin.castAdd_inj]
      exact old.1 x y
    · simp only [extend,Fin.addCases_left,Fin.addCases_right,Function.comp_apply,
        disj,sep]
    · simp only [extend,Fin.addCases_left,Fin.addCases_right,Function.comp_apply]
      exact iff_of_false (Ne.symm (disj _ _)) (fun r => sep y x r.symm)
    · simp only [extend,Fin.addCases_right]
      refine ⟨?_,fun r => inj (isolated_reach (isolated x) r)⟩
      intro e
      change G.Reachable (f (newSlot x)) (f (newSlot y))
      rw [e]
  · intro i
    refine Fin.addCases (fun x => ?_) (fun x => ?_) i
    · simp only [extend,Fin.addCases_left]
      exact old.2.1 x
    · simp only [extend,Fin.addCases_right,marks,ComponentFlag]
      exact ⟨fun h => ⟨_,.rfl,h⟩,fun ⟨z,r,h⟩ => (isolated_reach (isolated x) r).symm ▸ h⟩
  · intro i
    refine Fin.addCases (fun x => ?_) (fun x => ?_) i
    · simp only [extend,Fin.addCases_left]
      exact old.2.2 x
    · simp only [extend,Fin.addCases_right,opens,ComponentFlag]
      exact ⟨fun h => ⟨_,.rfl,h⟩,fun ⟨z,r,h⟩ => (isolated_reach (isolated x) r).symm ▸ h⟩

/-- Vertical bond, horizontal bond to the previous site, then apex
wire, in the same order as the three insertion tests in Rust. A
missing previous row is the initialization sentinel, not a mark row. -/
def edges {n : Nat} (previous : Option (Fin n → Bool)) (mark tooth : Fin n → Bool) :
    List (SlotEdge (n+1+n)) :=
  (List.finRange n).flatMap fun i =>
    (if previous.any (fun old => old i || mark i) then [(oldSlot i.castSucc,newSlot i)] else []) ++
    (if h : 0 < i.val then
      let j : Fin n := ⟨i.val-1,by have := i.isLt; omega⟩
      if mark j || mark i then [(newSlot j,newSlot i)] else []
      else []) ++
    (if mark i && tooth i then [(newSlot i,oldSlot (Fin.last n))] else [])

def transition {n : Nat} (packed : PackedPartition) (previous : Option (Fin n → Bool))
    (mark tooth exits : Fin n → Bool) : Option PackedPartition :=
  rowCore (extend (Partition.unpack (n+1) packed) mark exits)
    (edges previous mark tooth) (drop n) keep

/-- One indexed packed row transition, including allocating the new
slots and forgetting the old ones. Its remaining hypotheses are
about the physical interpretation of the scheduled edges and flags. -/
theorem transition_reflects {V : Type} {n : Nat} {packed : PackedPartition}
    {G W : SimpleGraph V} {f : Fin (n+1+n) → V} {mark openSite : V → Prop}
    (inj : Function.Injective f)
    (old : (Partition.unpack (n+1) packed).Reflects G (f ∘ oldSlot) mark openSite)
    (isolated : ∀ i, G.IsIsolated (f (newSlot i)))
    (previous : Option (Fin n → Bool)) (bMark tooth exits : Fin n → Bool)
    (marks : ∀ i, bMark i=true ↔ mark (f (newSlot i)))
    (opens : ∀ i, exits i=true ↔ openSite (f (newSlot i)))
    (acy : W.IsAcyclic) (sub : G ≤ W) (size : n+1≤16)
    (schedule : FreshSchedule f W G (edges previous bMark tooth))
    (closure : RowClosure (addEdges f G (edges previous bMark tooth)) f mark openSite (drop n) keep) :
    ∃ out, transition packed previous bMark tooth exits=some out ∧
      (Partition.unpack (n+1) out).Reflects (addEdges f G (edges previous bMark tooth))
        (f ∘ keep) mark openSite :=
  rowCore_reflects (extend_reflects inj old isolated bMark exits marks opens) acy sub
    _ schedule size _ _ closure

end Row
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
