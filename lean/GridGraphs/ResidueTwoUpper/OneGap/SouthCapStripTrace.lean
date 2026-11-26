import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStripRowLayout

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
open SimpleGraph
namespace Row

structure Program (n : Nat) where
  mark : Nat → Fin n → Bool
  tooth : Nat → Fin n → Bool
  exits : Nat → Fin n → Bool

def Program.previous {n : Nat} (p : Program n) : Nat → Option (Fin n → Bool)
  | 0 => none
  | j+1 => some (p.mark j)

def Program.advance {n : Nat} (p : Program n) (j : Nat) (s : PackedPartition) :
    Option PackedPartition :=
  transition s (p.previous j) (p.mark j) (p.tooth j) (p.exits j)

def Program.run {n : Nat} (p : Program n) (b : PackedPartition) :
    Nat → Option PackedPartition
  | 0 => some b
  | j+1 => (p.run b j).bind (p.advance j)

/-- A graph interpretation for a finite sequence of physical rows.
Each old frontier is the same one that the preceding row retained.
The fields state the geometric obligations, not that a machine
transition succeeded. -/
structure Realization {V : Type} {n : Nat} (p : Program n) (length : Nat)
    (W : SimpleGraph V) (mark openSite : V → Prop) where
  graph : Nat → SimpleGraph V
  frontier : Nat → Fin (n+1) → V
  slots : Nat → Fin (n+1+n) → V
  injective : ∀ j < length, Function.Injective (slots j)
  reuses : ∀ j < length, slots j ∘ oldSlot = frontier j
  retains : ∀ j < length, slots j ∘ keep = frontier (j+1)
  newIsolated : ∀ j < length, ∀ i, (graph j).IsIsolated (slots j (newSlot i))
  marks : ∀ j < length, ∀ i, p.mark j i=true ↔ mark (slots j (newSlot i))
  opens : ∀ j < length, ∀ i, p.exits j i=true ↔ openSite (slots j (newSlot i))
  subgraph : ∀ j < length, graph j ≤ W
  schedule : ∀ j < length, FreshSchedule (slots j) W (graph j) (edges (p.previous j) (p.mark j) (p.tooth j))
  advances : ∀ j < length, addEdges (slots j) (graph j)
    (edges (p.previous j) (p.mark j) (p.tooth j))=graph (j+1)
  closure : ∀ j < length, RowClosure (graph (j+1)) (slots j) mark openSite (drop n) keep

/-- A whole accepted packed run, once the geometric row interpretation
is supplied. The induction does not need to retain retired slots or
choose a fresh representative in the actual forest. -/
theorem packed_run_reflects {V : Type} {n length : Nat} {p : Program n}
    {W : SimpleGraph V} {mark openSite : V → Prop}
    (R : Realization p length W mark openSite) (acy : W.IsAcyclic) (size : n+1≤16)
    {base : PackedPartition}
    (initial : (Partition.unpack (n+1) base).Reflects (R.graph 0) (R.frontier 0) mark openSite) :
    ∀ j ≤ length, ∃ s, p.run base j=some s ∧
      (Partition.unpack (n+1) s).Reflects (R.graph j) (R.frontier j) mark openSite := by
  intro j
  induction j with
  | zero => intro _; exact ⟨base,rfl,initial⟩
  | succ j ih =>
    intro bound
    have lt : j<length := by omega
    obtain ⟨old,done,inv⟩ := ih (by omega)
    have oldInv : (Partition.unpack (n+1) old).Reflects (R.graph j)
        (R.slots j ∘ oldSlot) mark openSite := by
      rwa [R.reuses j lt]
    have close := R.closure j lt
    rw [←R.advances j lt] at close
    obtain ⟨out,step,next⟩ := transition_reflects (R.injective j lt) oldInv
      (R.newIsolated j lt) (p.previous j) (p.mark j) (p.tooth j) (p.exits j)
      (R.marks j lt) (R.opens j lt) acy (R.subgraph j lt) size (R.schedule j lt) close
    rw [R.advances j lt,R.retains j lt] at next
    refine ⟨out,?_,next⟩
    rw [Program.run,done]
    exact step

/-- The initial state's only open class is the unmarked virtual
root. All previous-row slots are isolated sentinel slots. -/
def basePartition (n : Nat) : Partition (n+1) :=
  ⟨id,fun _ => false,fun i => i==Fin.last n⟩

def Program.accepts (n : Nat) (s : PackedPartition) : Bool :=
  let p := Partition.unpack (n+1) s
  (List.finRange (n+1)).all fun i => !p.marked i || p.opened i

theorem base_reflects {V : Type} {n : Nat} (size : n+1≤16) {f : Fin (n+1) → V}
    {mark openSite : V → Prop} (inj : Function.Injective f)
    (marks : ∀ i, ¬mark (f i)) (opens : ∀ i, openSite (f i) ↔ i=Fin.last n) :
    (Partition.unpack (n+1) (basePartition n).pack).Reflects ⊥ f mark openSite := by
  rw [Partition.unpack_pack _ size (fun _ => ⟨rfl,rfl,rfl⟩)]
  refine ⟨?_,?_,?_⟩
  · intro x y
    simp only [basePartition,id_eq,reachable_bot]
    exact inj.eq_iff.symm
  · intro i
    simp [basePartition,ComponentFlag,reachable_bot,marks i]
  · intro i
    simp [basePartition,ComponentFlag,reachable_bot,opens i]

/-- Terminal acceptance tests exactly the components still
represented at the frontier; sealed ones already dropped were
checked at the row where they disappeared. -/
theorem accepts_iff {V : Type} {n : Nat} {s : PackedPartition} {G : SimpleGraph V}
    {f : Fin (n+1) → V} {mark openSite : V → Prop}
    (inv : (Partition.unpack (n+1) s).Reflects G f mark openSite) :
    Program.accepts n s=true ↔ ∀ i, ComponentFlag G mark (f i) → ComponentFlag G openSite (f i) := by
  unfold Program.accepts
  simp only [List.all_eq_true,List.mem_finRange,true_implies,Bool.or_eq_true,Bool.not_eq_true',inv.2.2]
  constructor
  · intro ok i h
    exact (ok i).resolve_left (fun no => Bool.noConfusion (no.symm.trans ((inv.2.1 i).mpr h)))
  · intro ok i
    by_cases h : (Partition.unpack (n+1) s).marked i=true
    · exact .inr (ok i ((inv.2.1 i).mp h))
    · exact .inl (Bool.eq_false_iff.mpr h)

theorem packed_run_accepts {V : Type} {n length : Nat} {p : Program n}
    {W : SimpleGraph V} {mark openSite : V → Prop}
    (R : Realization p length W mark openSite) (acy : W.IsAcyclic) (size : n+1≤16)
    {base : PackedPartition}
    (initial : (Partition.unpack (n+1) base).Reflects (R.graph 0) (R.frontier 0) mark openSite)
    (final : ∀ i, ComponentFlag (R.graph length) mark (R.frontier length i) →
      ComponentFlag (R.graph length) openSite (R.frontier length i)) :
    ∃ s, p.run base length=some s ∧ Program.accepts n s=true := by
  obtain ⟨s,done,inv⟩ := packed_run_reflects R acy size initial length le_rfl
  exact ⟨s,done,(accepts_iff inv).mpr final⟩

end Row
end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
