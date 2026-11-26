import GridGraphs.ResidueTwoUpper.OneGap.SouthCapStripWiredForest

namespace GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
open SimpleGraph

/-- The exact equivalence relation obtained by merging two classes.
No vertex outside either old class changes its connectivity. -/
def Merged {V : Type} (G : SimpleGraph V) (a b x y : V) : Prop :=
  G.Reachable x y ∨ (G.Reachable x a ∧ G.Reachable b y) ∨
    (G.Reachable x b ∧ G.Reachable a y)

theorem reachable_after_union {V : Type} {G : SimpleGraph V} {a b x y : V} (ne : a≠b) :
    (G ⊔ SimpleGraph.edge a b).Reachable x y ↔ Merged G a b x y := by
  constructor
  · rintro ⟨p⟩
    induction p with
    | nil => exact .inl .rfl
    | @cons i j k e p ih =>
      rcases (show G.Adj i j ∨ (SimpleGraph.edge a b).Adj i j from e) with e|e
      · rcases ih with r|⟨s,t⟩|⟨s,t⟩
        · exact .inl (e.reachable.trans r)
        · exact .inr (.inl ⟨e.reachable.trans s,t⟩)
        · exact .inr (.inr ⟨e.reachable.trans s,t⟩)
      · obtain ⟨e,_⟩ := (edge_adj a b i j).mp e
        rcases e with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · rcases ih with r|⟨_,r⟩|⟨_,r⟩
          · exact .inr (.inl ⟨.rfl,r⟩)
          · exact .inr (.inl ⟨.rfl,r⟩)
          · exact .inl r
        · rcases ih with r|⟨_,r⟩|⟨_,r⟩
          · exact .inr (.inr ⟨.rfl,r⟩)
          · exact .inl r
          · exact .inr (.inr ⟨.rfl,r⟩)
  · intro h
    have e : (G ⊔ SimpleGraph.edge a b).Adj a b :=
      (le_sup_right : SimpleGraph.edge a b ≤ _)
        ((edge_adj a b a b).mpr ⟨.inl ⟨rfl,rfl⟩,ne⟩)
    rcases h with h|⟨r,t⟩|⟨r,t⟩
    · exact h.mono le_sup_left
    · exact (r.mono le_sup_left).trans (e.reachable.trans (t.mono le_sup_left))
    · exact (r.mono le_sup_left).trans (e.symm.reachable.trans (t.mono le_sup_left))

def ComponentFlag {V : Type} (G : SimpleGraph V) (P : V → Prop) (x : V) : Prop :=
  ∃ z, G.Reachable x z ∧ P z

/-- Union-find's mark and open flags are disjunctions over the new
component. This proves the OR update for either flag at once. -/
theorem flag_after_union {V : Type} {G : SimpleGraph V} {a b x : V}
    (ne : a≠b) (P : V → Prop) :
    ComponentFlag (G ⊔ SimpleGraph.edge a b) P x ↔
      ComponentFlag G P x ∨ (G.Reachable x a ∧ ComponentFlag G P b) ∨
        (G.Reachable x b ∧ ComponentFlag G P a) := by
  unfold ComponentFlag
  constructor
  · rintro ⟨z,r,p⟩
    rcases (reachable_after_union ne).mp r with t|⟨t,s⟩|⟨t,s⟩
    · exact .inl ⟨z,t,p⟩
    · exact .inr (.inl ⟨t,z,s,p⟩)
    · exact .inr (.inr ⟨t,z,s,p⟩)
  · rintro (⟨z,t,p⟩|⟨t,z,s,p⟩|⟨t,z,s,p⟩)
    · exact ⟨z,(reachable_after_union ne).mpr (.inl t),p⟩
    · exact ⟨z,(reachable_after_union ne).mpr (.inr (.inl ⟨t,s⟩)),p⟩
    · exact ⟨z,(reachable_after_union ne).mpr (.inr (.inr ⟨t,s⟩)),p⟩

/-- When an engine row inserts a new physical edge exactly once, its
cycle test cannot reject an acyclic wired forest. -/
theorem union_does_not_reject {V : Type} {G W : SimpleGraph V} {a b : V}
    (acy : W.IsAcyclic) (old : G ≤ W) (edge : W.Adj a b) (fresh : ¬G.Adj a b) :
    ¬G.Reachable a b := by
  have e : SimpleGraph.edge a b ≤ W := by
    intro x y xy
    rcases ((edge_adj a b x y).mp xy).1 with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact edge
    · exact edge.symm
  have sub : G ⊔ SimpleGraph.edge a b ≤ W := sup_le old e
  have h := (isAcyclic_sup_fromEdgeSet_iff.mp (acy.anti sub)).2
  intro r
  exact (h r).elim edge.ne fresh

/-- Dropping inactive vertices does not lose information needed by
later insertions: agreement on the active frontier and its flags is
preserved by a union of any two vertices on that frontier. -/
theorem frontier_agrees_after_union {V : Type} {G K : SimpleGraph V} {S : Set V}
    {a b : V} (aS : a∈S) (bS : b∈S) (ne : a≠b) (P : V → Prop)
    (part : ∀ x∈S, ∀ y∈S, G.Reachable x y ↔ K.Reachable x y)
    (flags : ∀ x∈S, ComponentFlag G P x ↔ ComponentFlag K P x) :
    (∀ x∈S, ∀ y∈S, (G ⊔ SimpleGraph.edge a b).Reachable x y ↔
      (K ⊔ SimpleGraph.edge a b).Reachable x y) ∧
    (∀ x∈S, ComponentFlag (G ⊔ SimpleGraph.edge a b) P x ↔
      ComponentFlag (K ⊔ SimpleGraph.edge a b) P x) := by
  constructor
  · intro x hx y hy
    simp only [reachable_after_union ne,Merged,part x hx y hy,part x hx a aS,
      part x hx b bS,part a aS y hy,part b bS y hy]
  · intro x hx
    simp only [flag_after_union ne,flags x hx,flags a aS,flags b bS,
      part x hx a aS,part x hx b bS]

end GridGraphs.ResidueTwoUpper.Exceptional.OneGap.FanBoot.SouthCap.Strip
