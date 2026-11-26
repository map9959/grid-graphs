import GridGraphs.ResidueTwoUpper.TwoGapFrontierCut

namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.ExitReplay
open SimpleGraph

variable {V : Type*}

private theorem sup_iff (H : SimpleGraph V) (a b u v : V) (ab : a≠b) :
    (H ⊔ edge a b).Reachable u v ↔ H.Reachable u v ∨
    (H.Reachable u a ∧ H.Reachable b v) ∨ (H.Reachable u b ∧ H.Reachable a v) := by
  have bond : (H ⊔ edge a b).Adj a b := .inr ((edge_adj ..).mpr ⟨.inl ⟨rfl,rfl⟩,ab⟩)
  constructor
  · rintro ⟨w⟩
    induction w with
    | nil => exact .inl .rfl
    | @cons x y z e _ ih =>
      rcases e with h|h
      · rcases ih with h'|⟨h',l⟩|⟨h',l⟩
        · exact .inl (h.reachable.trans h')
        · exact .inr (.inl ⟨h.reachable.trans h',l⟩)
        · exact .inr (.inr ⟨h.reachable.trans h',l⟩)
      · rcases (edge_adj ..).mp h with ⟨⟨rfl,rfl⟩|⟨rfl,rfl⟩,_⟩ <;>
          rcases ih with h|⟨h,l⟩|⟨h,l⟩ <;> first
            | exact .inl l
            | exact .inr (.inl ⟨.rfl,h⟩)
            | exact .inr (.inr ⟨.rfl,h⟩)
            | exact .inr (.inl ⟨.rfl,l⟩)
            | exact .inr (.inr ⟨.rfl,l⟩)
  · rintro (h|⟨h,l⟩|⟨h,l⟩)
    · exact h.mono le_sup_left
    · exact (h.mono le_sup_left).trans (bond.reachable.trans (l.mono le_sup_left))
    · exact (h.mono le_sup_left).trans (bond.symm.reachable.trans (l.mono le_sup_left))

def hits (H : SimpleGraph V) (event : V → Prop) (x : V) := ∃ y, H.Reachable x y ∧ event y

private theorem hits_sup (H : SimpleGraph V) (event : V → Prop) (a b x : V) (ab : a≠b) :
    hits (H ⊔ edge a b) event x ↔ hits H event x ∨
    (H.Reachable x a ∧ hits H event b) ∨ (H.Reachable x b ∧ hits H event a) := by
  unfold hits
  simp_rw [sup_iff H a b _ _ ab]
  grind

/-- Exact physical meaning of the two mutable arrays, also between
insertions of one `advance`. A slot can stand for a whole old component. -/
structure Models (H : SimpleGraph V) (port : Fin n → V) (event : Fin 2 → V → Prop)
    (p t : Array Nat) : Prop where
  lenP : p.size=n
  lenT : t.size=n
  small : ∀ i : Fin n, p[i.val]!<n
  parts : ∀ i j : Fin n, p[i.val]! = p[j.val]! ↔ H.Reachable (port i) (port j)
  tags : ∀ (i : Fin n) (d : Fin 2), (t[p[i.val]!]!).testBit d ↔ hits H (event d) (port i)

/-- One actual `link` cannot reject a fresh physical edge of a forest.
The returned arrays retain *both directions* of reachability and the
exact existential interpretation of each flag, not just label soundness. -/
theorem link_survives {T H : SimpleGraph V} (forest : T.IsAcyclic) (sub : H≤T)
    {port : Fin n → V} {event : Fin 2 → V → Prop} {p t : Array Nat}
    (model : Models H port event p t) (i j : Fin n) (new : T.Adj (port i) (port j))
    (fresh : ¬H.Adj (port i) (port j)) :
    ∃ p' t', link p t i j=some (p',t') ∧
      Models (H ⊔ edge (port i) (port j)) port event p' t' := by
  let a := p[i.val]!
  let b := p[j.val]!
  have dis : ¬H.Reachable (port i) (port j) := by
    intro r
    have ac := forest.anti (sup_le sub ((edge_le_iff T).mpr (.inr new)))
    exact ((isAcyclic_sup_fromEdgeSet_iff.mp ac).2 r).elim new.ne fresh
  have ne : a≠b := fun eq => dis ((model.parts i j).mp eq)
  let p' := p.map fun c => if c=a then b else c
  let t' := t.set! b (t[a]! ||| t[b]!)
  refine ⟨p',t',by simp [link,a,b,ne,p',t'],?_⟩
  have lp := model.lenP
  have lt := model.lenT
  have sm (h : Fin n) := model.small h
  have get (h : Fin n) : p'[h.val]! = if p[h.val]! = a then b else p[h.val]! := by
    have hi : h.val<p.size := lp ▸ h.isLt
    simp [p',getElem!_pos,hi]
  have getT (z : Nat) (hz : z<n) : t'[z]! = if z=b then t[a]! ||| t[b]! else t[z]! := by
    have hb : b<t.size := lt ▸ sm j
    have hi : z<t.size := lt ▸ hz
    by_cases eq : z=b <;> simp [t',Array.set!_eq_setIfInBounds,Array.getElem_setIfInBounds,
      getElem!_pos,hb,hi,eq,Ne.symm]
  refine ⟨by simpa [p'],by simpa [t'],?_,?_,?_⟩
  · intro h; rw [get]; split <;> first | exact sm j | exact sm h
  · intro x y
    rw [get,get,sup_iff _ _ _ _ _ new.ne]
    simp only [←model.parts]
    change (if _=a then b else _)=(if _=a then b else _) ↔ _
    dsimp only [a,b] at *
    split_ifs <;> grind
  · intro x d
    rw [get,getT _ (by split <;> first | exact sm j | exact sm x),hits_sup _ _ _ _ _ new.ne]
    simp only [←model.tags,←model.parts]
    change _ ↔ _ ∨ (_=a ∧ _) ∨ (_=b ∧ _)
    by_cases ha : p[x.val]! = a <;> by_cases hb : p[x.val]! = b <;>
      simp_all [a,b,Nat.testBit_or] <;> tauto

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap.ExitReplay
