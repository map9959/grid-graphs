import GridGraphs.ResidueTwoUpper.TwoGapCrop

namespace GridGraphs.ResidueTwoUpper.Exceptional.TwoGap
open SimpleGraph Finset
variable {V : Type*}

/-- Reuse an isolated vertex of the crop as the common root. Pin only
the listed anchors; thus the lemma also applies to partially built strips. -/
def pinned (G : SimpleGraph V) (r : V) (s : Finset V) :=
  G ⊔ ⨆ x ∈ s, edge r x

private theorem pin_cut {G : SimpleGraph V} {r a : V} {s : Finset V}
    (hr : ¬G.Reachable a r) (hs : ∀ v∈s, ¬G.Reachable a v) :
    ¬(pinned G r s).Reachable a r := by
  classical
  rintro ⟨p⟩
  have extend {b c : V} (q : (pinned G r s).Walk b c) :
      G.Reachable a b → G.Reachable a c := by
    induction q with
    | nil => exact id
    | @cons x y z e tail ih =>
      intro hx
      apply ih
      rcases e with ge|added
      · exact hx.trans ge.reachable
      · simp only [iSup_adj,edge_adj] at added
        obtain ⟨v,hv,h⟩ := added
        rcases h with ⟨h,_⟩|⟨h,_⟩ <;> subst x <;> first | exact (hr hx).elim | exact (hs v hv hx).elim
  exact hr (extend p .rfl)

theorem pinned_forest {G : SimpleGraph V} (acy : G.IsAcyclic) (r : V) (s : Finset V)
    (away : ∀ x∈s, ¬G.Reachable x r)
    (sep : ∀ x∈s, ∀ y∈s, G.Reachable x y → x=y) : (pinned G r s).IsAcyclic := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa [pinned] using acy
  | @insert a s fresh ih =>
    have inside {x} (h : x∈s) : x∈insert a s := mem_insert_of_mem h
    have atA := mem_insert_self a s
    have prev := ih (fun x hx => away x (inside hx)) (fun x hx y hy => sep x (inside hx) y (inside hy))
    have dis := pin_cut (away a atA) (s:=s) (fun v hv c => fresh (sep a atA v (inside hv) c ▸ hv))
    have add := prev.sup_edge_of_not_reachable (fun c => dis c.symm)
    simpa only [pinned,Finset.iSup_insert,sup_assoc,sup_comm,sup_left_comm] using add

theorem physical_pins {G : SimpleGraph V} (acy : G.IsAcyclic) (rim : V → Prop) (r : V)
    (bd : rim r) (P : V → V) (arr : ∀ a b, G.Adj a b → (P a=b ↔ P b≠a))
    (s : Finset V) (pins : ∀ a∈s, anchor rim P a) :
    (pinned (crop G rim) r s).IsAcyclic := by
  apply pinned_forest (acy.anti (show crop G rim≤G from fun _ _ h => h.1))
  · intro x hx c
    obtain ⟨p⟩ := c.symm
    cases p with
    | nil => exact (pins _ hx).1 bd
    | cons e _ => exact e.2.1 bd
  · intro a ha b hb; exact unique_anchor arr (pins a ha) (pins b hb)

end GridGraphs.ResidueTwoUpper.Exceptional.TwoGap
