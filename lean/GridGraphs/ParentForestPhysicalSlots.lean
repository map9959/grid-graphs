import GridGraphs.PlaneChannelForest

/-!
# Physical children for parent-forest merger slots

If every parent has at most one nonphysical child, its `k - 1` units of branch
excess can be assigned injectively to physical children.  Since a child has a
unique parent, these local assignments combine into one global embedding.
-/

namespace GridGraphs

open Finset

namespace ParentForest

variable {V : Type*} [Fintype V] [DecidableEq V]

def physicalChildren (F : ParentForest V) (physical : V → Prop)
    [DecidablePred physical] (v : V) : Finset V :=
  (F.children v).filter physical

def nonphysicalChildren (F : ParentForest V) (physical : V → Prop)
    [DecidablePred physical] (v : V) : Finset V :=
  (F.children v).filter fun x => ¬physical x

theorem mergerExcessAt_le_card_physicalChildren
    (F : ParentForest V) (physical : V → Prop) [DecidablePred physical]
    (hghost : ∀ v, (F.nonphysicalChildren physical v).card ≤ 1)
    (v : V) :
    F.mergerExcessAt v ≤ (F.physicalChildren physical v).card := by
  have hpartition :=
    (F.children v).filter_card_add_filter_neg_card_eq_card physical
  change (F.children v).card - 1 ≤ ((F.children v).filter physical).card
  have hnonphysical := hghost v
  change ((F.children v).filter fun x => ¬physical x).card ≤ 1 at hnonphysical
  omega

noncomputable def localMergerSlotPhysicalChildEmbedding
    (F : ParentForest V) (physical : V → Prop) [DecidablePred physical]
    (hghost : ∀ v, (F.nonphysicalChildren physical v).card ≤ 1)
    (v : V) :
    Fin (F.mergerExcessAt v) ↪ ↥(F.physicalChildren physical v) := by
  classical
  apply Classical.choice
  rw [Function.Embedding.nonempty_iff_card_le, Fintype.card_fin,
    Fintype.card_coe]
  exact F.mergerExcessAt_le_card_physicalChildren physical hghost v

/-- Globally assign every merger-excess slot to a distinct physical child. -/
noncomputable def mergerSlotPhysicalChildEmbedding
    (F : ParentForest V) (physical : V → Prop) [DecidablePred physical]
    (hghost : ∀ v, (F.nonphysicalChildren physical v).card ≤ 1) :
    F.MergerSlot ↪ {x : V // physical x} where
  toFun s :=
    let child := F.localMergerSlotPhysicalChildEmbedding physical hghost s.1 s.2
    ⟨child.1, (Finset.mem_filter.mp child.2).2⟩
  inj' := by
    classical
    rintro ⟨v, i⟩ ⟨w, j⟩ hij
    let ei := F.localMergerSlotPhysicalChildEmbedding physical hghost v
    let ej := F.localMergerSlotPhysicalChildEmbedding physical hghost w
    have hchild : (ei i).1 = (ej j).1 := congrArg Subtype.val hij
    have hiv := (Finset.mem_filter.mp (ei i).2).1
    have hjw := (Finset.mem_filter.mp (ej j).2).1
    have hvw : v = w := by
      rw [ParentForest.children, Finset.mem_filter] at hiv hjw
      exact Option.some.inj (hiv.2.symm.trans (hchild ▸ hjw.2))
    subst w
    have hijLocal : i = j := ei.injective (Subtype.ext hchild)
    subst j
    rfl

end ParentForest

end GridGraphs
