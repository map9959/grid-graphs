import GridGraphs.PlaneChannelForest
import GridGraphs.LocalizedHallRouting

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
    (F.children v).card_filter_add_card_filter_not physical
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

/-! ## Collision-transparent resource assignment -/

/-- Resource selected by a local merger slot after selecting its physical
child.  This definition does not assert that two selected children have
different resources. -/
noncomputable def localMergerSlotResource
    (F : ParentForest V) (physical : V → Prop) [DecidablePred physical]
    (hghost : ∀ v, (F.nonphysicalChildren physical v).card ≤ 1)
    {R : Type*} (resource : {x : V // physical x} → R) (v : V) :
    Fin (F.mergerExcessAt v) → R := fun i =>
  resource ⟨(F.localMergerSlotPhysicalChildEmbedding physical hghost v i).1,
    (Finset.mem_filter.mp
      (F.localMergerSlotPhysicalChildEmbedding physical hghost v i).2).2⟩

/-- Exact local obstruction: slot resources are injective precisely when the
resource labels do not collide on the selected `q - 1` children. -/
theorem localMergerSlotResource_injective_iff
    (F : ParentForest V) (physical : V → Prop) [DecidablePred physical]
    (hghost : ∀ v, (F.nonphysicalChildren physical v).card ≤ 1)
    {R : Type*} (resource : {x : V // physical x} → R) (v : V) :
    Function.Injective (F.localMergerSlotResource physical hghost resource v) ↔
      ∀ i j, F.localMergerSlotResource physical hghost resource v i =
        F.localMergerSlotResource physical hghost resource v j → i = j :=
  Iff.rfl

/-- Globally selected raw resource.  Parent uniqueness already prevents a
selected child from belonging to two local branch fibers; the remaining issue
is equality of the raw labels supplied by `resource`. -/
noncomputable def mergerSlotResource
    (F : ParentForest V) (physical : V → Prop) [DecidablePred physical]
    (hghost : ∀ v, (F.nonphysicalChildren physical v).card ≤ 1)
    {R : Type*} (resource : {x : V // physical x} → R) : F.MergerSlot → R :=
  resource ∘ F.mergerSlotPhysicalChildEmbedding physical hghost

/-- Local injectivity is not enough across different branch vertices.  This
constructor records the exact global collision hypothesis and makes no Hall or
freshness assumption. -/
noncomputable def mergerSlotResourceEmbedding
    (F : ParentForest V) (physical : V → Prop) [DecidablePred physical]
    (hghost : ∀ v, (F.nonphysicalChildren physical v).card ≤ 1)
    {R : Type*} (resource : {x : V // physical x} → R)
    (hcollision : ∀ a b : F.MergerSlot,
      F.mergerSlotResource physical hghost resource a =
        F.mergerSlotResource physical hghost resource b → a = b) :
    F.MergerSlot ↪ R where
  toFun := F.mergerSlotResource physical hghost resource
  inj' := hcollision

/-- A globally injective child-resource label is a sufficient, stronger way to
discharge all local and cross-cell collisions. -/
noncomputable def mergerSlotResourceEmbeddingOfInjective
    (F : ParentForest V) (physical : V → Prop) [DecidablePred physical]
    (hghost : ∀ v, (F.nonphysicalChildren physical v).card ≤ 1)
    {R : Type*} (resource : {x : V // physical x} → R)
    (hresource : Function.Injective resource) : F.MergerSlot ↪ R :=
  (F.mergerSlotPhysicalChildEmbedding physical hghost).trans
    ⟨resource, hresource⟩

/-! ## Exact localized raw-resource obstruction -/

/-- A collision-free raw-resource assignment chooses one allowed resource for
each merger slot and is globally injective.  Candidate neighborhoods may depend
on the chosen parent tie-breaking; no cardinal or waste hypothesis is built in. -/
def MergerSlotRawResourceCollisionFree (F : ParentForest V)
    {R : Type*} [DecidableEq R] (candidates : F.MergerSlot → Finset R) : Prop :=
  ∃ resource : F.MergerSlot → R, Function.Injective resource ∧
    ∀ slot, resource slot ∈ candidates slot

/-- Finite Hall is the exact obstruction to a collision-free selection from
localized branch-resource neighborhoods. -/
theorem mergerSlotRawResourceCollisionFree_iff_localizedHall
    (F : ParentForest V) {R : Type*} [DecidableEq R]
    (candidates : F.MergerSlot → Finset R) :
    MergerSlotRawResourceCollisionFree F candidates ↔ LocalizedHall candidates := by
  rw [localizedHall_iff_exists_embedding]
  constructor
  · rintro ⟨resource, hinjective, hmem⟩
    exact ⟨⟨resource, hinjective⟩, hmem⟩
  · rintro ⟨resource, hmem⟩
    exact ⟨resource, resource.injective, hmem⟩

/-- Exact parent-choice form: some tie-breaking has a collision-free localized
raw-resource assignment iff some tie-breaking satisfies its localized Hall
inequalities. -/
theorem exists_mergerSlotRawResourceCollisionFree_iff_exists_localizedHall
    {Choice : Type*} (forest : Choice → ParentForest V)
    {R : Type*} [DecidableEq R]
    (candidates : ∀ choice, (forest choice).MergerSlot → Finset R) :
    (∃ choice, MergerSlotRawResourceCollisionFree
      (forest choice) (candidates choice)) ↔
      ∃ choice, LocalizedHall (candidates choice) := by
  constructor <;> rintro ⟨choice, hchoice⟩ <;> refine ⟨choice, ?_⟩
  · exact ((forest choice).mergerSlotRawResourceCollisionFree_iff_localizedHall
      (candidates choice)).mp hchoice
  · exact ((forest choice).mergerSlotRawResourceCollisionFree_iff_localizedHall
      (candidates choice)).mpr hchoice

end ParentForest

end GridGraphs
