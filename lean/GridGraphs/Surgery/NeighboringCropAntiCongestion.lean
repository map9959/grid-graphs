import GridGraphs.Surgery.BundleCycleDefect
import GridGraphs.Surgery.NeighboringCropPersistence

/-!
# Unconditional neighboring-crop anti-congestion facts

The cycle defect is a number, not an indexed cycle basis.  Consequently a
transfer argument must supply an arbitrary index type and retain the physical
edge label of every indexed transfer.  The indexing data below do not prove
that the transfers form a cycle basis or are independent.  This file records
what follows from the existing neighboring-crop seam theorem, and also records
the exact obstruction to forgetting the physical labels.
-/

namespace GridGraphs

open Finset SimpleGraph

private structure List.FirstWitness
    {α : Type*} (p : α → Prop) (l : List α) where
  preceding : List α
  value : α
  following : List α
  eq_support : l = preceding ++ value :: following
  value_property : p value
  preceding_not_property : ∀ z ∈ preceding, ¬p z

private theorem List.nonempty_firstWitness_of_exists_mem
    {α : Type*} {p : α → Prop} [DecidablePred p] {l : List α}
    (h : ∃ a ∈ l, p a) :
    Nonempty (List.FirstWitness p l) := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
      by_cases hx : p x
      · exact ⟨⟨[], x, xs, rfl, hx, by simp⟩⟩
      · obtain ⟨a, ha, hpa⟩ := h
        simp only [List.mem_cons] at ha
        rcases ha with rfl | ha
        · exact (hx hpa).elim
        · obtain ⟨fw⟩ := ih ⟨a, ha, hpa⟩
          exact ⟨⟨x :: fw.preceding, fw.value, fw.following,
            by simp [fw.eq_support], fw.value_property, by
              intro w hw
              simp only [List.mem_cons] at hw
              rcases hw with rfl | hw
              · exact hx
              · exact fw.preceding_not_property w hw⟩⟩

/-- The first seam component on the ordered support of a seam witness.  The
`preceding` field is the precise assertion that this is the first crossing; unlike
the original witness's chosen vertex, it is determined by path order. -/
structure NeighboringCropFirstSeamComponentWitness
    (n : Nat) (first second : FourCropCorner) (hn : 3 ≤ n)
    (F : Set (GridVertex n n))
    (x y : (neighboringCropOverlapEmbedding n first second hn) ⁻¹' F) where
  witness : NeighboringCropSeamComponentWitness n first second hn F x y
  preceding : List ((fourCropEmbedding n first hn) ⁻¹' F)
  firstVertex : (fourCropEmbedding n first hn) ⁻¹' F
  following : List ((fourCropEmbedding n first hn) ⁻¹' F)
  support_eq : witness.path.support = preceding ++ firstVertex :: following
  firstVertex_seam : firstVertex ∈
    neighboringCropFirstSeamSet n first second hn F
  preceding_not_seam : ∀ v ∈ preceding,
    v ∉ neighboringCropFirstSeamSet n first second hn F
  component : (neighboringCropFirstSeamGraph n first second hn F).ConnectedComponent
  component_eq : component =
    (neighboringCropFirstSeamGraph n first second hn F).connectedComponentMk
      ⟨firstVertex, firstVertex_seam⟩

/-- Every seam witness has a first seam component. -/
noncomputable def NeighboringCropSeamComponentWitness.toFirst
    {n : Nat} {first second : FourCropCorner} {hn : 3 ≤ n}
    {F : Set (GridVertex n n)}
    {x y : (neighboringCropOverlapEmbedding n first second hn) ⁻¹' F}
    (w : NeighboringCropSeamComponentWitness n first second hn F x y) :
    NeighboringCropFirstSeamComponentWitness n first second hn F x y := by
  classical
  let fw := Classical.choice (List.nonempty_firstWitness_of_exists_mem
      (p := fun v => v ∈ neighboringCropFirstSeamSet n first second hn F)
      ⟨w.seamVertex, w.seamVertex_mem, w.seamVertex_not_second⟩)
  exact {
    witness := w
    preceding := fw.preceding
    firstVertex := fw.value
    following := fw.following
    support_eq := fw.eq_support
    firstVertex_seam := fw.value_property
    preceding_not_seam := fw.preceding_not_property
    component :=
      (neighboringCropFirstSeamGraph n first second hn F).connectedComponentMk
        ⟨fw.value, fw.value_property⟩
    component_eq := rfl }

/-- An arbitrarily indexed family of failed connectivity transfers between two
crops, together with an ambient physical edge label for each index.  Merely
supplying `Index` asserts neither cycle-basis representation nor independence. -/
structure NeighboringCropBundleTransferFamily
    (n : Nat) (first second : FourCropCorner) (hn : 3 ≤ n)
    (F : Set (GridVertex n n)) (Index : Type*) where
  source : Index →
    (neighboringCropOverlapEmbedding n first second hn) ⁻¹' F
  target : Index →
    (neighboringCropOverlapEmbedding n first second hn) ⁻¹' F
  physicalBundleLabel : Index → GridEdge n n
  connectedInFirst : ∀ b,
    (cornerCropInducedForcedGraph n first hn F).Reachable
      (neighboringCropOverlapToFirstHom n first second hn F (source b))
      (neighboringCropOverlapToFirstHom n first second hn F (target b))
  disconnectedInSecond : ∀ b, ¬
    (cornerCropInducedForcedGraph n second hn F).Reachable
      (neighboringCropOverlapToSecondHom n first second hn F (source b))
      (neighboringCropOverlapToSecondHom n first second hn F (target b))

namespace NeighboringCropBundleTransferFamily

/-- The canonical first seam witness for one indexed transfer.  Path
uniqueness is inherited from `NeighboringCropSeamComponentWitness`. -/
noncomputable def firstSeamWitness
    {n : Nat} {first second : FourCropCorner} {hn : 3 ≤ n}
    {F : Set (GridVertex n n)} {Index : Type*}
    (family : NeighboringCropBundleTransferFamily n first second hn F Index)
    (hforest : (cornerCropInducedForcedGraph n first hn F).IsAcyclic)
    (b : Index) : NeighboringCropFirstSeamComponentWitness n first second hn F
      (family.source b) (family.target b) := by
  classical
  have hw : Nonempty (NeighboringCropSeamComponentWitness n first second hn F
      (family.source b) (family.target b)) := by
    rcases neighboringCrop_connectivity_reflects_or_seamComponent
        n first second hn F hforest (family.source b) (family.target b)
        (family.connectedInFirst b) with hsecond | hw
    · exact (family.disconnectedInSecond b hsecond).elim
    · exact hw
  exact (Classical.choice hw).toFirst

/-- The resource label keeps both physical bundle identity and first seam
component. -/
noncomputable def firstSeamLabel
    {n : Nat} {first second : FourCropCorner} {hn : 3 ≤ n}
    {F : Set (GridVertex n n)} {Index : Type*}
    (family : NeighboringCropBundleTransferFamily n first second hn F Index)
    (hforest : (cornerCropInducedForcedGraph n first hn F).IsAcyclic) :
    Index → GridEdge n n ×
      (neighboringCropFirstSeamGraph n first second hn F).ConnectedComponent :=
  fun b => (family.physicalBundleLabel b,
    (family.firstSeamWitness hforest b).component)

/-- Distinct physical bundle labels make the first-seam resource map
injective, even when several paths enter the same seam component. -/
theorem firstSeamLabel_injective
    {n : Nat} {first second : FourCropCorner} {hn : 3 ≤ n}
    {F : Set (GridVertex n n)} {Index : Type*}
    (family : NeighboringCropBundleTransferFamily n first second hn F Index)
    (hforest : (cornerCropInducedForcedGraph n first hn F).IsAcyclic)
    (hphysical : Function.Injective family.physicalBundleLabel) :
    Function.Injective (family.firstSeamLabel hforest) := by
  intro a b hab
  apply hphysical
  exact congrArg Prod.fst hab

/-- Cardinal representation only: the index type has the same cardinality as
the contracted-star defect at `owner`.  This predicate does not identify its
indices with cycles and does not assert linear or graphic independence. -/
def RepresentsBundleCycleDefectCardinality
    {n : Nat} {first second : FourCropCorner} {hn : 3 ≤ n}
    {F : Set (GridVertex n n)} {Index : Type*} [Fintype Index]
    (_family : NeighboringCropBundleTransferFamily n first second hn F Index)
    (owner : GridVertex (n - 3) (n - 3)) : Prop :=
  Fintype.card Index = bundleCycleDefect
    (gridGraph (n - 3) (n - 3)) ((fourCropEmbedding n first hn) ⁻¹' F) owner

/-- Assign an available labelled first-seam witness to an actual free slot. -/
noncomputable def firstSeamFreeSlot
    {n : Nat} {first second : FourCropCorner} {hn : 3 ≤ n}
    {F : Set (GridVertex n n)} {Index : Type*}
    (family : NeighboringCropBundleTransferFamily n first second hn F Index)
    (hforest : (cornerCropInducedForcedGraph n first hn F).IsAcyclic)
    (slotOf : GridEdge n n ×
      (neighboringCropFirstSeamGraph n first second hn F).ConnectedComponent →
        FourCropFreeSlot n) : Index → FourCropFreeSlot n :=
  fun b => slotOf (family.firstSeamLabel hforest b)

/-- An explicit assignment of physical bundle labels to the `6n` free slots
turns the seam witnesses into a genuine slot injection.  This is precisely the
extra resource required by `FourCropSurgery`; seam components alone do not
construct this assignment. -/
theorem firstSeam_freeSlot_injective
    {n : Nat} {first second : FourCropCorner} {hn : 3 ≤ n}
    {F : Set (GridVertex n n)} {Index : Type*}
    (family : NeighboringCropBundleTransferFamily n first second hn F Index)
    (hforest : (cornerCropInducedForcedGraph n first hn F).IsAcyclic)
    (slotOf : GridEdge n n ×
      (neighboringCropFirstSeamGraph n first second hn F).ConnectedComponent →
        FourCropFreeSlot n)
    (hphysical : Function.Injective family.physicalBundleLabel)
    (hslot : Set.InjOn slotOf (Set.range (family.firstSeamLabel hforest))) :
    Function.Injective (family.firstSeamFreeSlot hforest slotOf) := by
  intro a b hab
  apply family.firstSeamLabel_injective hforest hphysical
  exact hslot ⟨a, rfl⟩ ⟨b, rfl⟩ hab

/-- Therefore an explicitly slotted finite transfer family has at most `6n`
elements. -/
theorem card_index_le_six_mul
    {n : Nat} {first second : FourCropCorner} {hn : 3 ≤ n}
    {F : Set (GridVertex n n)} {Index : Type*} [Fintype Index]
    (family : NeighboringCropBundleTransferFamily n first second hn F Index)
    (hforest : (cornerCropInducedForcedGraph n first hn F).IsAcyclic)
    (slotOf : GridEdge n n ×
      (neighboringCropFirstSeamGraph n first second hn F).ConnectedComponent →
        FourCropFreeSlot n)
    (hphysical : Function.Injective family.physicalBundleLabel)
    (hslot : Set.InjOn slotOf (Set.range (family.firstSeamLabel hforest))) :
    Fintype.card Index ≤ 6 * n := by
  have hcard := Fintype.card_le_of_injective
    (family.firstSeamFreeSlot hforest slotOf)
    (family.firstSeam_freeSlot_injective hforest slotOf hphysical hslot)
  rw [card_fourCropFreeSlot] at hcard
  omega

/-- Equality between the index cardinality and the defect, plus an explicit
free-slot assignment, bounds the bundle-cycle defect by the available `6n`
slots. -/
theorem bundleCycleDefect_le_six_mul_of_firstSeamSlots
    {n : Nat} {first second : FourCropCorner} {hn : 3 ≤ n}
    {F : Set (GridVertex n n)} {Index : Type*} [Fintype Index]
    (family : NeighboringCropBundleTransferFamily n first second hn F Index)
    (owner : GridVertex (n - 3) (n - 3))
    (hrepresents : family.RepresentsBundleCycleDefectCardinality owner)
    (hforest : (cornerCropInducedForcedGraph n first hn F).IsAcyclic)
    (slotOf : GridEdge n n ×
      (neighboringCropFirstSeamGraph n first second hn F).ConnectedComponent →
        FourCropFreeSlot n)
    (hphysical : Function.Injective family.physicalBundleLabel)
    (hslot : Set.InjOn slotOf (Set.range (family.firstSeamLabel hforest))) :
    bundleCycleDefect (gridGraph (n - 3) (n - 3))
      ((fourCropEmbedding n first hn) ⁻¹' F) owner ≤ 6 * n := by
  rw [← hrepresents]
  exact family.card_index_le_six_mul hforest slotOf hphysical hslot

end NeighboringCropBundleTransferFamily

/-! ## Sharp symbolic obstruction -/

/-- Two distinct symbolic transfer labels can use one seam component. -/
abbrev TwoTransferLabels := Fin 2

def twoBundlePhysicalLabel : TwoTransferLabels → Fin 2 := id

def twoBundleSeamComponent : TwoTransferLabels → Unit := fun _ => ()

theorem twoBundlePhysicalLabel_injective :
    Function.Injective twoBundlePhysicalLabel := by
  intro a b hab
  exact hab

/-- Forest-path uniqueness cannot imply component injectivity: two distinct
indexed transfers may have the same unique path and hence the same first
component. -/
theorem twoBundleSeamComponent_not_injective :
    ¬Function.Injective twoBundleSeamComponent := by
  intro h
  have heq : (0 : Fin 2) = 1 := h rfl
  omega

/-- Retaining the distinct physical label repairs the symbolic collision. -/
theorem twoBundleLabelledSeam_injective :
    Function.Injective
      (fun b : TwoTransferLabels => (twoBundlePhysicalLabel b,
        twoBundleSeamComponent b)) := by
  intro a b hab
  exact congrArg Prod.fst hab

end GridGraphs
