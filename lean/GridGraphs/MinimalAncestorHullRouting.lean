import GridGraphs.OccurrenceLabelledCotreeDualForest
import GridGraphs.ParentForestAncestorHull
import GridGraphs.ParentForestPhysicalSlots
import GridGraphs.GridBoundaryNonalternation
import GridGraphs.TerminalCarrierQuotientRouting

/-!
# Merger routing in a minimal active ancestor hull

Branch excess relevant to selected starts belongs to their parent-ancestor
closure, not to the whole ambient forest.  This module constructs that hull and
gives its merger slots local neighborhoods labelled by the first separating
cell, edge, or component.  The general obstruction is exactly Hall.  An
injective first-separator labelling gives an unconditional routing.

Component nonalternation alone is weaker: repeated contacts with one component
are nonalternating but can still have a deficient Hall neighborhood.
-/

namespace GridGraphs

open Finset SimpleGraph

namespace SplitOccurrenceCotreeDualCore.ParentTieBreaking

variable {m n : Nat} {T : SimpleGraph (GridVertex m n)} [DecidableRel T.Adj]
  {O Start : Type*} [Fintype O] [DecidableEq O]
  [Fintype Start] [DecidableEq Start]
  {transition : O → LabelledCotreeTransition T}

/-- Minimal active ancestor hull for a particular geometric parent
tie-breaking.  Changing the tie-breaking changes only the active paths and
their reconvergences, not the ambient occurrence graph. -/
noncomputable def minimalActiveHull
    (choice : SplitOccurrenceCotreeDualCore.ParentTieBreaking transition)
    (start : Start ↪ ↥(choice.forest).leaves) :
    ParentForest ((choice.forest).AncestorHull start) :=
  (choice.forest).ancestorHullForest start

end SplitOccurrenceCotreeDualCore.ParentTieBreaking

/-- Raw local resource exposed at the first separation of two active branches. -/
abbrev FirstSeparatingResource (Cell Edge Component : Type*) :=
  Cell ⊕ Edge ⊕ Component

namespace ParentForest

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Candidate neighborhood obtained from the first separating resource of the
physical child selected for this local excess slot. -/
noncomputable def firstSeparatingNeighborhood
    (F : ParentForest V) (physical : V → Prop) [DecidablePred physical]
    (hghost : ∀ v, (F.nonphysicalChildren physical v).card ≤ 1)
    {Cell Edge Component : Type*}
    [DecidableEq Cell] [DecidableEq Edge] [DecidableEq Component]
    (firstSeparating : {x : V // physical x} →
      FirstSeparatingResource Cell Edge Component)
    (slot : F.MergerSlot) :
    Finset (FirstSeparatingResource Cell Edge Component) :=
  {firstSeparating (F.mergerSlotPhysicalChildEmbedding physical hghost slot)}

/-- For first-separator neighborhoods in the active hull, collision-free
matching is exactly the finite Hall condition. -/
theorem firstSeparatingCollisionFree_iff_localizedHall
    (F : ParentForest V) (physical : V → Prop) [DecidablePred physical]
    (hghost : ∀ v, (F.nonphysicalChildren physical v).card ≤ 1)
    {Cell Edge Component : Type*}
    [DecidableEq Cell] [DecidableEq Edge] [DecidableEq Component]
    (firstSeparating : {x : V // physical x} →
      FirstSeparatingResource Cell Edge Component) :
    F.MergerSlotRawResourceCollisionFree
        (F.firstSeparatingNeighborhood physical hghost firstSeparating) ↔
      LocalizedHall
        (F.firstSeparatingNeighborhood physical hghost firstSeparating) :=
  F.mergerSlotRawResourceCollisionFree_iff_localizedHall _

/-- If distinct physical branches have distinct first separating resources,
the active branch excess has an unconditional collision-free injection. -/
noncomputable def firstSeparatingResourceEmbedding
    (F : ParentForest V) (physical : V → Prop) [DecidablePred physical]
    (hghost : ∀ v, (F.nonphysicalChildren physical v).card ≤ 1)
    {Cell Edge Component : Type*}
    [DecidableEq Cell] [DecidableEq Edge] [DecidableEq Component]
    (firstSeparating : {x : V // physical x} →
      FirstSeparatingResource Cell Edge Component)
    (hinjective : Function.Injective firstSeparating) :
    F.MergerSlot ↪ FirstSeparatingResource Cell Edge Component :=
  F.mergerSlotResourceEmbeddingOfInjective physical hghost
    firstSeparating hinjective

/-- The unconditional injection chooses a member of each corresponding local
first-separator neighborhood. -/
theorem firstSeparatingResourceEmbedding_mem_neighborhood
    (F : ParentForest V) (physical : V → Prop) [DecidablePred physical]
    (hghost : ∀ v, (F.nonphysicalChildren physical v).card ≤ 1)
    {Cell Edge Component : Type*}
    [DecidableEq Cell] [DecidableEq Edge] [DecidableEq Component]
    (firstSeparating : {x : V // physical x} →
      FirstSeparatingResource Cell Edge Component)
    (hinjective : Function.Injective firstSeparating)
    (slot : F.MergerSlot) :
    F.firstSeparatingResourceEmbedding physical hghost firstSeparating
        hinjective slot ∈
      F.firstSeparatingNeighborhood physical hghost firstSeparating slot := by
  simp [firstSeparatingResourceEmbedding, firstSeparatingNeighborhood,
    mergerSlotResourceEmbeddingOfInjective]

/-- Injective first separators therefore prove Hall without a separate
cardinality argument. -/
theorem localizedHall_firstSeparatingNeighborhood_of_injective
    (F : ParentForest V) (physical : V → Prop) [DecidablePred physical]
    (hghost : ∀ v, (F.nonphysicalChildren physical v).card ≤ 1)
    {Cell Edge Component : Type*}
    [DecidableEq Cell] [DecidableEq Edge] [DecidableEq Component]
    (firstSeparating : {x : V // physical x} →
      FirstSeparatingResource Cell Edge Component)
    (hinjective : Function.Injective firstSeparating) :
    LocalizedHall
      (F.firstSeparatingNeighborhood physical hghost firstSeparating) := by
  rw [localizedHall_iff_exists_embedding]
  exact ⟨F.firstSeparatingResourceEmbedding physical hghost firstSeparating
    hinjective, F.firstSeparatingResourceEmbedding_mem_neighborhood physical
      hghost firstSeparating hinjective⟩

end ParentForest

/-! ## Nonalternation is not a capacity theorem -/

/-- Two demands can contact the same single component.  Their component labels
are nonalternating, but their common singleton neighborhood violates Hall. -/
theorem componentNonalternation_not_sufficient_for_collisionFreeMatching :
    ComponentLabelsNonalternating (⊤ : SimpleGraph Unit) () () () () ∧
      ¬LocalizedHall (fun _ : Fin 2 => ({()} : Finset Unit)) := by
  constructor
  · intro C D ha _ hb _
    exact ConnectedComponent.eq_of_common_vertex ha hb
  · intro hHall
    have h := hHall (Finset.univ : Finset (Fin 2))
    have heq : (Finset.univ : Finset (Fin 2)).biUnion
        (fun _ : Fin 2 => ({()} : Finset Unit)) = {()} := by
      ext x
      simp
    rw [heq] at h
    simp at h

/-! ## Representative-component permutation obstruction -/

/-- Minimal two-root forest used to isolate the representative-component
obstruction.  Both roots are active hull roots. -/
def representativePermutationForest : ParentForest (Fin 2) where
  parent := fun _ => none
  rank := fun _ => 0
  rank_parent := by simp

def representativePermutationRootPort :
    ↥representativePermutationForest.roots → Fin 2 := fun root => root.1

def representativePermutationRootComponent :
    ↥representativePermutationForest.roots → Fin 2 := fun root => root.1

/-- Prescribe the opposite contour-ranked component at each used port. -/
def representativePermutationReservedComponent :
    CarrierQuotient representativePermutationRootPort → Fin 2 := fun q =>
  if (carrierQuotientEmbedding representativePermutationRootPort q).1 = 0
    then 1 else 0

/-- The exact nonalternating counterconfiguration is `C@p,D@q` for active
roots and `D@p,C@q` for ranked reservations.  Both port fibers are exceptions.
Thus contour nonalternation, which permits contiguous blocks `C,C,D,D`, does
not determine the matching between component representatives and active-root
ports. -/
theorem representativePermutationException_exact :
    ComponentLabelsNonalternating (⊤ : SimpleGraph (Fin 2)) 0 0 1 1 ∧
      ∀ q : CarrierQuotient representativePermutationRootPort,
        (⟨q, by
          intro root hroot
          have hport : root.1 = carrierQuotientEmbedding
              representativePermutationRootPort q := by
            have h := congrArg
              (carrierQuotientEmbedding representativePermutationRootPort) hroot
            simpa only [carrierQuotientEmbedding_mk,
              representativePermutationRootPort] using h
          change root.1 ≠ (if (carrierQuotientEmbedding
            representativePermutationRootPort q).1 = 0 then 1 else 0)
          rw [hport]
          split_ifs with hzero <;> omega⟩ : RootPortRepresentativeException
            representativePermutationForest representativePermutationRootPort
            representativePermutationRootComponent
            representativePermutationReservedComponent).1 = q := by
  constructor
  · intro C D h0 _ h1 _
    exact ConnectedComponent.eq_of_common_vertex h0 h1
  · intro q
    rfl

end GridGraphs
