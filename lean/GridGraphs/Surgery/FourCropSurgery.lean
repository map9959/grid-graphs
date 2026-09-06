import GridGraphs.Surgery.CyclicCropBoundarySignature
import GridGraphs.Surgery.ThreeFrameSurgery

/-!
# Four-crop surgery bookkeeping

This file records bookkeeping shared by the four corner crops.  The current
concrete implication selects the north-west crop and, when it is active, uses
a supplied bundle-preserving injection argument for that crop.  It neither
constructs such an argument nor proves that some crop has one, and it makes no
comparison among the four crops.
-/

namespace GridGraphs

open Finset SimpleGraph

/-- The four `(n - 3) x (n - 3)` crops anchored at corners of the large grid. -/
inductive FourCropCorner
  | northWest
  | northEast
  | southWest
  | southEast
  deriving DecidableEq

namespace FourCropCorner

instance : Fintype FourCropCorner :=
  ⟨{northWest, northEast, southWest, southEast}, by intro x; cases x <;> simp⟩

def top : FourCropCorner → Nat
  | northWest | northEast => 0
  | southWest | southEast => 3

def bottom : FourCropCorner → Nat
  | northWest | northEast => 3
  | southWest | southEast => 0

def left : FourCropCorner → Nat
  | northWest | southWest => 0
  | northEast | southEast => 3

def right : FourCropCorner → Nat
  | northWest | southWest => 3
  | northEast | southEast => 0

@[simp] theorem top_add_bottom (c : FourCropCorner) : c.top + c.bottom = 3 := by
  cases c <;> rfl

@[simp] theorem left_add_right (c : FourCropCorner) : c.left + c.right = 3 := by
  cases c <;> rfl

end FourCropCorner

/-- The total-three crop embedding associated to a corner. -/
def fourCropEmbedding (n : Nat) (c : FourCropCorner) (hn : 3 ≤ n) :
    GridVertex (n - 3) (n - 3) ↪ GridVertex n n :=
  threeSideCropEmbedding n c.top c.bottom c.left c.right hn
    c.top_add_bottom c.left_add_right

/-- Forced vertices deleted by one of the four corner crops. -/
def fourCropLostVertices (n : Nat) (c : FourCropCorner) (hn : 3 ≤ n)
    (F : Finset (GridVertex n n)) : Finset (GridVertex n n) :=
  F \ Finset.univ.image (fourCropEmbedding n c hn)

/-- Frame loss specialized to a corner crop. -/
def fourCropFrameLoss (n : Nat) (c : FourCropCorner) (hn : 3 ≤ n)
    (F : Finset (GridVertex n n)) : Nat :=
  cropFrameLoss (fourCropEmbedding n c hn) F

/-- A crop is active exactly when its frame loss exceeds the `2n` allowance. -/
def FourCropActive (n : Nat) (c : FourCropCorner) (hn : 3 ≤ n)
    (F : Finset (GridVertex n n)) : Prop :=
  2 * n < fourCropFrameLoss n c hn F

theorem card_fourCropLostVertices (n : Nat) (c : FourCropCorner) (hn : 3 ≤ n)
    (F : Finset (GridVertex n n)) :
    (fourCropLostVertices n c hn F).card = fourCropFrameLoss n c hn F := by
  classical
  let e := fourCropEmbedding n c hn
  have himage : Finset.image e (cropForcedSet e F) =
      F ∩ Finset.image e Finset.univ := by
    ext v
    constructor
    · intro hv
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
      exact Finset.mem_inter.mpr
        ⟨(mem_cropForcedSet e F u).mp hu, Finset.mem_image.mpr ⟨u, by simp, rfl⟩⟩
    · intro hv
      have hv' := Finset.mem_inter.mp hv
      obtain ⟨u, -, huv⟩ := Finset.mem_image.mp hv'.2
      have hvF := hv'.1
      subst v
      exact Finset.mem_image.mpr ⟨u, (mem_cropForcedSet e F u).mpr hvF, rfl⟩
  have hcrop : (cropForcedSet e F).card =
      (F ∩ Finset.image e Finset.univ).card := by
    rw [← himage, Finset.card_image_of_injective _ e.injective]
  rw [fourCropLostVertices, fourCropFrameLoss, cropFrameLoss,
    Finset.card_sdiff, hcrop]
  rw [Finset.inter_comm]

/-- The canonical cyclic signature for a four-corner crop. -/
abbrev FourCropBoundarySignature (n : Nat) (hn : 5 ≤ n)
    (c : FourCropCorner) (F : Finset (GridVertex n n)) :=
  CyclicCropBoundarySignature c.top c.left
    (show c.top + (n - 3) ≤ n by cases c <;> simp [FourCropCorner.top] <;> omega)
    (show c.left + (n - 3) ≤ n by cases c <;> simp [FourCropCorner.left] <;> omega)
    (show 2 ≤ n - 3 by omega) (show 2 ≤ n - 3 by omega) F

/-- The repair vertices present after the first `k` choices. -/
def fourCropRepairPrefix {n : Nat}
    (order : List (GridVertex (n - 3) (n - 3))) (k : Nat) :
    Finset (GridVertex (n - 3) (n - 3)) :=
  (order.take k).toFinset

/-- Canonical signature state after an ordered repair prefix. -/
noncomputable def fourCropRepairPrefixSignature (n : Nat) (hn : 5 ≤ n)
    (c : FourCropCorner) (F : Finset (GridVertex n n))
    (order : List (GridVertex (n - 3) (n - 3))) (k : Nat) :
    FourCropBoundarySignature n hn c F :=
  canonicalCyclicCropBoundarySignature c.top c.left
    (show c.top + (n - 3) ≤ n by cases c <;> simp [FourCropCorner.top] <;> omega)
    (show c.left + (n - 3) ≤ n by cases c <;> simp [FourCropCorner.left] <;> omega)
    (show 2 ≤ n - 3 by omega) (show 2 ≤ n - 3 by omega)
    F (fourCropRepairPrefix order k)

/-- Ordered repair data whose canonical signature is admissible at every
prefix.  This records bundle independence rather than deriving it from the
cyclic boundary word. -/
structure FourCropOrderedRepairState (n : Nat) (hn : 5 ≤ n)
    (c : FourCropCorner) (F : Finset (GridVertex n n)) where
  order : List (GridVertex (n - 3) (n - 3))
  nodup : order.Nodup
  prefixSignatureAdmissible : ∀ k ≤ order.length,
    (fourCropRepairPrefixSignature n hn c F order k).RepairAdmissible

namespace FourCropOrderedRepairState

def repairSet {n : Nat} {hn : 5 ≤ n} {c : FourCropCorner}
    {F : Finset (GridVertex n n)}
    (state : FourCropOrderedRepairState n hn c F) :
    Finset (GridVertex (n - 3) (n - 3)) :=
  state.order.toFinset

end FourCropOrderedRepairState

/-- The fixed `6n` allowance: three tokens at each of two length-`n` sides. -/
abbrev FourCropFreeSlot (n : Nat) := Fin 3 × (Fin n ⊕ Fin n)

/-- Three copies of each forced vertex lost from a crop. -/
abbrev FourCropLostVertexThreeToken (n : Nat) (c : FourCropCorner)
    (hn : 3 ≤ n) (F : Finset (GridVertex n n)) :=
  {v // v ∈ fourCropLostVertices n c hn F} × Fin 3

/-- Three slots credited for every selected repair vertex. -/
abbrev FourCropRepairThreeSlot {n : Nat}
    (R : Finset (GridVertex (n - 3) (n - 3))) :=
  {v // v ∈ R} × Fin 3

@[simp] theorem card_fourCropFreeSlot (n : Nat) :
    Fintype.card (FourCropFreeSlot n) = 6 * n := by
  simp [FourCropFreeSlot]
  omega

@[simp] theorem card_fourCropLostVertexThreeToken (n : Nat)
    (c : FourCropCorner) (hn : 3 ≤ n) (F : Finset (GridVertex n n)) :
    Fintype.card (FourCropLostVertexThreeToken n c hn F) =
      3 * fourCropFrameLoss n c hn F := by
  simp [FourCropLostVertexThreeToken, card_fourCropLostVertices]
  omega

@[simp] theorem card_fourCropRepairThreeSlot {n : Nat}
    (R : Finset (GridVertex (n - 3) (n - 3))) :
    Fintype.card (FourCropRepairThreeSlot R) = 3 * R.card := by
  simp [FourCropRepairThreeSlot]
  omega

/-- Concrete input replacing the unproved anti-congestion step.  Besides an
actual injection, it carries the selected repair, its ordinary admissibility,
and the stronger ordered bundle-signature certificate. -/
structure BundlePreservingInjectionArgument (n : Nat) (hn : 5 ≤ n)
    (c : FourCropCorner) (F : Finset (GridVertex n n)) where
  state : FourCropOrderedRepairState n hn c F
  isRepairSet : IsCropRepairSet (fourCropEmbedding n c (by omega)) F state.repairSet
  repairAdmissible : CropRepairAdmissible (gridGraph (n - 3) (n - 3))
    (fourCropEmbedding n c (by omega)) F state.repairSet
  repair_card_le_loss : state.repairSet.card ≤
    fourCropFrameLoss n c (by omega) F
  slotMap : FourCropLostVertexThreeToken n c (by omega) F →
    FourCropFreeSlot n ⊕ FourCropRepairThreeSlot state.repairSet
  slotMap_injective : Function.Injective slotMap

/-- A token injection by itself gives the exact cardinal inequality needed by
crop surgery.  Repair disjointness and admissibility are deliberately not
hidden in this statement. -/
theorem netFrameLoss_le_two_mul_of_injection
    {n : Nat} {c : FourCropCorner} {hn : 3 ≤ n}
    {F : Finset (GridVertex n n)}
    (R : Finset (GridVertex (n - 3) (n - 3)))
    (slotMap : FourCropLostVertexThreeToken n c hn F →
      FourCropFreeSlot n ⊕ FourCropRepairThreeSlot R)
    (slotMap_injective : Function.Injective slotMap) :
    netFrameLoss (fourCropEmbedding n c hn) F R ≤ 2 * n := by
  have hcard := Fintype.card_le_of_injective slotMap slotMap_injective
  simp only [Fintype.card_sum, card_fourCropLostVertexThreeToken,
    card_fourCropFreeSlot, card_fourCropRepairThreeSlot] at hcard
  unfold netFrameLoss fourCropFrameLoss at *
  omega

/-- Bundled form of `netFrameLoss_le_two_mul_of_injection`.  The bundle's
other fields are explicit hypotheses used when extracting an actual repair. -/
theorem netFrameLoss_le_two_mul_of_bundlePreservingInjection
    {n : Nat} (hn : 5 ≤ n) {c : FourCropCorner}
    {F : Finset (GridVertex n n)}
    (argument : BundlePreservingInjectionArgument n hn c F) :
    netFrameLoss (fourCropEmbedding n c (by omega)) F argument.state.repairSet ≤
      2 * n :=
  netFrameLoss_le_two_mul_of_injection argument.state.repairSet
    argument.slotMap argument.slotMap_injective

/-- Select the north-west crop.  If it is active, use the supplied argument for
that selected crop; otherwise use the empty repair.  Although the conclusion
is existentially packaged for the crop-surgery API, this theorem neither
proves that a suitable injection argument exists nor compares the four crops. -/
theorem exists_fourCrop_repair_of_active_injections
    {n : Nat} (hn : 5 ≤ n) (F : Finset (GridVertex n n))
    (hF : (forcedEdgeGraph (gridGraph n n) (↑F : Set (GridVertex n n))).IsAcyclic)
    (concreteInjection : ∀ c, FourCropActive n c (by omega) F →
      BundlePreservingInjectionArgument n hn c F) :
    ∃ (c : FourCropCorner) (R : Finset (GridVertex (n - 3) (n - 3))),
      IsCropRepairSet (fourCropEmbedding n c (by omega)) F R ∧
      CropRepairAdmissible (gridGraph (n - 3) (n - 3))
        (fourCropEmbedding n c (by omega)) F R ∧
      R.card ≤ fourCropFrameLoss n c (by omega) F ∧
      netFrameLoss (fourCropEmbedding n c (by omega)) F R ≤ 2 * n := by
  let c := FourCropCorner.northWest
  by_cases hactive : FourCropActive n c (by omega) F
  · let argument := concreteInjection c hactive
    exact ⟨c, argument.state.repairSet, argument.isRepairSet,
      argument.repairAdmissible, argument.repair_card_le_loss,
      netFrameLoss_le_two_mul_of_bundlePreservingInjection hn argument⟩
  · refine ⟨c, ∅, by simp [IsCropRepairSet], ?_, by simp, ?_⟩
    · simpa [CropRepairAdmissible, fourCropEmbedding] using
        threeSideCrop_forcedSet_isAcyclic n c.top c.bottom c.left c.right
          (by omega) c.top_add_bottom c.left_add_right F hF
    · simp only [netFrameLoss, Finset.card_empty, Nat.sub_zero]
      exact Nat.le_of_not_gt hactive

/-- The formal Step 7 implication from supplied data.  The proof consumes only
the supplied argument for the selected north-west crop when that crop is
active.  It is not an existence theorem for injection arguments, an
anti-congestion theorem, or a theorem comparing the four crop choices. -/
theorem maxForcedAcyclic_fourCrop_upper_recurrence
    {n : Nat} (hn : 5 ≤ n)
    (concreteInjection : ∀ (F : Finset (GridVertex n n)),
      (forcedEdgeGraph (gridGraph n n) (↑F : Set (GridVertex n n))).IsAcyclic →
      ∀ c, FourCropActive n c (by omega) F →
        BundlePreservingInjectionArgument n hn c F) :
    maxForcedAcyclic n n ≤
      maxForcedAcyclic (n - 3) (n - 3) + 2 * n := by
  obtain ⟨F, hmax, hF, -⟩ := exists_card_eq_maxForcedAcyclic_and_maximal n n
  obtain ⟨c, R, hR, hadm, hsize, hloss⟩ :=
    exists_fourCrop_repair_of_active_injections hn F hF (concreteInjection F hF)
  exact maxForcedAcyclic_le_of_threeSideCrop_repair
    n c.top c.bottom c.left c.right (by omega)
    c.top_add_bottom c.left_add_right F R hmax hR hadm hsize hloss

/-- Spanning-tree form of the same concrete north-west implication.  The
hypothesis supplies the selected crop's argument; this does not establish its
existence or compare it with another crop. -/
theorem maxPreserved_fourCrop_upper_recurrence
    {n : Nat} (hn : 5 ≤ n)
    (concreteInjection : ∀ (F : Finset (GridVertex n n)),
      (forcedEdgeGraph (gridGraph n n) (↑F : Set (GridVertex n n))).IsAcyclic →
      ∀ c, FourCropActive n c (by omega) F →
        BundlePreservingInjectionArgument n hn c F) :
    maxPreserved n n ≤ maxPreserved (n - 3) (n - 3) + 2 * n := by
  rw [maxPreserved_eq_maxForcedAcyclic (by omega) (by omega),
    maxPreserved_eq_maxForcedAcyclic (by omega) (by omega)]
  exact maxForcedAcyclic_fourCrop_upper_recurrence hn concreteInjection

end GridGraphs
