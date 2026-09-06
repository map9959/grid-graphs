import GridGraphs.GridBoundaryCycle
import GridGraphs.GridCropComponents
import GridGraphs.CropRepairBundle

/-!
# Cyclic signatures of cropped grid boundaries

The boundary word alone is not enough to decide whether a repair is legal.
This file packages the boundary word together with the physical, component,
and labelled-quotient data used by a crop repair.  In particular, repair
bundles are not made disjoint: a physical edge incident to two repair vertices
occurs in both bundles and still has only one label in the quotient.
-/

namespace GridGraphs

open Finset SimpleGraph

section OffsetCrop

variable {p q m n : Nat} (rowOffset colOffset : Nat)
  (hrows : rowOffset + p ≤ m) (hcols : colOffset + q ≤ n)
  (hp : 2 ≤ p) (hq : 2 ≤ q)
  (F : Finset (GridVertex m n)) (R : Finset (GridVertex p q))

private abbrev cropEmbedding :=
  gridOffsetEmbedding rowOffset colOffset hrows hcols

private abbrev boundaryInducedGraph :=
  cropInducedForcedGraph rowOffset colOffset hrows hcols
    (↑F : Set (GridVertex m n))

/-- The induced forced component met by a boundary position, when that
boundary vertex is forced. -/
noncomputable def cyclicBoundaryInducedComponent?
    (i : GridBoundaryPosition p q) :
    Option (boundaryInducedGraph rowOffset colOffset hrows hcols F).ConnectedComponent := by
  classical
  let v := gridBoundaryVertex hp hq i
  if hv : cropEmbedding rowOffset colOffset hrows hcols v ∈ F then
    exact some ((boundaryInducedGraph rowOffset colOffset hrows hcols F).connectedComponentMk
      ⟨v, hv⟩)
  else
    exact none

/-- The ambient ancestor of the boundary component, when the boundary
position belongs to the induced forced set. -/
noncomputable def cyclicBoundaryAmbientAncestor?
    (i : GridBoundaryPosition p q) :
    Option (((gridGraph m n).induce (↑F : Set (GridVertex m n))).ConnectedComponent) :=
  (cyclicBoundaryInducedComponent? rowOffset colOffset hrows hcols hp hq F i).map
    (cropConnectedComponentAncestor rowOffset colOffset hrows hcols
      (↑F : Set (GridVertex m n)))

/-- All valid straight axes of the induced component at a boundary position.
`none` means that the boundary vertex is not in the induced forced set;
`some ∅` records a genuinely non-straight component. -/
noncomputable def cyclicBoundaryComponentAxes?
    (i : GridBoundaryPosition p q) : Option (Finset ForcedComponentAxis) :=
  (cyclicBoundaryInducedComponent? rowOffset colOffset hrows hcols hp hq F i).map
    inducedForcedComponentValidAxes

/-- Half-edges based at one canonical clockwise boundary position. -/
def cyclicBoundaryFrameHalfEdges (i : GridBoundaryPosition p q) :
    Set (CropFrameHalfEdge p q m n rowOffset colOffset hrows hcols hp hq) :=
  {e | e.boundaryPosition = i}

/-- One slot of the canonical clockwise boundary signature. -/
structure CyclicCropBoundarySlot (i : GridBoundaryPosition p q) where
  position : GridBoundaryPosition p q
  vertex : GridVertex p q
  inducedComponent? :
    Option (boundaryInducedGraph rowOffset colOffset hrows hcols F).ConnectedComponent
  ambientAncestor? :
    Option (((gridGraph m n).induce (↑F : Set (GridVertex m n))).ConnectedComponent)
  inducedAxes? : Option (Finset ForcedComponentAxis)
  frameHalfEdges :
    Set (CropFrameHalfEdge p q m n rowOffset colOffset hrows hcols hp hq)

/-- The canonical slot at position `i`. -/
noncomputable def canonicalCyclicCropBoundarySlot (i : GridBoundaryPosition p q) :
    CyclicCropBoundarySlot rowOffset colOffset hrows hcols hp hq F i where
  position := i
  vertex := gridBoundaryVertex hp hq i
  inducedComponent? :=
    cyclicBoundaryInducedComponent? rowOffset colOffset hrows hcols hp hq F i
  ambientAncestor? :=
    cyclicBoundaryAmbientAncestor? rowOffset colOffset hrows hcols hp hq F i
  inducedAxes? :=
    cyclicBoundaryComponentAxes? rowOffset colOffset hrows hcols hp hq F i
  frameHalfEdges :=
    cyclicBoundaryFrameHalfEdges rowOffset colOffset hrows hcols hp hq i

/-- Full data retained by a cyclic crop signature.  The quotient itself is
derived below from `physicalRepairEdges` and `quotientEnds`, so it cannot drift
out of sync with its labels or endpoints. -/
structure CyclicCropBoundarySignature where
  slots : (i : GridBoundaryPosition p q) →
    CyclicCropBoundarySlot rowOffset colOffset hrows hcols hp hq F i
  physicalRepairEdges : Finset (GridEdge p q)
  bundles : GridVertex p q → Finset (GridEdge p q)
  quotientEnds : GridEdge p q →
    (cropInitialForcedGraph (cropEmbedding rowOffset colOffset hrows hcols) F).ConnectedComponent ×
      (cropInitialForcedGraph (cropEmbedding rowOffset colOffset hrows hcols) F).ConnectedComponent
  quotientFibers : GridEdge p q → Finset (GridEdge p q)

/-- The labelled quotient reconstructed from signature data. -/
def CyclicCropBoundarySignature.quotient
    (σ : CyclicCropBoundarySignature rowOffset colOffset hrows hcols hp hq F) :=
  SimpleGraph.labelledExtension
    (⊥ : SimpleGraph
      (cropInitialForcedGraph (cropEmbedding rowOffset colOffset hrows hcols) F).ConnectedComponent)
    σ.quotientEnds σ.physicalRepairEdges

/-- Repair admissibility as seen by the full signature.  This is deliberately
the label-retaining quotient predicate, so loops and parallel physical labels
are not lost. -/
def CyclicCropBoundarySignature.RepairAdmissible
    (σ : CyclicCropBoundarySignature rowOffset colOffset hrows hcols hp hq F) : Prop :=
  σ.quotient.IsAcyclic

/-- The canonical full signature of an offset crop and a proposed repair. -/
noncomputable def canonicalCyclicCropBoundarySignature :
    CyclicCropBoundarySignature rowOffset colOffset hrows hcols hp hq F where
  slots := canonicalCyclicCropBoundarySlot rowOffset colOffset hrows hcols hp hq F
  physicalRepairEdges :=
    physicalCropRepairEdges (cropEmbedding rowOffset colOffset hrows hcols) F R
  bundles := fun u =>
    cropRepairBundle (cropEmbedding rowOffset colOffset hrows hcols) F R u
  quotientEnds :=
    cropRepairComponentEnds (cropEmbedding rowOffset colOffset hrows hcols) F
  quotientFibers := fun edge =>
    cropRepairParallelFiber (cropEmbedding rowOffset colOffset hrows hcols) F R edge

/-- Field-by-field specification of the canonical signature.  This theorem is
the stable simplification API for consumers; unfolding the constructor is not
required. -/
theorem canonicalCyclicCropBoundarySignature_spec :
    let σ := canonicalCyclicCropBoundarySignature
      rowOffset colOffset hrows hcols hp hq F R
    (∀ i, σ.slots i =
        canonicalCyclicCropBoundarySlot rowOffset colOffset hrows hcols hp hq F i) ∧
      σ.physicalRepairEdges =
        physicalCropRepairEdges (cropEmbedding rowOffset colOffset hrows hcols) F R ∧
      (∀ u, σ.bundles u =
        cropRepairBundle (cropEmbedding rowOffset colOffset hrows hcols) F R u) ∧
      σ.quotientEnds =
        cropRepairComponentEnds (cropEmbedding rowOffset colOffset hrows hcols) F ∧
      (∀ edge, σ.quotientFibers edge =
        cropRepairParallelFiber (cropEmbedding rowOffset colOffset hrows hcols) F R edge) := by
  simp [canonicalCyclicCropBoundarySignature]

/-- The quotient reconstructed by the canonical signature is definitionally
the crop-repair component quotient. -/
theorem canonicalCyclicCropBoundarySignature_quotient :
    (canonicalCyclicCropBoundarySignature
      rowOffset colOffset hrows hcols hp hq F R).quotient =
      cropRepairComponentQuotient
        (cropEmbedding rowOffset colOffset hrows hcols) F R := by
  rfl

/-- Canonical signature data decides its repair predicate exactly by the
labelled component quotient. -/
theorem canonicalCyclicCropBoundarySignature_quotientAcyclic_iff :
    (canonicalCyclicCropBoundarySignature
      rowOffset colOffset hrows hcols hp hq F R).RepairAdmissible ↔
      (cropRepairComponentQuotient
        (cropEmbedding rowOffset colOffset hrows hcols) F R).IsAcyclic := by
  rfl

/-- Quotient-theorem form of the canonical admissibility test. -/
theorem canonicalCyclicCropBoundarySignature_admissible_iff_independent :
    (canonicalCyclicCropBoundarySignature
      rowOffset colOffset hrows hcols hp hq F R).RepairAdmissible ↔
      SimpleGraph.LabelledEdgeIndependent
        (cropInitialForcedGraph (cropEmbedding rowOffset colOffset hrows hcols) F)
        GridEdge.primalEndpoints
        (physicalCropRepairEdges (cropEmbedding rowOffset colOffset hrows hcols) F R) := by
  rw [canonicalCyclicCropBoundarySignature_quotientAcyclic_iff]
  exact SimpleGraph.labelledComponentQuotient_isAcyclic_iff _ _ _

/-- Actual crop-repair admissibility is exactly admissibility of the canonical
signature.  No enumeration or physical-edge subdivision hypothesis is needed. -/
theorem cropRepairAdmissible_iff_canonical_signature
    (hR : IsCropRepairSet
      (cropEmbedding rowOffset colOffset hrows hcols) F R)
    (hInitial :
      (cropInitialForcedGraph
        (cropEmbedding rowOffset colOffset hrows hcols) F).IsAcyclic) :
    CropRepairAdmissible (gridGraph p q)
        (cropEmbedding rowOffset colOffset hrows hcols) F R ↔
      (canonicalCyclicCropBoundarySignature
        rowOffset colOffset hrows hcols hp hq F R).RepairAdmissible := by
  rw [canonicalCyclicCropBoundarySignature_quotientAcyclic_iff]
  exact cropRepairAdmissible_iff_componentQuotient_isAcyclic
    (cropEmbedding rowOffset colOffset hrows hcols) F R hR hInitial

/-- Canonical-signature formulation of actual repair admissibility. -/
theorem canonicalCyclicCropBoundarySignature_admissible_iff
    (hR : IsCropRepairSet
      (cropEmbedding rowOffset colOffset hrows hcols) F R)
    (hInitial :
      (cropInitialForcedGraph
        (cropEmbedding rowOffset colOffset hrows hcols) F).IsAcyclic) :
    (canonicalCyclicCropBoundarySignature
        rowOffset colOffset hrows hcols hp hq F R).RepairAdmissible ↔
      CropRepairAdmissible (gridGraph p q)
        (cropEmbedding rowOffset colOffset hrows hcols) F R :=
  (cropRepairAdmissible_iff_canonical_signature
    rowOffset colOffset hrows hcols hp hq F R hR hInitial).symm

/-- A strict isomorphism keeps all labels literal.  It is stronger than an
abstract graph isomorphism and is useful for comparing independently produced
certificates without permitting a hidden permutation of physical edges. -/
structure StrictCyclicCropBoundarySignatureIso
    (σ τ : CyclicCropBoundarySignature rowOffset colOffset hrows hcols hp hq F) where
  slots_eq : σ.slots = τ.slots
  physicalRepairEdges_eq : σ.physicalRepairEdges = τ.physicalRepairEdges
  bundles_eq : σ.bundles = τ.bundles
  quotientEnds_eq : σ.quotientEnds = τ.quotientEnds
  quotientFibers_eq : σ.quotientFibers = τ.quotientFibers

namespace StrictCyclicCropBoundarySignatureIso

/-- Strict signature isomorphisms preserve the clockwise successor slots. -/
theorem successor_slot_eq
    {σ τ : CyclicCropBoundarySignature rowOffset colOffset hrows hcols hp hq F}
    (h : StrictCyclicCropBoundarySignatureIso rowOffset colOffset hrows hcols hp hq F σ τ)
    (i : GridBoundaryPosition p q) :
    σ.slots (gridBoundarySucc hp hq i) =
      τ.slots (gridBoundarySucc hp hq i) := by
  rw [h.slots_eq]

/-- Strict isomorphisms preserve the reconstructed labelled quotient. -/
theorem quotient_eq
    {σ τ : CyclicCropBoundarySignature rowOffset colOffset hrows hcols hp hq F}
    (h : StrictCyclicCropBoundarySignatureIso rowOffset colOffset hrows hcols hp hq F σ τ) :
    σ.quotient = τ.quotient := by
  unfold CyclicCropBoundarySignature.quotient
  rw [h.physicalRepairEdges_eq, h.quotientEnds_eq]

/-- Repair admissibility transports across a strict signature isomorphism. -/
theorem repairAdmissible_iff
    {σ τ : CyclicCropBoundarySignature rowOffset colOffset hrows hcols hp hq F}
    (h : StrictCyclicCropBoundarySignatureIso rowOffset colOffset hrows hcols hp hq F σ τ) :
    σ.RepairAdmissible ↔ τ.RepairAdmissible := by
  rw [CyclicCropBoundarySignature.RepairAdmissible,
    CyclicCropBoundarySignature.RepairAdmissible, h.quotient_eq]

/-- Strictly isomorphic canonical signatures transport the actual
`CropRepairAdmissible` predicate between repair sets. -/
theorem cropRepairAdmissible_iff
    (S : Finset (GridVertex p q))
    (h : StrictCyclicCropBoundarySignatureIso rowOffset colOffset hrows hcols hp hq F
      (canonicalCyclicCropBoundarySignature
        rowOffset colOffset hrows hcols hp hq F R)
      (canonicalCyclicCropBoundarySignature
        rowOffset colOffset hrows hcols hp hq F S))
    (hR : IsCropRepairSet
      (cropEmbedding rowOffset colOffset hrows hcols) F R)
    (hS : IsCropRepairSet
      (cropEmbedding rowOffset colOffset hrows hcols) F S)
    (hInitial :
      (cropInitialForcedGraph
        (cropEmbedding rowOffset colOffset hrows hcols) F).IsAcyclic) :
    CropRepairAdmissible (gridGraph p q)
        (cropEmbedding rowOffset colOffset hrows hcols) F R ↔
      CropRepairAdmissible (gridGraph p q)
        (cropEmbedding rowOffset colOffset hrows hcols) F S := by
  exact (cropRepairAdmissible_iff_canonical_signature
    rowOffset colOffset hrows hcols hp hq F R hR hInitial).trans
      (h.repairAdmissible_iff.trans
        (cropRepairAdmissible_iff_canonical_signature
          rowOffset colOffset hrows hcols hp hq F S hS hInitial).symm)

end StrictCyclicCropBoundarySignatureIso

end OffsetCrop

end GridGraphs
