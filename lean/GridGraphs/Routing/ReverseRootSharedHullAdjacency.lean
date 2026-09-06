import GridGraphs.Routing.AutomaticOwnershipDisplacement

/-!
# Reverse-root shared-hull adjacency

This module views an active root of the one-copy shared cotree-dual hull from
above.  Incoming provenance retains either an exact selected start occurrence
or an exact child-sector occurrence.  Parent-chain certificates point toward
the root even though resources are read in the reverse direction.

The resource side is the raw physical universe.  Its finite neighborhood is a
set, so coincident observations do not create copies of a physical resource.
No Hall statement is made.
-/

namespace GridGraphs

open Finset SimpleGraph

namespace CanonicalExpandedContourForest

variable {n : Nat} (axis : ShoreSweepAxis) (hn2 : 2 ≤ n) (hn3 : 3 ≤ n)
  {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
  (hT : IsSpanningSubtree (gridGraph n n) T)

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- A selected start occurrence whose parent chain reaches one active shared
hull root.  The collision occurrence, rather than only its component label, is
retained. -/
structure FullPrunedSharedCotreeDualHullRootDescendantStart
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (activeRoot : ↥((fullPrunedSharedCotreeDualHullForest
      axis hn2 hn3 hT assignment).roots)) where
  source : FullPrunedInwardCollision axis hn2 hn3 hT
  reaches : Relation.ReflTransGen
    (fullPrunedSharedCotreeDualHullForest
      axis hn2 hn3 hT assignment).ParentStep
    ((fullPrunedSharedCotreeDualHullLeafEquiv
      axis hn2 hn3 hT assignment source).1) activeRoot.1

/-- An exact child-sector occurrence on an incoming chain to an active root.
Both its parent and child are retained, so equal physical observations do not
identify sector occurrences. -/
structure FullPrunedSharedCotreeDualHullRootDescendantChildSector
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (activeRoot : ↥((fullPrunedSharedCotreeDualHullForest
      axis hn2 hn3 hT assignment).roots)) where
  parent : FullPrunedSharedCotreeDualHullCarrier axis hn2 hn3 hT assignment
  child : ↥((fullPrunedSharedCotreeDualHullForest
    axis hn2 hn3 hT assignment).children parent)
  parent_reaches : Relation.ReflTransGen
    (fullPrunedSharedCotreeDualHullForest
      axis hn2 hn3 hT assignment).ParentStep parent activeRoot.1

/-- Occurrence-preserving origins of reverse traversal from an active root. -/
inductive FullPrunedSharedCotreeDualHullReverseRootOrigin
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (activeRoot : ↥((fullPrunedSharedCotreeDualHullForest
      axis hn2 hn3 hT assignment).roots)) where
  | selectedStart
      (start : FullPrunedSharedCotreeDualHullRootDescendantStart
        axis hn2 hn3 hT assignment activeRoot)
  | childSector
      (sector : FullPrunedSharedCotreeDualHullRootDescendantChildSector
        axis hn2 hn3 hT assignment activeRoot)

/-- Hull vertex at which an incoming occurrence starts. -/
def FullPrunedSharedCotreeDualHullReverseRootOrigin.vertex
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    {activeRoot : ↥((fullPrunedSharedCotreeDualHullForest
      axis hn2 hn3 hT assignment).roots)} :
    FullPrunedSharedCotreeDualHullReverseRootOrigin
        axis hn2 hn3 hT assignment activeRoot →
      FullPrunedSharedCotreeDualHullCarrier axis hn2 hn3 hT assignment
  | .selectedStart start =>
      (fullPrunedSharedCotreeDualHullLeafEquiv
        axis hn2 hn3 hT assignment start.source).1
  | .childSector sector => sector.child.1

/-- Every retained reverse origin carries its complete incoming parent chain. -/
theorem FullPrunedSharedCotreeDualHullReverseRootOrigin.reaches_root
    {root : GridVertex n n}
    {assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root}
    {activeRoot : ↥((fullPrunedSharedCotreeDualHullForest
      axis hn2 hn3 hT assignment).roots)}
    (origin : FullPrunedSharedCotreeDualHullReverseRootOrigin
      axis hn2 hn3 hT assignment activeRoot) :
    Relation.ReflTransGen
      (fullPrunedSharedCotreeDualHullForest
        axis hn2 hn3 hT assignment).ParentStep
      (origin.vertex axis hn2 hn3 hT) activeRoot.1 := by
  cases origin with
  | selectedStart start => exact start.reaches
  | childSector sector =>
      apply Relation.ReflTransGen.head _ sector.parent_reaches
      exact (Finset.mem_filter.mp sector.child.2).2

/-- A raw resource observed at a vertex lying on the certified incoming chain
of a retained origin. -/
structure FullPrunedSharedCotreeDualHullReverseRootAdjacencyWitness
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (activeRoot : ↥((fullPrunedSharedCotreeDualHullForest
      axis hn2 hn3 hT assignment).roots))
    (raw : PlanarLensRawPhysicalResource (T := T)) where
  origin : FullPrunedSharedCotreeDualHullReverseRootOrigin
    axis hn2 hn3 hT assignment activeRoot
  terminal : FullPrunedSharedCotreeDualHullCarrier axis hn2 hn3 hT assignment
  incoming : Relation.ReflTransGen
    (fullPrunedSharedCotreeDualHullForest
      axis hn2 hn3 hT assignment).ParentStep
    (origin.vertex axis hn2 hn3 hT) terminal
  toRoot : Relation.ReflTransGen
    (fullPrunedSharedCotreeDualHullForest
      axis hn2 hn3 hT assignment).ParentStep terminal activeRoot.1
  exposes : (fullPrunedSharedCotreeDualHullObservationAt
    axis hn2 hn3 hT assignment terminal).rawResource?
      axis hn2 hn3 hT = some raw

/-- Reverse-root adjacency uses raw physical equality and therefore introduces
no occurrence-indexed copy on the resource side. -/
def FullPrunedSharedCotreeDualHullReverseRootAdjacent
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (activeRoot : ↥((fullPrunedSharedCotreeDualHullForest
      axis hn2 hn3 hT assignment).roots))
    (raw : PlanarLensRawPhysicalResource (T := T)) : Prop :=
  Nonempty (FullPrunedSharedCotreeDualHullReverseRootAdjacencyWitness
    axis hn2 hn3 hT assignment activeRoot raw)

/-- Any raw observation encountered on a certified incoming chain is adjacent
to its active root. -/
theorem fullPrunedSharedCotreeDualHullReverseRootAdjacent_of_encountered
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (activeRoot : ↥((fullPrunedSharedCotreeDualHullForest
      axis hn2 hn3 hT assignment).roots))
    (origin : FullPrunedSharedCotreeDualHullReverseRootOrigin
      axis hn2 hn3 hT assignment activeRoot)
    (terminal : FullPrunedSharedCotreeDualHullCarrier axis hn2 hn3 hT assignment)
    (raw : PlanarLensRawPhysicalResource (T := T))
    (incoming : Relation.ReflTransGen
      (fullPrunedSharedCotreeDualHullForest
        axis hn2 hn3 hT assignment).ParentStep
      (origin.vertex axis hn2 hn3 hT) terminal)
    (toRoot : Relation.ReflTransGen
      (fullPrunedSharedCotreeDualHullForest
        axis hn2 hn3 hT assignment).ParentStep terminal activeRoot.1)
    (exposes : (fullPrunedSharedCotreeDualHullObservationAt
      axis hn2 hn3 hT assignment terminal).rawResource?
        axis hn2 hn3 hT = some raw) :
    FullPrunedSharedCotreeDualHullReverseRootAdjacent
      axis hn2 hn3 hT assignment activeRoot raw :=
  ⟨{ origin, terminal, incoming, toRoot, exposes }⟩

/-- Adjacency preserves an exact incoming occurrence and its certified origin
at the same active root. -/
theorem fullPrunedSharedCotreeDualHullReverseRootAdjacent_origin
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (activeRoot : ↥((fullPrunedSharedCotreeDualHullForest
      axis hn2 hn3 hT assignment).roots))
    (raw : PlanarLensRawPhysicalResource (T := T))
    (hadj : FullPrunedSharedCotreeDualHullReverseRootAdjacent
      axis hn2 hn3 hT assignment activeRoot raw) :
    ∃ origin : FullPrunedSharedCotreeDualHullReverseRootOrigin
        axis hn2 hn3 hT assignment activeRoot,
      ∃ terminal : FullPrunedSharedCotreeDualHullCarrier
          axis hn2 hn3 hT assignment,
        Relation.ReflTransGen
            (fullPrunedSharedCotreeDualHullForest
              axis hn2 hn3 hT assignment).ParentStep
            (origin.vertex axis hn2 hn3 hT) terminal ∧
          Relation.ReflTransGen
            (fullPrunedSharedCotreeDualHullForest
              axis hn2 hn3 hT assignment).ParentStep terminal activeRoot.1 ∧
          (fullPrunedSharedCotreeDualHullObservationAt
            axis hn2 hn3 hT assignment terminal).rawResource?
              axis hn2 hn3 hT = some raw := by
  let witness := Classical.choice hadj
  exact ⟨witness.origin, witness.terminal, witness.incoming,
    witness.toRoot, witness.exposes⟩

/-- The physical root port determines the retained active-root occurrence.
Thus connecting reverse adjacency through a used port cannot exchange one root
occurrence for another. -/
theorem fullPrunedSharedCotreeDualHullReverseRoot_source_occurrence_unique
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (a b : ↥((fullPrunedSharedCotreeDualHullForest
      axis hn2 hn3 hT assignment).roots))
    (hport : fullPrunedSharedCotreeDualHullRootPort
      axis hn2 hn3 hT assignment a =
        fullPrunedSharedCotreeDualHullRootPort
          axis hn2 hn3 hT assignment b) :
    a = b :=
  fullPrunedSharedCotreeDualHullRootPort_injective
    axis hn2 hn3 hT assignment hport

/-- The physical reverse neighborhood is a finite set.  Multiple incoming
occurrences exposing the same raw resource contribute one member. -/
noncomputable def fullPrunedSharedCotreeDualHullReverseRootRawResources
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (activeRoot : ↥((fullPrunedSharedCotreeDualHullForest
      axis hn2 hn3 hT assignment).roots)) :
    Finset (PlanarLensRawPhysicalResource (T := T)) :=
  Finset.univ.filter fun raw =>
    FullPrunedSharedCotreeDualHullReverseRootAdjacent
      axis hn2 hn3 hT assignment activeRoot raw

@[simp] theorem mem_fullPrunedSharedCotreeDualHullReverseRootRawResources
    {root : GridVertex n n}
    (assignment : FullPrunedCarrierBlockGapAssignment axis hn2 hn3 hT root)
    (activeRoot : ↥((fullPrunedSharedCotreeDualHullForest
      axis hn2 hn3 hT assignment).roots))
    (raw : PlanarLensRawPhysicalResource (T := T)) :
    raw ∈ fullPrunedSharedCotreeDualHullReverseRootRawResources
        axis hn2 hn3 hT assignment activeRoot ↔
      FullPrunedSharedCotreeDualHullReverseRootAdjacent
        axis hn2 hn3 hT assignment activeRoot raw := by
  simp [fullPrunedSharedCotreeDualHullReverseRootRawResources]

end

end CanonicalExpandedContourForest

end GridGraphs
