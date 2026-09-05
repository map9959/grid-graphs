import GridGraphs.CanonicalReconvergenceLens
import GridGraphs.UniversalWasteBoundReduction

/-!
# Conditional universal primal-contour endpoint

This module packages the final conditional U4 reduction.  Its hypothesis is an
explicit routing of the canonical geometric demands into the concrete primal
contour ledger, not a cardinal inequality.
-/

namespace GridGraphs

open Finset SimpleGraph

noncomputable section

/-- The primal contour ledger has cardinality exactly one below the four-side
component rank on the cotree support of a square grid spanning tree. -/
theorem card_primalContourResource_add_one_eq_fourSideComponentRank
    {n : Nat} (hn : 2 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T) :
    let U := supportFinset (gridGraph n n \ T)
    Fintype.card (PrimalContourResource T U) + 1 =
      fourSideComponentRank n U := by
  let U := supportFinset (gridGraph n n \ T)
  have hprimal := card_primalContourResource T U
  have hrank := fourSideComponentRank_eq_component_charge hn U
  have hforced :
      Fintype.card (forcedEdgeGraph (gridGraph n n)
        (↑((Finset.univ : Finset (GridVertex n n)) \ U) :
          Set (GridVertex n n))).ConnectedComponent =
        (internalEdgeFinset T U).card + 1 := by
    simpa [U] using card_forced_compl_components_eq_internalTreeEdges_add_one hT
  dsimp only
  change Fintype.card (PrimalContourResource T U) + 1 =
    fourSideComponentRank n U
  rw [hprimal, hrank]
  rw [hforced]
  omega

/-- Explicit geometric routing of all `n + 3` canonical sweep demands into the
three concrete primal contour resource kinds. -/
structure UniversalPrimalContourRouting
    {n : Nat} (axis : ShoreSweepAxis)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (_hT : IsSpanningSubtree (gridGraph n n) T) where
  toEmbedding : CanonicalShoreDemand axis n ↪
    PrimalContourResource T (supportFinset (gridGraph n n \ T))

/-- The raw physical U3 ledger is exactly the primal contour resource ledger;
the boundary summand changes only through the established port/sector
equivalence. -/
noncomputable def planarLensRawPhysicalResourceEquivPrimalContourResource
    {n : Nat} (hn : 2 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T) :
    CanonicalExpandedContourForest.PlanarLensRawPhysicalResource (T := T) ≃
      PrimalContourResource T (supportFinset (gridGraph n n \ T)) :=
  Equiv.sumCongr (gridCotreeOuterPortEquivBoundarySector hn hn hT)
    (Equiv.sumCongr (Equiv.refl _) (Equiv.refl _))

/-- The full pruned-source regional certificate reaches U4 through the exact
canonical pruning injection.  Direct/reached exits, canonical internal token
edges, and one representative per noninternal carrier are reserved before the
certificate routes only the remaining labelled collisions. -/
noncomputable def universalPrimalContourRoutingOfFullPrunedRegionalCertificate
    {n : Nat} (hn : 2 ≤ n) (axis : ShoreSweepAxis) (hn3 : 3 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T)
    {root : GridVertex n n}
    (certificate : CanonicalExpandedContourForest.FullPrunedRegionalCertificate
      axis hn hn3 hT root) :
    UniversalPrimalContourRouting axis hT where
  toEmbedding :=
    (CanonicalExpandedContourForest.canonicalDemandFullPrunedEmbedding
      axis hn hn3 hT).trans
      (certificate.fullPrunedEmbedding.trans
      (planarLensRawPhysicalResourceEquivPrimalContourResource hn hT).toEmbedding)

/-- Port-aware quotient routing gives the same full-pruned physical embedding
as a regional certificate, without requiring the stronger transition data. -/
noncomputable def universalPrimalContourRoutingOfCanonicalExpandedJointCollisionRouting
    {n : Nat} (hn : 2 ≤ n) (axis : ShoreSweepAxis) (hn3 : 3 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T)
    (routing : CanonicalExpandedContourForest.CanonicalExpandedJointCollisionRouting
      axis hn hn3 hT) :
    UniversalPrimalContourRouting axis hT where
  toEmbedding :=
    (CanonicalExpandedContourForest.canonicalDemandFullPrunedEmbedding
      axis hn hn3 hT).trans
      ((Classical.choice routing).resourceEmbedding.trans
        (planarLensRawPhysicalResourceEquivPrimalContourResource hn hT).toEmbedding)

/-- The shared grouped Hall condition closes the complete conditional routing
chain through its finite residual-cardinality consequence. -/
noncomputable def universalPrimalContourRoutingOfSharedCanonicalGroupedResidualHall
    {n : Nat} (hn : 2 ≤ n) (axis : ShoreSweepAxis) (hn3 : 3 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T)
    {root : GridVertex n n}
    {assignment : CanonicalExpandedContourForest.FullPrunedCarrierBlockGapAssignment
      axis hn hn3 hT root}
    (neighborhoods :
      CanonicalExpandedContourForest.SharedCanonicalGroupedPhysicalNeighborhoods
        axis hn hn3 hT assignment)
    (hHall : CanonicalExpandedContourForest.SharedCanonicalGroupedResidualHall
      axis hn hn3 hT neighborhoods) :
    UniversalPrimalContourRouting axis hT :=
  universalPrimalContourRoutingOfCanonicalExpandedJointCollisionRouting
    hn axis hn3 hT
    (CanonicalExpandedContourForest.sharedCanonicalGroupedResidualHall_canonicalExpandedJointCollisionRouting
      axis hn hn3 hT neighborhoods hHall)

instance {n : Nat} {axis : ShoreSweepAxis}
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    {hT : IsSpanningSubtree (gridGraph n n) T} :
    CoeFun (UniversalPrimalContourRouting axis hT)
      (fun _ => CanonicalShoreDemand axis n →
        PrimalContourResource T (supportFinset (gridGraph n n \ T))) :=
  ⟨fun routing => routing.toEmbedding⟩

/-- An explicit universal primal-contour routing supplies the exact `n + 4`
four-side component-rank bound. -/
theorem n_add_four_le_fourSideComponentRank_of_routing
    {n : Nat} (hn : 2 ≤ n) (axis : ShoreSweepAxis)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T)
    (_routing : UniversalPrimalContourRouting axis hT) :
    n + 4 ≤ fourSideComponentRank n
      (supportFinset (gridGraph n n \ T)) := by
  have hcard := Fintype.card_le_of_injective
    _routing.toEmbedding _routing.toEmbedding.injective
  rw [CanonicalShoreDemand.card] at hcard
  have hledger :=
    card_primalContourResource_add_one_eq_fourSideComponentRank hn hT
  omega

/-- Clean conditional U4 endpoint: geometric primal-contour routing implies the
square-grid universal waste bound through the exact four-side reduction. -/
theorem square_grid_tree_universalWaste_of_universalPrimalContourRouting
    {n : Nat} (hn : 3 ≤ n) (axis : ShoreSweepAxis)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T)
    (routing : UniversalPrimalContourRouting axis hT) :
    n + 2 ≤ incidenceWaste (gridGraph n n \ T) := by
  rw [square_grid_tree_universalWaste_iff_fourSideComponentRank hn hT]
  exact n_add_four_le_fourSideComponentRank_of_routing
    (by omega) axis hT routing

theorem square_grid_tree_universalWaste_of_fullPrunedRegionalCertificate
    {n : Nat} (hn3 : 3 ≤ n) (axis : ShoreSweepAxis)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T)
    {root : GridVertex n n}
    (certificate : CanonicalExpandedContourForest.FullPrunedRegionalCertificate
      axis (by omega) hn3 hT root) :
    n + 2 ≤ incidenceWaste (gridGraph n n \ T) :=
  square_grid_tree_universalWaste_of_universalPrimalContourRouting hn3 axis hT
    (universalPrimalContourRoutingOfFullPrunedRegionalCertificate
      (by omega) axis hn3 hT certificate)

/-- End-to-end conditional universal-waste theorem from the active shared
grouped residual Hall condition; no independent or global Hall hypothesis is
introduced. -/
theorem square_grid_tree_universalWaste_of_sharedCanonicalGroupedResidualHall
    {n : Nat} (hn3 : 3 ≤ n) (axis : ShoreSweepAxis)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T)
    {root : GridVertex n n}
    {assignment : CanonicalExpandedContourForest.FullPrunedCarrierBlockGapAssignment
      axis (by omega) hn3 hT root}
    (neighborhoods :
      CanonicalExpandedContourForest.SharedCanonicalGroupedPhysicalNeighborhoods
        axis (by omega) hn3 hT assignment)
    (hHall : CanonicalExpandedContourForest.SharedCanonicalGroupedResidualHall
      axis (by omega) hn3 hT neighborhoods) :
    n + 2 ≤ incidenceWaste (gridGraph n n \ T) :=
  square_grid_tree_universalWaste_of_universalPrimalContourRouting hn3 axis hT
    (universalPrimalContourRoutingOfSharedCanonicalGroupedResidualHall
      (by omega) axis hn3 hT neighborhoods hHall)

end

end GridGraphs
