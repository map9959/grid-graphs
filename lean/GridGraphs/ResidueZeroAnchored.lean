import GridGraphs.ResidueZeroWidening
import GridGraphs.ResidueZeroCaps
import GridGraphs.ResidueZeroWord
import GridGraphs.ResidueZeroFrontier

/-!
# A bounded anchor for the residue-zero dual graph

The final interior face at the right boundary is a useful endpoint for an
inductive connectivity certificate: unlike `GridFace.out`, it has a coordinate
which can be widened.  The edge from that face to `out` is kept separate.

The current widening API proves preservation only for paths in
`widenableOldDualGraph`.  Accordingly the certificate below records such paths,
not merely paths in the old dual graph.  The final section states the exact
additional geometric obligations needed to complete the induction.  In
particular, no computational proof of the width-seven case is used here.
-/

namespace GridGraphs

open SimpleGraph

/-- Coordinates of the rightmost face on the final interior frontier. -/
def residueZeroAnchorCoord (k : Nat) (hk : 7 ≤ k) :
    Fin (3 * k - 1) × Fin (3 * k - 1) :=
  (⟨3 * k - 3, by omega⟩, ⟨3 * k - 2, by omega⟩)

/-- The designated bounded anchor. -/
def residueZeroAnchor (k : Nat) (hk : 7 ≤ k) :
    GridFace (3 * k) (3 * k) :=
  .cell (residueZeroAnchorCoord k hk).1 (residueZeroAnchorCoord k hk).2

/-- The anchor has a separately proved edge to the unbounded face. -/
theorem residueZeroAnchor_adj_out (k : Nat) (hk : 7 ≤ k) :
    (uuDualGraph (uResidueZero k hk)).Adj (residueZeroAnchor k hk) .out := by
  simpa [residueZeroAnchor, residueZeroAnchorCoord] using
    final_interior_frontier_adj_out k hk

/-- A strengthened bounded-anchor certificate.  Its paths use only old edges
which are also known to survive the next widening. -/
structure ResidueZeroAnchoredCertificate (k : Nat) (hk : 7 ≤ k) : Prop where
  reachesAnchor :
    ∀ (r : Fin (3 * k - 1)), 0 < r.val → r.val < 3 * k - 2 →
      ∀ c : Fin (3 * k - 1),
        (uuDualGraph (uResidueZero k hk)).Reachable (.cell r c)
          (residueZeroAnchor k hk)
  stableReachesAnchor :
    ∀ (r : Fin (3 * k - 1)), 0 < r.val → r.val < 3 * k - 2 →
      ∀ c : Fin (3 * k - 1),
        (widenableOldDualGraph k hk).Reachable (r, c)
          (residueZeroAnchorCoord k hk)
  anchorToOut :
    (uuDualGraph (uResidueZero k hk)).Adj (residueZeroAnchor k hk) .out

/-- The OUT edge is uniform, so only the stable bounded paths have to be
supplied when constructing a certificate. -/
theorem residueZeroAnchoredCertificate_mk (k : Nat) (hk : 7 ≤ k)
    (hreach :
      ∀ (r : Fin (3 * k - 1)), 0 < r.val → r.val < 3 * k - 2 →
        ∀ c : Fin (3 * k - 1),
          (widenableOldDualGraph k hk).Reachable (r, c)
            (residueZeroAnchorCoord k hk)) :
    ResidueZeroAnchoredCertificate k hk :=
  ⟨fun r hr0 hrlast c => by
      simpa [residueZeroAnchor, residueZeroAnchorCoord, widenableOldDualToOld] using
        (hreach r hr0 hrlast c).map (widenableOldDualToOld k hk),
    hreach, residueZeroAnchor_adj_out k hk⟩

/-- Stable paths are, in particular, paths in the old dual graph. -/
theorem ResidueZeroAnchoredCertificate.bounded_reachable_anchor
    {k : Nat} {hk : 7 ≤ k} (h : ResidueZeroAnchoredCertificate k hk)
    (r : Fin (3 * k - 1)) (hr0 : 0 < r.val) (hrlast : r.val < 3 * k - 2)
    (c : Fin (3 * k - 1)) :
    (uuDualGraph (uResidueZero k hk)).Reachable (.cell r c)
      (residueZeroAnchor k hk) :=
  h.reachesAnchor r hr0 hrlast c

/-- A bounded-anchor certificate closes the previously conditional interior
reachability statement. -/
theorem ResidueZeroAnchoredCertificate.interiorReachability
    {k : Nat} {hk : 7 ≤ k} (h : ResidueZeroAnchoredCertificate k hk) :
    ResidueZeroInteriorReachability k hk := by
  intro r hr0 hrlast c
  exact (h.bounded_reachable_anchor r hr0 hrlast c).trans
    h.anchorToOut.reachable

/-- Connectivity follows from the anchored certificate. -/
theorem uuDualGraph_uResidueZero_connected_of_anchored
    (k : Nat) (hk : 7 ≤ k) (h : ResidueZeroAnchoredCertificate k hk) :
    (uuDualGraph (uResidueZero k hk)).Connected :=
  uuDualGraph_uResidueZero_connected_of_interior k hk h.interiorReachability

/-- Forced-complement acyclicity follows from the anchored certificate. -/
theorem forced_compl_uResidueZero_isAcyclic_of_anchored
    (k : Nat) (hk : 7 ≤ k) (h : ResidueZeroAnchoredCertificate k hk) :
    (forcedEdgeGraph (gridGraph (3 * k) (3 * k))
      (↑(uResidueZero k hk) : Set (GridVertex (3 * k) (3 * k)))ᶜ).IsAcyclic :=
  forced_compl_uResidueZero_isAcyclic_of_interior k hk h.interiorReachability

/-- The preserving spanning-tree consequence of an anchored certificate. -/
theorem exists_isTree_preserving_compl_uResidueZero_of_anchored
    (k : Nat) (hk : 7 ≤ k) (h : ResidueZeroAnchoredCertificate k hk) :
    ∃ T : SimpleGraph (GridVertex (3 * k) (3 * k)),
      T ≤ gridGraph (3 * k) (3 * k) ∧ T.IsTree ∧
      ∀ ⦃v : GridVertex (3 * k) (3 * k)⦄,
        v ∈ (↑(uResidueZero k hk) : Set (GridVertex (3 * k) (3 * k)))ᶜ →
          preservesIncidentEdges (gridGraph (3 * k) (3 * k)) T v :=
  exists_isTree_preserving_compl_uResidueZero_of_interior
    k hk h.interiorReachability

/-- The target lower bound follows from an anchored certificate. -/
theorem residueZero_le_maxPreserved_of_anchored
    (k : Nat) (hk : 7 ≤ k) (h : ResidueZeroAnchoredCertificate k hk) :
    3 * k ^ 2 + 3 * k - 2 ≤ maxPreserved (3 * k) (3 * k) :=
  residueZero_le_maxPreserved_of_interior k hk h.interiorReachability

/-! ## Exact widening obligations -/

/-- First checkpoint in the new right slab, level with the embedded old
anchor. -/
def widenedAnchorSlabFace (k : Nat) (hk : 7 ≤ k) :
    GridFace (3 * (k + 1)) (3 * (k + 1)) :=
  .cell ⟨3 * k - 1, by omega⟩ ⟨3 * k, by omega⟩

/-- Checkpoint below the slab, on the frontier supplied by the appended
`R_k`. -/
def widenedAnchorAppendedFace (k : Nat) (hk : 7 ≤ k) :
    GridFace (3 * (k + 1)) (3 * (k + 1)) :=
  .cell ⟨3 * k, by omega⟩ ⟨3 * k, by omega⟩

/-- The missing bounded bridge, split at the new right slab and appended
`R_k`.  The old anchor is already shifted by the two prepended rows by
`widenCell`.

The existing local widening lemmas do not prove the first leg from column
`3*k-2` to column `3*k`, nor the final leg to column `3*k+1`.
-/
def ResidueZeroAnchorWideningBridge (k : Nat) (hk : 7 ≤ k) : Prop :=
  let G := uuDualGraph (uResidueZero (k + 1) (by omega))
  G.Reachable
      (widenCell k (residueZeroAnchorCoord k hk).1
        (residueZeroAnchorCoord k hk).2)
      (widenedAnchorSlabFace k hk) ∧
    G.Reachable (widenedAnchorSlabFace k hk)
      (widenedAnchorAppendedFace k hk) ∧
    G.Reachable (widenedAnchorAppendedFace k hk)
      (residueZeroAnchor (k + 1) (by omega))

theorem residueZeroAnchorWideningBridge_reachable
    (k : Nat) (hk : 7 ≤ k) (h : ResidueZeroAnchorWideningBridge k hk) :
    (uuDualGraph (uResidueZero (k + 1) (by omega))).Reachable
      (widenCell k (residueZeroAnchorCoord k hk).1
        (residueZeroAnchorCoord k hk).2)
      (residueZeroAnchor (k + 1) (by omega)) :=
  h.1.trans (h.2.1.trans h.2.2)

/-- A new interior face is genuinely new if it is not the widened image of an
old interior face.  This includes the two prepended face rows, the new right
slab, and the appended-row region. -/
def IsNewResidueZeroInteriorFace (k : Nat)
    (r c : Fin (3 * (k + 1) - 1)) : Prop :=
  ¬ ∃ (r₀ : Fin (3 * k - 1)), 0 < r₀.val ∧ r₀.val < 3 * k - 2 ∧
      ∃ c₀ : Fin (3 * k - 1), widenCell k r₀ c₀ = .cell r c

/-- Besides the bridge, the induction needs paths for all genuinely new faces
and stable paths one width further ahead.  The latter is necessary because the
certificate deliberately retains enough information for the next induction
step. -/
structure ResidueZeroAnchorStepGeometry (k : Nat) (hk : 7 ≤ k) : Prop where
  bridge : ResidueZeroAnchorWideningBridge k hk
  newFaces :
    ∀ (r : Fin (3 * (k + 1) - 1)), 0 < r.val →
      r.val < 3 * (k + 1) - 2 → ∀ c : Fin (3 * (k + 1) - 1),
        IsNewResidueZeroInteriorFace k r c →
          (uuDualGraph (uResidueZero (k + 1) (by omega))).Reachable
            (.cell r c) (residueZeroAnchor (k + 1) (by omega))
  nextStable :
    ∀ (r : Fin (3 * (k + 1) - 1)), 0 < r.val →
      r.val < 3 * (k + 1) - 2 → ∀ c : Fin (3 * (k + 1) - 1),
        (widenableOldDualGraph (k + 1) (by omega)).Reachable (r, c)
          (residueZeroAnchorCoord (k + 1) (by omega))

/-- The formal induction step.  Embedded old paths are mapped with the widening
lemma and then explicitly concatenated with the slab/appended-row bridge.
`newFaces` accounts for every face outside that embedded rectangle, while
`nextStable` retains the stronger invariant. -/
theorem residueZeroAnchoredCertificate_succ (k : Nat) (hk : 7 ≤ k)
    (hold : ResidueZeroAnchoredCertificate k hk)
    (hgeom : ResidueZeroAnchorStepGeometry k hk) :
    ResidueZeroAnchoredCertificate (k + 1) (by omega) := by
  refine ⟨?_, hgeom.nextStable, residueZeroAnchor_adj_out (k + 1) (by omega)⟩
  intro r hr0 hrlast c
  by_cases himage : ∃ (r₀ : Fin (3 * k - 1)),
      0 < r₀.val ∧ r₀.val < 3 * k - 2 ∧
        ∃ c₀ : Fin (3 * k - 1), widenCell k r₀ c₀ = .cell r c
  · rcases himage with ⟨r₀, hr₀, hr₀last, c₀, hface⟩
    rw [← hface]
    exact (widenable_old_dual_reachable k hk
      (hold.stableReachesAnchor r₀ hr₀ hr₀last c₀)).trans
        (residueZeroAnchorWideningBridge_reachable k hk hgeom.bridge)
  · exact hgeom.newFaces r hr0 hrlast c himage

/-- The exact symbolic base obligation still absent from the imported local
lemmas.  Proving this proposition requires explicit stable paths through the
rows of `phaseRowsBase`; it cannot be obtained merely from
`phaseRowsBase_valid`, whose frontier lemma assumes an already connected outer
frontier. -/
def ResidueZeroAnchorBasePaths : Prop :=
  ∀ (r : Fin (3 * 7 - 1)), 0 < r.val → r.val < 3 * 7 - 2 →
    ∀ c : Fin (3 * 7 - 1),
      (widenableOldDualGraph 7 (by omega)).Reachable (r, c)
        (residueZeroAnchorCoord 7 (by omega))

theorem residueZeroAnchoredCertificate_seven
    (hbase : ResidueZeroAnchorBasePaths) :
    ResidueZeroAnchoredCertificate 7 (by omega) :=
  residueZeroAnchoredCertificate_mk 7 (by omega) hbase

end GridGraphs
