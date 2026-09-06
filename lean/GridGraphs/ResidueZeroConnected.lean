import GridGraphs.ResidueZeroWord
import GridGraphs.ResidueZeroFrontier
import GridGraphs.ResidueZeroCaps
import GridGraphs.GridDual
import GridGraphs.MaxPreserved

/-!
# Connectivity consequences for the residue-zero construction

The symbolic phase word and the local frontier theorem fit together directly.
They do not, however, prove that the frontier containing a given phase row is
the OUT frontier: `DualFaceRowsAttached` assumes that its outer face row is
already connected.  `ResidueZeroInteriorReachability` isolates exactly the
remaining global frontier certificate.  The cap lemmas turn that certificate
into full dual connectivity, after which forced acyclicity, tree extension, and
the preservation lower bound are formal consequences.
-/

namespace GridGraphs

open Finset SimpleGraph

/-- The syntactic transition classification is the transition relation used by
the local frontier theorem. -/
theorem ValidPhaseTransition.toLocal {k : Nat} {top bottom : PhaseRow}
    (h : ValidPhaseTransition k top bottom) :
    LocalPhaseTransition k top bottom := by
  cases h with
  | ordinaryPred ha0 ha => exact .ordinaryPred _ ha0 ha
  | ordinarySucc ha => exact .ordinarySucc _ ha
  | ordinarySeamSame ha => exact .ordinarySeamSame _ ha
  | ordinarySeamSucc ha => exact .ordinarySeamSucc _ ha
  | seamOrdinaryPred ha0 ha => exact .seamOrdinaryPred _ ha0 ha
  | seamOrdinarySame ha => exact .seamOrdinarySame _ ha

/-- Every adjacent pair in the phase word satisfies the corresponding local
frontier-propagation statement. -/
theorem phaseRows_adjacent_frontier_attached (k : Nat) (hk : 7 ≤ k)
    (i : Nat) (hi : i + 1 < (phaseRows k).length) :
    match ((phaseRows k)[i]'(by omega)) with
    | .ordinary _ =>
        DualFaceRowsAttached (uuDualGraph (uResidueZero k hk))
            (fun c => .cell ⟨i + 1, by rw [phaseRows_length k hk] at hi; omega⟩ c)
            (fun c => .cell ⟨i + 1, by rw [phaseRows_length k hk] at hi; omega⟩ c) →
          DualFaceRowsAttached (uuDualGraph (uResidueZero k hk))
            (fun c => .cell ⟨i + 1, by rw [phaseRows_length k hk] at hi; omega⟩ c)
            (fun c => .cell ⟨i + 2, by rw [phaseRows_length k hk] at hi; omega⟩ c)
    | .seam _ =>
        DualFaceRowsAttached (uuDualGraph (uResidueZero k hk))
            (fun c => .cell ⟨i + 3, by rw [phaseRows_length k hk] at hi; omega⟩ c)
            (fun c => .cell ⟨i + 3, by rw [phaseRows_length k hk] at hi; omega⟩ c) →
          DualFaceRowsAttached (uuDualGraph (uResidueZero k hk))
            (fun c => .cell ⟨i + 3, by rw [phaseRows_length k hk] at hi; omega⟩ c)
            (fun c => .cell ⟨i + 2, by rw [phaseRows_length k hk] at hi; omega⟩ c) := by
  apply localPhaseTransition_frontier_attached k hk i hi
  exact (phaseRows_adjacent_valid k hk i hi).toLocal

/-- The exact global statement still needed from a strengthened frontier
invariant: every non-cap face lies in the OUT component. -/
def ResidueZeroInteriorReachability (k : Nat) (hk : 7 ≤ k) : Prop :=
  ∀ (r : Fin (3 * k - 1)), 0 < r.val → r.val < 3 * k - 2 →
    ∀ c : Fin (3 * k - 1),
      (uuDualGraph (uResidueZero k hk)).Reachable (.cell r c) .out

/-- The interior certificate and the two cap arguments put every dual face in
the OUT component. -/
theorem uResidueZero_dual_reachable_out_of_interior (k : Nat) (hk : 7 ≤ k)
    (hinterior : ResidueZeroInteriorReachability k hk)
    (f : GridFace (3 * k) (3 * k)) :
    (uuDualGraph (uResidueZero k hk)).Reachable f .out := by
  have hk3 : 21 ≤ 3 * k := Nat.mul_le_mul_left 3 hk
  cases f with
  | out => exact Reachable.refl _
  | cell r c =>
      by_cases htop : r.val = 0
      · have hr : r = ⟨0, by omega⟩ := Fin.ext htop
        rw [hr]
        apply initial_cap_face_reachable_out k hk
        intro d
        simpa using hinterior ⟨1, by omega⟩ (by simp) (by simp; omega) d
      · by_cases hbottom : r.val = 3 * k - 2
        · have hr : r = ⟨3 * k - 2, by omega⟩ := Fin.ext hbottom
          rw [hr]
          apply final_cap_face_reachable_out k hk
          intro d hd0 hdlast
          simpa using hinterior ⟨3 * k - 3, by omega⟩
            (by simp; omega) (by simp; omega) d
        · exact hinterior r (by omega) (by omega) c

/-- Conditional completion of dual connectivity.  The sole extra hypothesis is
the strengthened global frontier certificate above. -/
theorem uuDualGraph_uResidueZero_connected_of_interior (k : Nat) (hk : 7 ≤ k)
    (hinterior : ResidueZeroInteriorReachability k hk) :
    (uuDualGraph (uResidueZero k hk)).Connected := by
  have : Nonempty (GridFace (3 * k) (3 * k)) := ⟨.out⟩
  constructor
  intro f g
  exact (uResidueZero_dual_reachable_out_of_interior k hk hinterior f).trans
    (uResidueZero_dual_reachable_out_of_interior k hk hinterior g).symm

/-- Forced-complement acyclicity, conditional only on the missing frontier
certificate. -/
theorem forced_compl_uResidueZero_isAcyclic_of_interior (k : Nat) (hk : 7 ≤ k)
    (hinterior : ResidueZeroInteriorReachability k hk) :
    (forcedEdgeGraph (gridGraph (3 * k) (3 * k))
      (↑(uResidueZero k hk) : Set (GridVertex (3 * k) (3 * k)))ᶜ).IsAcyclic := by
  exact gridDualCycleSeparation (uResidueZero k hk)
    (uuDualGraph_uResidueZero_connected_of_interior k hk hinterior)

/-- A spanning tree preserving the complement, conditional only on the missing
frontier certificate. -/
theorem exists_isTree_preserving_compl_uResidueZero_of_interior
    (k : Nat) (hk : 7 ≤ k)
    (hinterior : ResidueZeroInteriorReachability k hk) :
    ∃ T : SimpleGraph (GridVertex (3 * k) (3 * k)),
      T ≤ gridGraph (3 * k) (3 * k) ∧ T.IsTree ∧
      ∀ ⦃v : GridVertex (3 * k) (3 * k)⦄,
        v ∈ (↑(uResidueZero k hk) : Set (GridVertex (3 * k) (3 * k)))ᶜ →
          preservesIncidentEdges (gridGraph (3 * k) (3 * k)) T v := by
  exact exists_isTree_preserving_compl_of_uuDual_connected_grid
    (uResidueZero k hk)
    (uuDualGraph_uResidueZero_connected_of_interior k hk hinterior)
    (gridGraph_connected (by omega) (by omega))

private theorem degree_eq_of_preserves {V : Type*} [Fintype V]
    (G T : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel T.Adj]
    (hTG : T ≤ G) (v : V) (hv : preservesIncidentEdges G T v) :
    T.degree v = G.degree v := by
  apply congrArg Finset.card
  ext w
  simp only [SimpleGraph.mem_neighborFinset]
  exact ⟨fun h => hTG h, fun h => hv h⟩

/-- The residue-zero construction gives the target lower bound once the missing
interior frontier certificate is supplied. -/
theorem residueZero_le_maxPreserved_of_interior (k : Nat) (hk : 7 ≤ k)
    (hinterior : ResidueZeroInteriorReachability k hk) :
    3 * k ^ 2 + 3 * k - 2 ≤ maxPreserved (3 * k) (3 * k) := by
  classical
  obtain ⟨T, hTG, htree, hpreserves⟩ :=
    exists_isTree_preserving_compl_uResidueZero_of_interior k hk hinterior
  apply le_maxPreserved_of_witness ⟨hTG, htree⟩
  have hsubset :
      (Finset.univ \ uResidueZero k hk) ⊆
        (Finset.univ : Finset (GridVertex (3 * k) (3 * k))).filter
          (fun v => isPreserved (3 * k) (3 * k) T v) := by
    intro v hv
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    unfold isPreserved
    apply degree_eq_of_preserves (gridGraph (3 * k) (3 * k)) T hTG
    exact hpreserves (by simpa using hv)
  unfold numPreserved
  have hcard := Finset.card_le_card hsubset
  rw [Finset.card_sdiff, Finset.inter_univ, uResidueZero_card k hk] at hcard
  simp only [Finset.card_univ] at hcard
  have hgridcard :
      Fintype.card (GridVertex (3 * k) (3 * k)) = (3 * k) * (3 * k) := by
    unfold GridVertex
    simp [Fintype.card_prod]
  rw [hgridcard] at hcard
  have hcompl :
      (3 * k) * (3 * k) - (6 * k ^ 2 - 3 * k + 2) =
        3 * k ^ 2 + 3 * k - 2 := by
    have hkSq : k ≤ 2 * k ^ 2 := by nlinarith
    ring_nf
    omega
  rw [hcompl] at hcard
  exact hcard

end GridGraphs
