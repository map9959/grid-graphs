import GridGraphs.Constructions.ReverseFrame
import GridGraphs.Constructions.ResidueOne.ResidueOneDual

/-!
# Reverse frame for the residue-one family

The old square is shifted down by three rows.  This aligns every old row type
with the same row type in the successor and sends the old bottom row to the new
bottom row.  The complement of the image is the new frame.  Its sequential
certificate is obtained by refactoring the already-proved uniform acyclicity
of the residue-one successor, not by an independent local frame proof.
-/

namespace GridGraphs

open Finset SimpleGraph

/-- Forced vertices in the explicit residue-one construction. -/
def forcedResidueOne (k : Nat) : Finset (GridVertex (3 * k + 1) (3 * k + 1)) :=
  Finset.univ \ uResidueOne k

/-- Coordinate embedding underlying the residue-one reverse recurrence. -/
def residueOneReverseEmbedding (k : Nat) :
    GridVertex (3 * k + 1) (3 * k + 1) ↪
      GridVertex (3 * (k + 1) + 1) (3 * (k + 1) + 1) :=
  gridOffsetEmbedding 3 0 (by omega) (by omega)

/-- Every old forced coordinate remains forced after shifting down three rows. -/
theorem residueOneReverseEmbedding_mem (k : Nat)
    {v : GridVertex (3 * k + 1) (3 * k + 1)}
    (hv : v ∈ forcedResidueOne k) :
    residueOneReverseEmbedding k v ∈ forcedResidueOne (k + 1) := by
  rcases v with ⟨r, c⟩
  simp only [forcedResidueOne, Finset.mem_sdiff, Finset.mem_univ, true_and] at hv ⊢
  intro hnew
  apply hv
  simp only [uResidueOne, Finset.mem_filter, Finset.mem_univ, true_and] at hnew ⊢
  unfold isInUResidueOne at hnew ⊢
  simp only [residueOneReverseEmbedding, gridOffsetEmbedding_fst_val,
    gridOffsetEmbedding_snd_val] at hnew
  rcases hnew with h | h | h | h
  · left
    constructor
    · omega
    constructor <;> omega
  · right; left
    constructor
    · omega
    constructor <;> omega
  · right; right; left
    constructor
    · omega
    constructor <;> omega
  · right; right; right
    omega

theorem residueOneReverseEmbedding_image_subset (k : Nat) :
    (forcedResidueOne k).image (residueOneReverseEmbedding k) ⊆
      forcedResidueOne (k + 1) := by
  intro v hv
  rcases Finset.mem_image.mp hv with ⟨u, hu, rfl⟩
  exact residueOneReverseEmbedding_mem k hu

/-- The residue-one frame as an explicitly ordered coordinate difference. -/
noncomputable def residueOneReverseFrameOrder (k : Nat) :
    List (GridVertex (3 * (k + 1) + 1) (3 * (k + 1) + 1)) :=
  (forcedResidueOne (k + 1) \
    (forcedResidueOne k).image (residueOneReverseEmbedding k)).toList

theorem forcedResidueOne_card (k : Nat) (hk : 1 ≤ k) :
    (forcedResidueOne k).card = 3 * k ^ 2 + 5 * k := by
  rw [forcedResidueOne, Finset.card_sdiff, Finset.inter_univ,
    uResidueOne_card k hk]
  simp only [Finset.card_univ]
  unfold GridVertex
  simp only [Fintype.card_prod, Fintype.card_fin]
  have hpoly : (3 * k + 1) * (3 * k + 1) =
      (6 * k ^ 2 + k + 1) + (3 * k ^ 2 + 5 * k) := by ring
  omega

/-- The coordinate difference contains exactly twice the successor side length
many forced vertices. -/
theorem residueOneReverseFrameOrder_length (k : Nat) (hk : 1 ≤ k) :
    (residueOneReverseFrameOrder k).length = 2 * (3 * (k + 1) + 1) := by
  rw [residueOneReverseFrameOrder, ← List.toFinset_card_of_nodup
    (Finset.nodup_toList _), Finset.toList_toFinset, Finset.card_sdiff]
  rw [Finset.inter_eq_left.mpr (residueOneReverseEmbedding_image_subset k)]
  rw [Finset.card_image_of_injective _ (residueOneReverseEmbedding k).injective]
  rw [forcedResidueOne_card (k + 1) (by omega), forcedResidueOne_card k hk]
  ring_nf
  omega

/-- Refactor the already-proved uniform residue-one successor acyclicity into a
reverse-frame template via the uniform sequential-insertion equivalence.  The
construction does not independently prove acyclicity from local frame checks;
the finite dual certificate API is not used. -/
noncomputable def residueOneReverseFrameTemplate (k : Nat) (hk : 1 ≤ k) :
    ReverseFrameTemplate (3 * k + 1) (3 * k + 1)
      (3 * (k + 1) + 1) (3 * (k + 1) + 1)
      (forcedResidueOne k) (forcedResidueOne (k + 1))
      (2 * (3 * (k + 1) + 1)) := by
  let e := residueOneReverseEmbedding k
  let core := (forcedResidueOne k).image e
  let frame := forcedResidueOne (k + 1) \ core
  have htarget : core ∪ frame = forcedResidueOne (k + 1) := by
    exact Finset.union_sdiff_of_subset (residueOneReverseEmbedding_image_subset k)
  have htargetAcyclic :
      (forcedEdgeGraph (gridGraph (3 * (k + 1) + 1) (3 * (k + 1) + 1))
        (↑(forcedResidueOne (k + 1)) : Set _)).IsAcyclic := by
    have hsets : (↑(forcedResidueOne (k + 1)) : Set _) =
        Set.compl (fun v : GridVertex (3 * (k + 1) + 1) (3 * (k + 1) + 1) =>
          v ∈ uResidueOne (k + 1)) := by
      ext v
      change v ∈ Finset.univ \ uResidueOne (k + 1) ↔
        ¬v ∈ uResidueOne (k + 1)
      simp
    rw [hsets]
    exact forced_compl_uResidueOne_isAcyclic (k + 1) (by omega)
  have hcoreAcyclic :
      (forcedEdgeGraph (gridGraph (3 * (k + 1) + 1) (3 * (k + 1) + 1))
        (↑core : Set _)).IsAcyclic := by
    apply htargetAcyclic.anti
    intro v w hvw
    exact ⟨hvw.1, hvw.2.imp
      (fun hv => residueOneReverseEmbedding_image_subset k hv)
      (fun hw => residueOneReverseEmbedding_image_subset k hw)⟩
  let order := frame.toList
  have hnodup : order.Nodup := Finset.nodup_toList frame
  have hdisj : ∀ v ∈ order, v ∉ core := by
    intro v hv
    have hvframe : v ∈ frame := by simpa [order] using hv
    dsimp [frame] at hvframe
    exact (Finset.mem_sdiff.mp hvframe).2
  have hseq : SequentiallyInsertable
      (gridGraph (3 * (k + 1) + 1) (3 * (k + 1) + 1)) (↑core : Set _) order := by
    apply (forcedEdgeGraph_union_list_isAcyclic_iff_sequentiallyInsertable
      (gridGraph (3 * (k + 1) + 1) (3 * (k + 1) + 1))
      (↑core : Set _) order hnodup hdisj hcoreAcyclic).1
    have htargetSet : (↑core : Set _) ∪ (↑frame : Set _) =
        (↑(forcedResidueOne (k + 1)) :
          Set (GridVertex (3 * (k + 1) + 1) (3 * (k + 1) + 1))) := by
      rw [← Finset.coe_union, htarget]
    simp only [order, Finset.toList_toFinset]
    rw [htargetSet]
    exact htargetAcyclic
  refine {
    embedding := e
    coreAcyclic := hcoreAcyclic
    frameOrder := order
    frame_nodup := hnodup
    frame_disjoint := hdisj
    frame_card := ?_
    covers := ?_
    sequential := hseq }
  · simpa [order, frame, core, e, residueOneReverseFrameOrder] using
      residueOneReverseFrameOrder_length k hk
  · simpa [order, frame, core, e] using htarget

/-- Explicit forced-set reverse recurrence in residue one. -/
theorem forcedResidueOne_card_succ (k : Nat) (hk : 1 ≤ k) :
    (forcedResidueOne (k + 1)).card =
      (forcedResidueOne k).card + 2 * (3 * (k + 1) + 1) :=
  (residueOneReverseFrameTemplate k hk).card_newForced

/-- The explicit residue-one construction score advances by the full reverse
frame gain.  This is a lower bound from the displayed construction, not a
claim that the old construction is maximal. -/
theorem residueOne_constructionScore_lower_step (k : Nat) (hk : 1 ≤ k) :
    3 * k ^ 2 + 5 * k + 2 * (3 * (k + 1) + 1) ≤
      maxPreserved (3 * (k + 1) + 1) (3 * (k + 1) + 1) := by
  rw [← forcedResidueOne_card k hk]
  rw [← (residueOneReverseFrameTemplate k hk).card_newForced]
  exact ReverseFrameTemplate.card_newForced_le_maxPreserved
    (residueOneReverseFrameTemplate k hk)
    (Nat.succ_le_succ (Nat.zero_le _))
    (Nat.succ_le_succ (Nat.zero_le _))

/-- If the old explicit residue-one forced set attains the old maximum, reverse
insertion gives the corresponding true lower recurrence for the operational
maxima.  No unconditional maximum recurrence is asserted. -/
theorem maxPreserved_residueOne_lower_recurrence_of_forcedResidueOne_exact
    (k : Nat) (hk : 1 ≤ k)
    (hOld : (forcedResidueOne k).card =
      maxForcedAcyclic (3 * k + 1) (3 * k + 1)) :
    maxPreserved (3 * k + 1) (3 * k + 1) +
        2 * (3 * (k + 1) + 1) ≤
      maxPreserved (3 * (k + 1) + 1) (3 * (k + 1) + 1) := by
  exact ReverseFrameTemplate.maxPreserved_add_gain_le_maxPreserved_of_card_oldForced_eq
      (residueOneReverseFrameTemplate k hk)
      (Nat.succ_le_succ (Nat.zero_le _))
      (Nat.succ_le_succ (Nat.zero_le _))
      (Nat.succ_le_succ (Nat.zero_le _))
      (Nat.succ_le_succ (Nat.zero_le _)) hOld

end GridGraphs
