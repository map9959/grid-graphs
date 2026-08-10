import GridGraphs.SixteenCropSurgery
import GridGraphs.SequentialToothSurgery
import GridGraphs.ForcedMaximum

/-!
# Upper recurrence from sixteen crop surgeries

This file packages the delete/add data for each total-three crop.  The summed
gain inequality remains an explicit geometric hypothesis.
-/

namespace GridGraphs

open Finset SimpleGraph

/-- A certified delete/add surgery for one total-three crop. -/
structure TotalThreeCropDeleteAddArgument
    (n : Nat) (hn : 3 ≤ n) (F : Finset (GridVertex n n))
    (c : TotalThreeCrop) where
  D : Finset (GridVertex (n - 3) (n - 3))
  R : Finset (GridVertex (n - 3) (n - 3))
  deletion_subset : D ⊆ totalThreeCropForcedSet n c hn F
  replacement_disjoint :
    Disjoint (totalThreeCropForcedSet n c hn F \ D) R
  final_isAcyclic :
    (forcedEdgeGraph (gridGraph (n - 3) (n - 3))
      (↑((totalThreeCropForcedSet n c hn F \ D) ∪ R) :
        Set (GridVertex (n - 3) (n - 3)))).IsAcyclic
  deletion_card_le_replacement_card : D.card ≤ R.card

/-- The exact nonnegative gain supplied by a crop surgery. -/
def TotalThreeCropDeleteAddArgument.gain
    {n : Nat} {hn : 3 ≤ n} {F : Finset (GridVertex n n)}
    {c : TotalThreeCrop}
    (argument : TotalThreeCropDeleteAddArgument n hn F c) : Nat :=
  argument.R.card - argument.D.card

/-- Delete/add surgery data indexed over all sixteen total-three crops. -/
abbrev TotalThreeCropDeleteAddFamily
    (n : Nat) (hn : 3 ≤ n) (F : Finset (GridVertex n n)) :=
  ∀ c : TotalThreeCrop, TotalThreeCropDeleteAddArgument n hn F c

/-- The aggregate gain hypothesis selects a crop whose repaired frame costs at
most `2 * n`. -/
theorem exists_totalThreeCrop_frameLoss_add_deletion_le
    (n : Nat) (hn : 3 ≤ n) (F : Finset (GridVertex n n))
    (family : TotalThreeCropDeleteAddFamily n hn F)
    (haggregate :
      (∑ c : TotalThreeCrop, totalThreeCropDemand n c hn F) ≤
        ∑ c : TotalThreeCrop, (family c).gain) :
    ∃ c : TotalThreeCrop,
      totalThreeCropFrameLoss n c hn F + (family c).D.card ≤
        2 * n + (family c).R.card := by
  obtain ⟨c, hc⟩ := exists_totalThreeCrop_gain_ge_demand
    n hn F (fun c => (family c).gain) totalThreeCrop_univ_nonempty haggregate
  refine ⟨c, ?_⟩
  have hnonnegative := (family c).deletion_card_le_replacement_card
  unfold totalThreeCropDemand TotalThreeCropDeleteAddArgument.gain at hc
  have hframe := Nat.sub_le_iff_le_add.mp hc
  calc
    totalThreeCropFrameLoss n c hn F + (family c).D.card ≤
        ((family c).R.card - (family c).D.card + 2 * n) +
          (family c).D.card := Nat.add_le_add_right hframe _
    _ = ((family c).R.card - (family c).D.card) +
          (2 * n + (family c).D.card) := Nat.add_assoc _ _ _
    _ = 2 * n + ((family c).R.card - (family c).D.card +
          (family c).D.card) := Nat.add_left_comm _ _ _
    _ = 2 * n + (family c).R.card := by
      rw [Nat.sub_add_cancel hnonnegative]

/-- A selected certified crop with repaired frame cost at most `2 * n` bounds
the cardinality of the original forced set. -/
theorem card_le_maxForcedAcyclic_add_two_mul_of_totalThreeCrop
    (n : Nat) (hn : 3 ≤ n) (F : Finset (GridVertex n n))
    (c : TotalThreeCrop)
    (argument : TotalThreeCropDeleteAddArgument n hn F c)
    (hbalance : totalThreeCropFrameLoss n c hn F + argument.D.card ≤
      2 * n + argument.R.card) :
    F.card ≤ maxForcedAcyclic (n - 3) (n - 3) + 2 * n := by
  have hcrop := card_eq_crop_add_frameLoss
    (totalThreeCropEmbedding n c hn) F
  have hdelete := Finset.card_sdiff_add_card_eq_card argument.deletion_subset
  have hfinal :
      ((totalThreeCropForcedSet n c hn F \ argument.D) ∪ argument.R).card ≤
        maxForcedAcyclic (n - 3) (n - 3) := by
    apply Finset.le_sup (f := Finset.card)
    exact mem_acyclicForcedSets.mpr argument.final_isAcyclic
  change F.card = (totalThreeCropForcedSet n c hn F).card +
    totalThreeCropFrameLoss n c hn F at hcrop
  rw [Finset.card_union_of_disjoint argument.replacement_disjoint] at hfinal
  apply Nat.le_of_add_le_add_right
  calc
    F.card + argument.R.card =
        ((totalThreeCropForcedSet n c hn F).card +
          totalThreeCropFrameLoss n c hn F) + argument.R.card := by rw [hcrop]
    _ = (((totalThreeCropForcedSet n c hn F \ argument.D).card +
          argument.D.card) + totalThreeCropFrameLoss n c hn F) +
          argument.R.card := by rw [hdelete]
    _ = (totalThreeCropForcedSet n c hn F \ argument.D).card +
        (argument.D.card +
          (totalThreeCropFrameLoss n c hn F + argument.R.card)) :=
      (Nat.add_assoc _ _ _).trans (Nat.add_assoc _ _ _)
    _ = (totalThreeCropForcedSet n c hn F \ argument.D).card +
        (argument.R.card +
          (totalThreeCropFrameLoss n c hn F + argument.D.card)) := by
      apply congrArg ((totalThreeCropForcedSet n c hn F \ argument.D).card + ·)
      exact (Nat.add_comm _ _).trans
        ((Nat.add_assoc _ _ _).trans (Nat.add_left_comm _ _ _))
    _ = ((totalThreeCropForcedSet n c hn F \ argument.D).card +
          argument.R.card) +
        (totalThreeCropFrameLoss n c hn F + argument.D.card) :=
      (Nat.add_assoc _ _ _).symm
    _ ≤ ((totalThreeCropForcedSet n c hn F \ argument.D).card +
          argument.R.card) + (2 * n + argument.R.card) :=
      Nat.add_le_add_left hbalance _
    _ = (((totalThreeCropForcedSet n c hn F \ argument.D).card +
          argument.R.card) + 2 * n) + argument.R.card :=
      (Nat.add_assoc _ _ _).symm
    _ ≤ (maxForcedAcyclic (n - 3) (n - 3) + 2 * n) +
          argument.R.card :=
      Nat.add_le_add_right (Nat.add_le_add_right hfinal _) _

/-- A maximum forced set and the explicit aggregate geometric inequality imply
the diagonal upper recurrence. -/
theorem maxForcedAcyclic_sixteenCrop_upper_recurrence_of_maximum
    (n : Nat) (hn : 3 ≤ n) (F : Finset (GridVertex n n))
    (hmax : F.card = maxForcedAcyclic n n)
    (family : TotalThreeCropDeleteAddFamily n hn F)
    (haggregate :
      (∑ c : TotalThreeCrop, totalThreeCropDemand n c hn F) ≤
        ∑ c : TotalThreeCrop, (family c).gain) :
    maxForcedAcyclic n n ≤
      maxForcedAcyclic (n - 3) (n - 3) + 2 * n := by
  obtain ⟨c, hbalance⟩ :=
    exists_totalThreeCrop_frameLoss_add_deletion_le n hn F family haggregate
  rw [← hmax]
  exact card_le_maxForcedAcyclic_add_two_mul_of_totalThreeCrop
    n hn F c (family c) hbalance

/-- Spanning-tree form of the sixteen-crop upper recurrence. -/
theorem maxPreserved_sixteenCrop_upper_recurrence_of_maximum
    (n : Nat) (hn : 4 ≤ n) (F : Finset (GridVertex n n))
    (hmax : F.card = maxForcedAcyclic n n)
    (family : TotalThreeCropDeleteAddFamily n (le_trans (Nat.le_succ 3) hn) F)
    (haggregate :
      (∑ c : TotalThreeCrop,
        totalThreeCropDemand n c (le_trans (Nat.le_succ 3) hn) F) ≤
        ∑ c : TotalThreeCrop, (family c).gain) :
    maxPreserved n n ≤ maxPreserved (n - 3) (n - 3) + 2 * n := by
  have hone : 1 ≤ n := le_trans (Nat.succ_le_succ (Nat.zero_le 3)) hn
  have hsmall : 1 ≤ n - 3 := Nat.le_sub_of_add_le hn
  rw [maxPreserved_eq_maxForcedAcyclic hone hone,
    maxPreserved_eq_maxForcedAcyclic hsmall hsmall]
  exact maxForcedAcyclic_sixteenCrop_upper_recurrence_of_maximum
    n (le_trans (Nat.le_succ 3) hn) F hmax family haggregate

end GridGraphs
