import GridGraphs.Surgery.ThreeFrameSurgery
import GridGraphs.Surgery.GridCrop

/-!
# The sixteen total-three crops

This file indexes all ways to remove three rows and three columns between the
opposite sides of a square grid.  It also records the abstract finite-family
selection step used after a separate geometric gain estimate is available.
-/

namespace GridGraphs

open Finset

/-- The sixteen choices of top and left offsets for a total-three crop. -/
abbrev TotalThreeCrop := Fin 4 × Fin 4

namespace TotalThreeCrop

/-- Number of rows removed above the crop. -/
abbrev top (c : TotalThreeCrop) : Nat := c.1.val

/-- Number of rows removed below the crop. -/
abbrev bottom (c : TotalThreeCrop) : Nat := 3 - c.1.val

/-- Number of columns removed to the left of the crop. -/
abbrev left (c : TotalThreeCrop) : Nat := c.2.val

/-- Number of columns removed to the right of the crop. -/
abbrev right (c : TotalThreeCrop) : Nat := 3 - c.2.val

@[simp] theorem top_add_bottom (c : TotalThreeCrop) :
    c.top + c.bottom = 3 := by
  simp only [top, bottom]
  omega

@[simp] theorem left_add_right (c : TotalThreeCrop) :
    c.left + c.right = 3 := by
  simp only [left, right]
  omega

/-- A crop index is determined extensionally by its top and left offsets. -/
@[ext] theorem ext {c d : TotalThreeCrop} (htop : c.top = d.top)
    (hleft : c.left = d.left) : c = d := by
  apply Prod.ext <;> apply Fin.ext
  · exact htop
  · exact hleft

end TotalThreeCrop

@[simp] theorem card_totalThreeCrop : Fintype.card TotalThreeCrop = 16 := by
  simp [TotalThreeCrop, Fintype.card_prod]

/-- The contiguous `(n - 3) x (n - 3)` grid selected by a crop index. -/
abbrev totalThreeCropEmbedding (n : Nat) (c : TotalThreeCrop) (hn : 3 ≤ n) :
    GridVertex (n - 3) (n - 3) ↪ GridVertex n n :=
  threeSideCropEmbedding n c.top c.bottom c.left c.right hn
    c.top_add_bottom c.left_add_right

/-- Forced vertices surviving the indexed crop. -/
abbrev totalThreeCropForcedSet (n : Nat) (c : TotalThreeCrop) (hn : 3 ≤ n)
    (F : Finset (GridVertex n n)) : Finset (GridVertex (n - 3) (n - 3)) :=
  cropForcedSet (totalThreeCropEmbedding n c hn) F

/-- Forced vertices lost from the frame of the indexed crop. -/
abbrev totalThreeCropFrameLoss (n : Nat) (c : TotalThreeCrop) (hn : 3 ≤ n)
    (F : Finset (GridVertex n n)) : Nat :=
  cropFrameLoss (totalThreeCropEmbedding n c hn) F

/-- Frame loss after deleting local forced vertices and adding replacements. -/
abbrev totalThreeCropDeleteAddNetLoss (n : Nat) (c : TotalThreeCrop)
    (hn : 3 ≤ n) (F : Finset (GridVertex n n))
    (D R : Finset (GridVertex (n - 3) (n - 3))) : Nat :=
  deleteAddNetFrameLoss (totalThreeCropEmbedding n c hn) F D R

/-- The gain required from a crop beyond its free `2n` frame allowance. -/
abbrev totalThreeCropDemand (n : Nat) (c : TotalThreeCrop) (hn : 3 ≤ n)
    (F : Finset (GridVertex n n)) : Nat :=
  totalThreeCropFrameLoss n c hn F - 2 * n

/-- Abstract finite-family pigeonhole principle for crop gains.  The sum
hypothesis is the geometric input; this theorem only selects one index. -/
theorem exists_totalThreeCrop_gain_ge_demand
    (n : Nat) (hn : 3 ≤ n) (F : Finset (GridVertex n n))
    (availableGain : TotalThreeCrop → Nat)
    (hindex : (Finset.univ : Finset TotalThreeCrop).Nonempty)
    (hsum : (∑ c : TotalThreeCrop, totalThreeCropDemand n c hn F) ≤
      ∑ c : TotalThreeCrop, availableGain c) :
    ∃ c : TotalThreeCrop,
      totalThreeCropDemand n c hn F ≤ availableGain c := by
  by_contra hnone
  push Not at hnone
  have hlt : (∑ c : TotalThreeCrop, availableGain c) <
      ∑ c : TotalThreeCrop, totalThreeCropDemand n c hn F := by
    apply Finset.sum_lt_sum
    · intro c _
      exact Nat.le_of_lt (hnone c)
    · obtain ⟨c, hc⟩ := hindex
      exact ⟨c, hc, hnone c⟩
  omega

/-- The concrete sixteen-crop index family is nonempty. -/
theorem totalThreeCrop_univ_nonempty :
    (Finset.univ : Finset TotalThreeCrop).Nonempty := by
  exact ⟨(0, 0), by simp⟩

end GridGraphs
