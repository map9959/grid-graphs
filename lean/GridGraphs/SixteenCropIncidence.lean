import GridGraphs.SixteenCropSurgery
import GridGraphs.GridCrop

/-!
# Exact incidence counts for the sixteen total-three crops

Every statement here is unconditional: it only counts which ambient vertices
belong to which of the sixteen contiguous crops.
-/

namespace GridGraphs

open Finset

/-- Number of top offsets whose row interval contains `r`. -/
def rowOffsetMultiplicity (n : Nat) (_hn : 3 ≤ n) (r : Fin n) : Nat :=
  ((Finset.univ : Finset (Fin 4)).filter fun t =>
    t.val ≤ r.val ∧ r.val < t.val + (n - 3)).card

/-- Number of left offsets whose column interval contains `s`. -/
def columnOffsetMultiplicity (n : Nat) (_hn : 3 ≤ n) (s : Fin n) : Nat :=
  ((Finset.univ : Finset (Fin 4)).filter fun l =>
    l.val ≤ s.val ∧ s.val < l.val + (n - 3)).card

/-- For grids of side at least seven, row incidence rises from one to four,
stays four on the common core, and falls symmetrically back to one. -/
theorem rowOffsetMultiplicity_eq_min (n : Nat) (hn : 7 ≤ n) (r : Fin n) :
    rowOffsetMultiplicity n ((by simp : 3 ≤ 7).trans hn) r =
      min 4 (min (r.val + 1) (n - r.val)) := by
  have hn3 : 3 ≤ n := (by simp : 3 ≤ 7).trans hn
  have hcrop4 : 4 ≤ n - 3 := Nat.le_sub_of_add_le (by simpa using hn)
  by_cases htop : r.val < 3
  · have hr4 : r.val < 4 := htop.trans (by simp)
    let b : Fin 4 := ⟨r.val, hr4⟩
    have hrCrop : r.val < n - 3 :=
      htop.trans_le ((by simp : 3 ≤ 4).trans hcrop4)
    have hfilter :
        (Finset.univ : Finset (Fin 4)).filter (fun t =>
            t.val ≤ r.val ∧ r.val < t.val + (n - 3)) = Finset.Iic b := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic]
      change (t.val ≤ r.val ∧ r.val < t.val + (n - 3)) ↔ t.val ≤ b.val
      constructor
      · exact fun h => h.1
      · intro ht
        exact ⟨ht, hrCrop.trans_le (Nat.le_add_left (n - 3) t.val)⟩
    have hcard : rowOffsetMultiplicity n hn3 r = r.val + 1 := by
      rw [rowOffsetMultiplicity, hfilter, Fin.card_Iic]
    have hleft : r.val + 1 ≤ 4 := Nat.succ_le_iff.mpr hr4
    have hrn : r.val + 4 ≤ n :=
      (Nat.le_of_lt (Nat.add_lt_add_right htop 4)).trans hn
    have hright : 4 ≤ n - r.val := Nat.le_sub_of_add_le (by
      simpa [Nat.add_comm] using hrn)
    have hinner : r.val + 1 ≤ n - r.val := hleft.trans hright
    rw [hcard, Nat.min_eq_left hinner, Nat.min_eq_right hleft]
  · have hthree : 3 ≤ r.val := Nat.le_of_not_gt htop
    by_cases hbottom : n - 3 ≤ r.val
    · let aVal := r.val - (n - 3)
      have hnSplit : n - 3 + 3 = n := Nat.sub_add_cancel hn3
      have hrSplit : n - 3 + aVal = r.val := Nat.add_sub_of_le hbottom
      have hnLt : n < n - 3 + 4 := by
        rw [← hnSplit]
        simp
      have ha4 : aVal < 4 := (Nat.sub_lt_iff_lt_add hbottom).mpr (by
        rw [Nat.add_comm]
        exact r.isLt.trans hnLt)
      let a : Fin 4 := ⟨aVal, ha4⟩
      have hfilter :
          (Finset.univ : Finset (Fin 4)).filter (fun t =>
              t.val ≤ r.val ∧ r.val < t.val + (n - 3)) = Finset.Ioi a := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ioi]
        change (t.val ≤ r.val ∧ r.val < t.val + (n - 3)) ↔ a.val < t.val
        have ht3 : t.val ≤ 3 := Nat.lt_succ_iff.mp t.isLt
        have htr : t.val ≤ r.val := ht3.trans hthree
        have hright : r.val < t.val + (n - 3) ↔ a.val < t.val := by
          rw [← hrSplit]
          change n - 3 + a.val < t.val + (n - 3) ↔ _
          rw [Nat.add_comm t.val (n - 3), Nat.add_lt_add_iff_left]
        exact ⟨fun h => hright.mp h.2, fun h => ⟨htr, hright.mpr h⟩⟩
      have hcard : rowOffsetMultiplicity n hn3 r = n - r.val := by
        rw [rowOffsetMultiplicity, hfilter, Fin.card_Ioi]
        change 3 - aVal = n - r.val
        symm
        calc
          n - r.val = (n - 3 + 3) - r.val := by rw [hnSplit]
          _ = (n - 3 + 3) - (n - 3 + aVal) := by rw [hrSplit]
          _ = 3 - aVal := Nat.add_sub_add_left (n - 3) 3 aVal
      have hright3 : n - r.val ≤ 3 := by
        calc
          n - r.val = (n - 3 + 3) - r.val := by rw [hnSplit]
          _ = (n - 3 + 3) - (n - 3 + aVal) := by rw [hrSplit]
          _ = 3 - aVal := Nat.add_sub_add_left (n - 3) 3 aVal
          _ ≤ 3 := Nat.sub_le 3 aVal
      have hright4 : n - r.val ≤ 4 := hright3.trans (by simp)
      have hrightRow : n - r.val ≤ r.val + 1 :=
        hright3.trans (hthree.trans (Nat.le_succ r.val))
      rw [hcard, Nat.min_eq_right hrightRow, Nat.min_eq_right hright4]
    · have hrCrop : r.val < n - 3 := Nat.lt_of_not_ge hbottom
      have hfilter :
          (Finset.univ : Finset (Fin 4)).filter (fun t =>
              t.val ≤ r.val ∧ r.val < t.val + (n - 3)) = Finset.univ := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [iff_true]
        have ht3 : t.val ≤ 3 := Nat.lt_succ_iff.mp t.isLt
        exact ⟨ht3.trans hthree,
          hrCrop.trans_le (Nat.le_add_left (n - 3) t.val)⟩
      have hcard : rowOffsetMultiplicity n hn3 r = 4 := by
        rw [rowOffsetMultiplicity, hfilter, Finset.card_univ, Fintype.card_fin]
      have hleft : 4 ≤ r.val + 1 := Nat.succ_le_succ hthree
      have hrn : r.val + 4 ≤ n := by
        apply Nat.succ_le_iff.mpr
        simpa [Nat.sub_add_cancel hn3, Nat.add_assoc] using
          Nat.add_lt_add_right hrCrop 3
      have hright : 4 ≤ n - r.val := Nat.le_sub_of_add_le (by
        simpa [Nat.add_comm] using hrn)
      rw [hcard, Nat.min_eq_left (le_min hleft hright)]

/-- The same distance-to-boundary formula holds for column offsets. -/
theorem columnOffsetMultiplicity_eq_min (n : Nat) (hn : 7 ≤ n) (s : Fin n) :
    columnOffsetMultiplicity n ((by simp : 3 ≤ 7).trans hn) s =
      min 4 (min (s.val + 1) (n - s.val)) := by
  exact rowOffsetMultiplicity_eq_min n hn s

/-- A coordinate on either outer boundary belongs to exactly one offset. -/
theorem rowOffsetMultiplicity_eq_one_of_boundary
    (n : Nat) (hn : 7 ≤ n) (r : Fin n)
    (hr : r.val = 0 ∨ r.val + 1 = n) :
    rowOffsetMultiplicity n ((by simp : 3 ≤ 7).trans hn) r = 1 := by
  rw [rowOffsetMultiplicity_eq_min n hn r]
  rcases hr with htop | hbottom
  · have hn1 : 1 ≤ n := (by simp : 1 ≤ 7).trans hn
    simp [htop, hn1]
  · have hdist : n - r.val = 1 := by
      calc
        n - r.val = (r.val + 1) - r.val := by rw [hbottom]
        _ = 1 := by simp
    simp [hdist]

/-- The corresponding outer-boundary statement for columns. -/
theorem columnOffsetMultiplicity_eq_one_of_boundary
    (n : Nat) (hn : 7 ≤ n) (s : Fin n)
    (hs : s.val = 0 ∨ s.val + 1 = n) :
    columnOffsetMultiplicity n ((by simp : 3 ≤ 7).trans hn) s = 1 := by
  exact rowOffsetMultiplicity_eq_one_of_boundary n hn s hs

/-- Vertices at distance at least three from every side form the intersection
of all sixteen total-three crops. -/
def inStrictTotalThreeCommonCore (n : Nat) (v : GridVertex n n) : Prop :=
  3 ≤ v.1.val ∧ v.1.val + 4 ≤ n ∧
    3 ≤ v.2.val ∧ v.2.val + 4 ≤ n

/-- Number of the sixteen crops containing an ambient grid vertex. -/
def cropSurvivalMultiplicity (n : Nat) (hn : 3 ≤ n)
    (v : GridVertex n n) : Nat :=
  ((Finset.univ : Finset TotalThreeCrop).filter fun c =>
    v ∈ Set.range (totalThreeCropEmbedding n c hn)).card

theorem mem_range_totalThreeCropEmbedding_iff
    (n : Nat) (hn : 3 ≤ n) (c : TotalThreeCrop) (v : GridVertex n n) :
    v ∈ Set.range (totalThreeCropEmbedding n c hn) ↔
      c.top ≤ v.1.val ∧ v.1.val < c.top + (n - 3) ∧
        c.left ≤ v.2.val ∧ v.2.val < c.left + (n - 3) := by
  constructor
  · rintro ⟨w, rfl⟩
    simp only [totalThreeCropEmbedding, threeSideCropEmbedding,
      gridOffsetEmbedding_fst_val, gridOffsetEmbedding_snd_val]
    exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left w.1.isLt _,
      Nat.le_add_right _ _, Nat.add_lt_add_left w.2.isLt _⟩
  · rintro ⟨hr₀, hr₁, hc₀, hc₁⟩
    let w : GridVertex (n - 3) (n - 3) :=
      (⟨v.1.val - c.top, (Nat.sub_lt_iff_lt_add hr₀).mpr (by
          rw [Nat.add_comm (n - 3) c.top]
          exact hr₁)⟩,
        ⟨v.2.val - c.left, (Nat.sub_lt_iff_lt_add hc₀).mpr (by
          rw [Nat.add_comm (n - 3) c.left]
          exact hc₁)⟩)
    refine ⟨w, ?_⟩
    apply Prod.ext
    · apply Fin.ext
      simp only [totalThreeCropEmbedding, threeSideCropEmbedding,
        gridOffsetEmbedding_fst_val, w]
      exact Nat.add_sub_of_le hr₀
    · apply Fin.ext
      simp only [totalThreeCropEmbedding, threeSideCropEmbedding,
        gridOffsetEmbedding_snd_val, w]
      exact Nat.add_sub_of_le hc₀

/-- Row and column offset choices are independent. -/
theorem cropSurvivalMultiplicity_eq_mul (n : Nat) (hn : 3 ≤ n)
    (v : GridVertex n n) :
    cropSurvivalMultiplicity n hn v =
      rowOffsetMultiplicity n hn v.1 * columnOffsetMultiplicity n hn v.2 := by
  classical
  let rows := (Finset.univ : Finset (Fin 4)).filter fun t =>
    t.val ≤ v.1.val ∧ v.1.val < t.val + (n - 3)
  let columns := (Finset.univ : Finset (Fin 4)).filter fun l =>
    l.val ≤ v.2.val ∧ v.2.val < l.val + (n - 3)
  have hfilter :
      (Finset.univ : Finset TotalThreeCrop).filter (fun c =>
          v ∈ Set.range (totalThreeCropEmbedding n c hn)) =
        rows ×ˢ columns := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_product, rows, columns,
      mem_range_totalThreeCropEmbedding_iff]
    constructor
    · rintro ⟨hr₀, hr₁, hc₀, hc₁⟩
      exact ⟨⟨hr₀, hr₁⟩, hc₀, hc₁⟩
    · rintro ⟨⟨hr₀, hr₁⟩, hc₀, hc₁⟩
      exact ⟨hr₀, hr₁, hc₀, hc₁⟩
  rw [cropSurvivalMultiplicity, hfilter, Finset.card_product]
  rfl

/-- Closed two-dimensional survival formula obtained from independent row and
column choices. -/
theorem cropSurvivalMultiplicity_eq_min_mul_min
    (n : Nat) (hn : 7 ≤ n) (v : GridVertex n n) :
    cropSurvivalMultiplicity n ((by simp : 3 ≤ 7).trans hn) v =
      min 4 (min (v.1.val + 1) (n - v.1.val)) *
        min 4 (min (v.2.val + 1) (n - v.2.val)) := by
  rw [cropSurvivalMultiplicity_eq_mul,
    rowOffsetMultiplicity_eq_min n hn,
    columnOffsetMultiplicity_eq_min n hn]

/-- Every strict common-core vertex survives all sixteen crops. -/
theorem cropSurvivalMultiplicity_eq_sixteen_of_mem_commonCore
    (n : Nat) (hn : 7 ≤ n) (v : GridVertex n n)
    (hv : inStrictTotalThreeCommonCore n v) :
    cropSurvivalMultiplicity n ((by simp : 3 ≤ 7).trans hn) v = 16 := by
  rcases hv with ⟨hr₀, hr₁, hc₀, hc₁⟩
  have hrRight : 4 ≤ n - v.1.val := Nat.le_sub_of_add_le (by
    simpa [Nat.add_comm] using hr₁)
  have hcRight : 4 ≤ n - v.2.val := Nat.le_sub_of_add_le (by
    simpa [Nat.add_comm] using hc₁)
  have hrLeft : 4 ≤ v.1.val + 1 := Nat.succ_le_succ hr₀
  have hcLeft : 4 ≤ v.2.val + 1 := Nat.succ_le_succ hc₀
  rw [cropSurvivalMultiplicity_eq_min_mul_min n hn]
  rw [Nat.min_eq_left (le_min hrLeft hrRight),
    Nat.min_eq_left (le_min hcLeft hcRight)]

/-- A strict common-core vertex contributes no summand to aggregate frame
loss. -/
theorem aggregateFrameLossTerm_eq_zero_of_mem_commonCore
    (n : Nat) (hn : 7 ≤ n) (v : GridVertex n n)
    (hv : inStrictTotalThreeCommonCore n v) :
    16 - cropSurvivalMultiplicity n ((by simp : 3 ≤ 7).trans hn) v = 0 := by
  rw [cropSurvivalMultiplicity_eq_sixteen_of_mem_commonCore n hn v hv]

private theorem totalThreeCropForcedSet_card_eq_filter
    (n : Nat) (hn : 3 ≤ n) (F : Finset (GridVertex n n))
    (c : TotalThreeCrop) :
    (totalThreeCropForcedSet n c hn F).card =
      (F.filter fun v =>
        v ∈ Set.range (totalThreeCropEmbedding n c hn)).card := by
  classical
  let e := totalThreeCropEmbedding n c hn
  have himage : Finset.image e (cropForcedSet e F) =
      F.filter fun v => v ∈ Set.range e := by
    ext v
    constructor
    · intro hv
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
      exact Finset.mem_filter.mpr
        ⟨(mem_cropForcedSet e F u).mp hu, ⟨u, rfl⟩⟩
    · intro hv
      obtain ⟨hvF, u, rfl⟩ := Finset.mem_filter.mp hv
      exact Finset.mem_image.mpr
        ⟨u, (mem_cropForcedSet e F u).mpr hvF, rfl⟩
  change (cropForcedSet e F).card = _
  rw [← himage, Finset.card_image_of_injective _ e.injective]

/-- Exact double counting of incidences between forced vertices and crops. -/
theorem sum_totalThreeCropForcedSet_card
    (n : Nat) (hn : 3 ≤ n) (F : Finset (GridVertex n n)) :
    (∑ c : TotalThreeCrop, (totalThreeCropForcedSet n c hn F).card) =
      ∑ v ∈ F, cropSurvivalMultiplicity n hn v := by
  classical
  simp_rw [totalThreeCropForcedSet_card_eq_filter]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  rw [cropSurvivalMultiplicity, Finset.card_eq_sum_ones,
    Finset.sum_filter]

/-- Exact double counting of all forced vertices deleted by crop frames. -/
theorem sum_totalThreeCropFrameLoss
    (n : Nat) (hn : 3 ≤ n) (F : Finset (GridVertex n n)) :
    (∑ c : TotalThreeCrop, totalThreeCropFrameLoss n c hn F) =
      ∑ v ∈ F, (16 - cropSurvivalMultiplicity n hn v) := by
  classical
  have hcrops := sum_totalThreeCropForcedSet_card n hn F
  have hleft :
      (∑ c : TotalThreeCrop, (totalThreeCropForcedSet n c hn F).card) +
          ∑ c : TotalThreeCrop, totalThreeCropFrameLoss n c hn F =
        16 * F.card := by
    calc
      (∑ c : TotalThreeCrop, (totalThreeCropForcedSet n c hn F).card) +
          ∑ c : TotalThreeCrop, totalThreeCropFrameLoss n c hn F =
          ∑ c : TotalThreeCrop,
            ((totalThreeCropForcedSet n c hn F).card +
              totalThreeCropFrameLoss n c hn F) :=
            (Finset.sum_add_distrib).symm
      _ =
          ∑ _c : TotalThreeCrop, F.card := by
            apply Finset.sum_congr rfl
            intro c _
            exact (card_eq_crop_add_frameLoss
              (totalThreeCropEmbedding n c hn) F).symm
      _ = 16 * F.card := by simp
  have hmult_le (v : GridVertex n n) :
      cropSurvivalMultiplicity n hn v ≤ 16 := by
    calc
      cropSurvivalMultiplicity n hn v ≤
          (Finset.univ : Finset TotalThreeCrop).card :=
        Finset.card_filter_le _ _
      _ = 16 := by
        rw [Finset.card_univ, card_totalThreeCrop]
  have hright :
      (∑ v ∈ F, cropSurvivalMultiplicity n hn v) +
          (∑ v ∈ F, (16 - cropSurvivalMultiplicity n hn v)) =
        16 * F.card := by
    calc
      (∑ v ∈ F, cropSurvivalMultiplicity n hn v) +
          (∑ v ∈ F, (16 - cropSurvivalMultiplicity n hn v)) =
          ∑ v ∈ F, (cropSurvivalMultiplicity n hn v +
            (16 - cropSurvivalMultiplicity n hn v)) :=
        (Finset.sum_add_distrib).symm
      _ = ∑ _v ∈ F, 16 := by
        apply Finset.sum_congr rfl
        intro v _
        exact Nat.add_sub_of_le (hmult_le v)
      _ = 16 * F.card := by simp [mul_comm]
  rw [hcrops] at hleft
  exact Nat.add_left_cancel (hleft.trans hright.symm)

/-- A forced set contained in the strict common core has zero aggregate frame
loss across all sixteen crops. -/
theorem sum_totalThreeCropFrameLoss_eq_zero_of_commonCore
    (n : Nat) (hn : 7 ≤ n) (F : Finset (GridVertex n n))
    (hF : ∀ v ∈ F, inStrictTotalThreeCommonCore n v) :
    (∑ c : TotalThreeCrop,
      totalThreeCropFrameLoss n c ((by simp : 3 ≤ 7).trans hn) F) = 0 := by
  rw [sum_totalThreeCropFrameLoss]
  apply Finset.sum_eq_zero
  intro v hv
  exact aggregateFrameLossTerm_eq_zero_of_mem_commonCore n hn v (hF v hv)

end GridGraphs
