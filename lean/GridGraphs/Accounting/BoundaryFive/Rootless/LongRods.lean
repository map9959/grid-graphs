import GridGraphs.Accounting.BoundaryFive.Rootless.MissingTriples

/-!
# Long interval rods and the endpoint contradiction

This is a coordinate packing theorem. Its hypotheses are interval geometry,
local contact/six-cycle restrictions, interior axes, and four distinct short
corner rods on the two corner-adjacent axes. Neither longness, axis spacing,
missing triples, nor a deficit inequality is assumed. RodInventory and
CornerRoots supply the complete actual-grid bridge and the four corner records.
-/

namespace GridGraphs.BoundaryFive.Rootless

open Finset

structure Rod (m : Nat) where
  horizontal : Bool
  axis : Fin m
  lo : Fin m
  hi : Fin m
  ordered : lo ≤ hi

def Rod.span {m : Nat} (R : Rod m) : Finset Nat := Icc R.lo.val R.hi.val

def Rod.length {m : Nat} (R : Rod m) : Nat := R.hi.val + 1 - R.lo.val

def Rod.point {m : Nat} (R : Rod m) (j : Nat) : Nat × Nat :=
  if R.horizontal = true then (R.axis.val, j) else (j, R.axis.val)

theorem Rod.span_card {m : Nat} (R : Rod m) : R.span.card = R.length := by
  simp [Rod.span, Rod.length, Nat.card_Icc]

theorem Rod.span_subset {m : Nat} (R : Rod m) : R.span ⊆ range m := by
  intro x hx
  have hx' := mem_Icc.mp hx
  exact mem_range.mpr (by have := R.hi.isLt; omega)

/-- Different induced carriers cannot meet, be grid-adjacent, or occupy
opposite cell corners. This condition records precisely those local contacts. -/
def Rod.Separated {m : Nat} (R S : Rod m) : Prop :=
  ∀ x ∈ R.span, ∀ y ∈ S.span,
    (R.point x).1 + 1 < (S.point y).1 ∨ (S.point y).1 + 1 < (R.point x).1 ∨
    (R.point x).2 + 1 < (S.point y).2 ∨ (S.point y).2 + 1 < (R.point x).2

/-- Long intervals contain the same two central positions, including both
parities of m. The strict threshold is (m+1)/2, not m/2. -/
theorem Rod.long_central {m : Nat} (R : Rod m) (hlong : m + 1 < 2 * R.length) :
    (m - 1) / 2 ∈ R.span ∧ (m - 1) / 2 + 1 ∈ R.span := by
  have hlo := R.lo.isLt
  have hhi := R.hi.isLt
  have hord : R.lo.val ≤ R.hi.val := R.ordered
  simp only [Rod.span, mem_Icc]
  dsimp [Rod.length] at hlong
  omega

/-- Parallel long rods are three-spaced. The distance-two input is the
standard rectangle six-cycle bound, not a spacing assumption. -/
theorem Rod.long_parallel_spacing {m : Nat} (R S : Rod m)
    (hR : m + 1 < 2 * R.length) (hS : m + 1 < 2 * S.length)
    (hdir : R.horizontal = S.horizontal) (hsep : R.Separated S)
    (htwo : R.axis.val + 2 = S.axis.val ∨ S.axis.val + 2 = R.axis.val →
      R.length + S.length ≤ m + 1) :
    R.axis.val + 3 ≤ S.axis.val ∨ S.axis.val + 3 ≤ R.axis.val := by
  have h := hsep _ (R.long_central hR).1 _ (S.long_central hS).1
  have hgap : R.axis.val + 1 < S.axis.val ∨ S.axis.val + 1 < R.axis.val := by
    by_cases hd : S.horizontal = true
    · simpa [Rod.point, hdir, hd] using h
    · simpa [Rod.point, hdir, hd] using h
  by_contra hn
  have he : R.axis.val + 2 = S.axis.val ∨ S.axis.val + 2 = R.axis.val := by omega
  have := htwo he
  omega

/-- The perpendicular pair misses an entire triple on at least one rod.
This uses only the local contact restriction, not longness or rootedness. -/
theorem Rod.perpendicular_missing_triple {m : Nat} (R S : Rod m)
    (hR : R.horizontal = true) (hS : S.horizontal = false)
    (hsep : R.Separated S) :
    Disjoint (Icc (S.axis.val - 1) (S.axis.val + 1)) R.span ∨
      Disjoint (Icc (R.axis.val - 1) (R.axis.val + 1)) S.span := by
  by_contra hn
  have hn' := not_or.mp hn
  obtain ⟨x, hx, hxR⟩ := not_disjoint_iff.mp hn'.1
  obtain ⟨y, hy, hyS⟩ := not_disjoint_iff.mp hn'.2
  have h := hsep x hxR y hyS
  simp only [Rod.point, hR, hS, Bool.false_eq_true, if_true, if_false] at h
  have hx' := mem_Icc.mp hx
  have hy' := mem_Icc.mp hy
  omega

/-- Subtract the strict baseline before estimating an individual length.
Three OTHER short corner rods save six, whether or not i is a corner rod. -/
theorem four_short_force_long {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k m : Nat) (hk : 7 ≤ k) (hm : m + 2 = 3 * k)
    (hcount : Fintype.card ι = k) (length : ι → Nat)
    (hcap : ∀ i, length i ≤ m - 1)
    (corners : Finset ι) (hfour : corners.card = 4)
    (hshort : ∀ i ∈ corners, length i + 3 ≤ m)
    (hmass : 3 * (∑ i, length i) + k = m * m) :
    ∀ i, 5 * k + 13 ≤ 3 * length i ∧ m + 1 < 2 * length i := by
  let d := fun i => m - 1 - length i
  have hsplit : (∑ i, d i) + (∑ i, length i) = (m - 1) * k := by
    rw [← sum_add_distrib]
    calc
      _ = ∑ _i : ι, (m - 1) := sum_congr rfl (fun i _ => Nat.sub_add_cancel (hcap i))
      _ = _ := by simp [hcount, Nat.mul_comm]
  have hm1 : m - 1 + 1 = m := by omega
  have hdelta : 3 * (∑ i, d i) + 4 = 4 * k := by nlinarith
  intro i
  have hecard : 3 ≤ (corners.erase i).card := by
    by_cases hi : i ∈ corners
    · have := card_erase_add_one hi
      omega
    · simp [erase_eq_of_notMem hi, hfour]
  have hsix : 6 ≤ ∑ j ∈ corners.erase i, d j := by
    have h := sum_le_sum (s := corners.erase i) (f := fun _ => 2) (g := d) (fun j hj => by
      have := hshort j (mem_of_mem_erase hj)
      dsimp [d]
      omega)
    simp only [sum_const, smul_eq_mul] at h
    omega
  have hlocal : d i + 6 ≤ ∑ j, d j := by
    have h := sum_le_sum_of_subset (f := d) (subset_univ (insert i (corners.erase i)))
    rw [sum_insert (notMem_erase i corners)] at h
    omega
  have hd : d i + length i = m - 1 := Nat.sub_add_cancel (hcap i)
  constructor <;> nlinarith

/-- Complete endpoint exclusion for interval inventories with the actual
local grid restrictions and four corner records. In particular the cyclic
orientation is not an exception to this theorem. The actual rooted-forest
corollary is in CornerRoots, via RodInventory. -/
theorem long_rods_endpoint_false {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k m : Nat) (hk : 7 ≤ k) (hm : m + 2 = 3 * k)
    (hcount : Fintype.card ι = k) (R : ι → Rod m)
    (hcap : ∀ i, (R i).length ≤ m - 1)
    (haxis : ∀ i, 1 ≤ (R i).axis.val ∧ (R i).axis.val + 1 < m)
    (hsep : ∀ i j, i ≠ j → (R i).Separated (R j))
    (htwo : ∀ i j, i ≠ j → (R i).horizontal = (R j).horizontal →
      (R i).axis.val + 2 = (R j).axis.val ∨ (R j).axis.val + 2 = (R i).axis.val →
      (R i).length + (R j).length ≤ m + 1)
    (corners : Finset ι) (hfour : corners.card = 4)
    (hshort : ∀ i ∈ corners, (R i).length + 3 ≤ m)
    (hcorneraxis : ∀ i ∈ corners, (R i).axis.val = 1 ∨ (R i).axis.val + 2 = m)
    (hmass : 3 * (∑ i, (R i).length) + k = m * m) : False := by
  have hlong := four_short_force_long k m hk hm hcount (fun i => (R i).length)
    hcap corners hfour hshort hmass
  let H := univ.filter (fun i => (R i).horizontal = true)
  let V := univ.filter (fun i => (R i).horizontal ≠ true)
  have hspace (S : Finset ι) (hd : ∀ i ∈ S, ∀ j ∈ S, (R i).horizontal = (R j).horizontal) :
      ThreeSpaced S (fun i => (R i).axis.val) := by
    intro i hi j hj hne
    exact (R i).long_parallel_spacing (R j) (hlong i).2 (hlong j).2 (hd i hi j hj)
      (hsep i j hne) (htwo i j hne (hd i hi j hj))
  have hsH : ThreeSpaced H (fun i => (R i).axis.val) := hspace H (by
    intro i hi j hj
    exact (mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm)
  have hsV : ThreeSpaced V (fun i => (R i).axis.val) := hspace V (by
    intro i hi j hj
    have hi' := (mem_filter.mp hi).2
    have hj' := (mem_filter.mp hj).2
    cases hiR : (R i).horizontal <;> cases hjR : (R j).horizontal <;> simp_all)
  have hHV : H.card + V.card = k := by
    simpa [H, V, hcount] using card_filter_add_card_filter_not
      (s := (univ : Finset ι)) (p := fun i => (R i).horizontal = true)
  have hsmall (S : Finset ι) (hS : ThreeSpaced S (fun i => (R i).axis.val)) :
      (corners ∩ S).card ≤ 2 := by
    have hinj : Set.InjOn (fun i => (R i).axis.val) (↑(corners ∩ S) : Set ι) := by
      intro i hi j hj he
      by_contra hne
      have := hS i (mem_inter.mp hi).2 j (mem_inter.mp hj).2 hne
      omega
    have hsub : (corners ∩ S).image (fun i => (R i).axis.val) ⊆ ({1, m - 2} : Finset Nat) := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
      have := hcorneraxis i (mem_inter.mp hi).1
      simp only [mem_insert, mem_singleton]
      omega
    have h := card_le_card hsub
    rw [card_image_of_injOn hinj] at h
    exact h.trans (by simpa using card_insert_le 1 ({m - 2} : Finset Nat))
  have hcornersplit : (corners ∩ H).card + (corners ∩ V).card = 4 := by
    have he (p : ι → Prop) [DecidablePred p] : corners ∩ univ.filter p = corners.filter p := by
      ext i
      simp only [mem_inter, mem_filter, mem_univ, true_and]
    simp only [H, V, he]
    rw [card_filter_add_card_filter_not, hfour]
  have hH2 : 2 ≤ H.card := by
    have := hsmall V hsV
    have := card_le_card (inter_subset_right (s₁ := corners) (s₂ := H))
    omega
  have hV2 : 2 ≤ V.card := by
    have := hsmall H hsH
    have := card_le_card (inter_subset_right (s₁ := corners) (s₂ := V))
    omega
  have hpacking := missing_triples_bound m H V (fun i => (R i).axis.val)
    (fun i => (R i).axis.val) (fun i => (R i).span) (fun i => (R i).span)
    (fun i _ => (R i).span_subset) (fun i _ => (R i).span_subset) hsH hsV
    (fun i _ => haxis i) (fun i _ => haxis i) (by
      intro i hi j hj
      have hi' := (mem_filter.mp hi).2
      have hj' := (mem_filter.mp hj).2
      have hjf : (R j).horizontal = false := by cases he : (R j).horizontal <;> simp_all
      have hne : i ≠ j := by intro he; exact hj' (he ▸ hi')
      exact (R i).perpendicular_missing_triple (R j) hi' hjf (hsep i j hne))
  have hsum : H.sum (fun i => m - (R i).span.card) + V.sum (fun i => m - (R i).span.card) =
      ∑ i, (m - (R i).length) := by
    simp only [H, V, Rod.span_card]
    exact sum_filter_add_sum_filter_not _ _ _
  rw [hsum] at hpacking
  have hsplit : (∑ i, (m - (R i).length)) + (∑ i, (R i).length) = m * k := by
    rw [← sum_add_distrib]
    calc
      _ = ∑ _i : ι, m := sum_congr rfl (fun i _ => Nat.sub_add_cancel (by have := hcap i; omega))
      _ = _ := by simp [hcount, Nat.mul_comm]
  have hdeficit : 3 * (∑ i, (m - (R i).length)) + 4 = 7 * k := by nlinarith
  have hprod : 2 * (k - 2) ≤ H.card * V.card := by
    have := Nat.zero_le ((H.card - 2) * (V.card - 2))
    have hHsub : H.card - 2 + 2 = H.card := by omega
    have hVsub : V.card - 2 + 2 = V.card := by omega
    have hk2 : k - 2 + 2 = k := by omega
    nlinarith
  have hk2 : k - 2 + 2 = k := by omega
  nlinarith

end GridGraphs.BoundaryFive.Rootless
