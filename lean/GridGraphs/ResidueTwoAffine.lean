import GridGraphs.Defs

/-!
# The affine residue-two family

This is the width-three affine recurrence based at the 17 by 17 pattern.  A
step duplicates base rows 9, 10, 11 and base columns 4, 5, 6.  The definition
below records a base coordinate together with its copy number, so the
recurrence is represented without constructing any intermediate finite board.
-/

namespace GridGraphs

open Finset

/-- The rows of the 17 by 17 affine base, represented by their U columns. -/
def residueTwoAffineBaseRow : Nat → Finset Nat
  | 0 => [1].toFinset
  | 1 => [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16].toFinset
  | 2 => [1, 2, 3, 4, 6, 7, 9, 10, 12, 13, 15, 16].toFinset
  | 3 => [1, 2, 4, 5, 6, 7, 9, 10, 12, 13, 14, 15].toFinset
  | 4 => [1, 2, 4, 5, 7, 8, 9, 10, 12, 14, 15].toFinset
  | 5 => [1, 2, 4, 5, 7, 8, 10, 11, 12, 14, 15].toFinset
  | 6 => [1, 2, 4, 5, 7, 8, 10, 12, 13, 14, 15].toFinset
  | 7 => [1, 2, 4, 5, 7, 8, 9, 10, 12, 13, 15].toFinset
  | 8 => [1, 2, 4, 5, 7, 9, 10, 12, 13, 14, 15].toFinset
  | 9 => [1, 2, 4, 5, 7, 8, 9, 10, 12, 14, 15].toFinset
  | 10 => [1, 2, 4, 5, 7, 8, 10, 11, 12, 14, 15].toFinset
  | 11 => [1, 2, 4, 5, 7, 8, 10, 11, 12, 14, 15].toFinset
  | 12 => [1, 2, 4, 5, 7, 8, 10, 12, 13, 14, 15].toFinset
  | 13 => [1, 2, 4, 5, 7, 8, 10, 11, 12, 13, 15].toFinset
  | 14 => [1, 2, 4, 5, 7, 8, 10, 11, 13, 14, 15].toFinset
  | 15 => [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15].toFinset
  | 16 => [1, 15].toFinset
  | _ => ∅

/-- Membership in the fixed affine base. -/
def IsResidueTwoAffineBase (r c : Fin 17) : Prop :=
  c.val ∈ residueTwoAffineBaseRow r.val

instance (r c : Fin 17) : Decidable (IsResidueTwoAffineBase r c) := by
  unfold IsResidueTwoAffineBase
  infer_instance

/-- A pumped base coordinate has `t+1` copies; every other coordinate has one. -/
def residueTwoPumpMultiplicity (cut t : Nat) (i : Fin 17) : Nat :=
  if cut ≤ i.val ∧ i.val < cut + 3 then t + 1 else 1

/-- A base coordinate and the number of the selected affine copy. -/
structure ResidueTwoAffineIndex (cut t : Nat) where
  base : Fin 17
  copy : Fin (residueTwoPumpMultiplicity cut t base)
  deriving DecidableEq, Fintype

/-- Expand a copied base coordinate into the board enlarged by `3t`. -/
def residueTwoExpandIndex (cut t : Nat) (hcut : cut + 3 ≤ 17)
    (x : ResidueTwoAffineIndex cut t) : Fin (17 + 3 * t) :=
  if hpump : cut ≤ x.base.val ∧ x.base.val < cut + 3 then
    ⟨x.base.val + 3 * x.copy.val, by
      have hc := x.copy.isLt
      simp only [residueTwoPumpMultiplicity, if_pos hpump] at hc
      omega⟩
  else if habove : cut + 3 ≤ x.base.val then
    ⟨x.base.val + 3 * t, by have := x.base.isLt; omega⟩
  else
    ⟨x.base.val, by omega⟩

@[simp] theorem residueTwoExpandIndex_of_pump (cut t : Nat) (hcut : cut + 3 ≤ 17)
    (x : ResidueTwoAffineIndex cut t)
    (h : cut ≤ x.base.val ∧ x.base.val < cut + 3) :
    (residueTwoExpandIndex cut t hcut x).val = x.base.val + 3 * x.copy.val := by
  simp [residueTwoExpandIndex, h]

@[simp] theorem residueTwoExpandIndex_of_above (cut t : Nat) (hcut : cut + 3 ≤ 17)
    (x : ResidueTwoAffineIndex cut t) (hp : ¬(cut ≤ x.base.val ∧ x.base.val < cut + 3))
    (h : cut + 3 ≤ x.base.val) :
    (residueTwoExpandIndex cut t hcut x).val = x.base.val + 3 * t := by
  simp [residueTwoExpandIndex, hp, h]

@[simp] theorem residueTwoExpandIndex_of_below (cut t : Nat) (hcut : cut + 3 ≤ 17)
    (x : ResidueTwoAffineIndex cut t) (hp : ¬(cut ≤ x.base.val ∧ x.base.val < cut + 3))
    (h : ¬cut + 3 ≤ x.base.val) :
    (residueTwoExpandIndex cut t hcut x).val = x.base.val := by
  simp [residueTwoExpandIndex, hp, h]

/-- Coordinate expansion is injective: copy numbers describe disjoint blocks. -/
theorem residueTwoExpandIndex_injective (cut t : Nat) (hcut : cut + 3 ≤ 17) :
    Function.Injective (residueTwoExpandIndex cut t hcut) := by
  rintro ⟨xb, xc⟩ ⟨yb, yc⟩ h
  have hv := congrArg Fin.val h
  by_cases xpump : cut ≤ xb.val ∧ xb.val < cut + 3
  · rw [residueTwoExpandIndex_of_pump cut t hcut ⟨xb, xc⟩ xpump] at hv
    by_cases ypump : cut ≤ yb.val ∧ yb.val < cut + 3
    · rw [residueTwoExpandIndex_of_pump cut t hcut ⟨yb, yc⟩ ypump] at hv
      change xb.val + 3 * xc.val = yb.val + 3 * yc.val at hv
      have hxc := xc.isLt
      have hyc := yc.isLt
      simp only [residueTwoPumpMultiplicity, if_pos xpump] at hxc
      simp only [residueTwoPumpMultiplicity, if_pos ypump] at hyc
      have hbval : xb.val = yb.val := by omega
      have hcval : xc.val = yc.val := by omega
      have hb : xb = yb := Fin.ext hbval
      subst yb
      have hc : xc = yc := Fin.ext hcval
      subst yc
      rfl
    ·
      by_cases yabove : cut + 3 ≤ yb.val
      · rw [residueTwoExpandIndex_of_above cut t hcut ⟨yb, yc⟩ ypump yabove] at hv
        change xb.val + 3 * xc.val = yb.val + 3 * t at hv
        have hxc := xc.isLt
        simp only [residueTwoPumpMultiplicity, if_pos xpump] at hxc
        omega
      · rw [residueTwoExpandIndex_of_below cut t hcut ⟨yb, yc⟩ ypump yabove] at hv
        change xb.val + 3 * xc.val = yb.val at hv
        omega
  ·
    by_cases xabove : cut + 3 ≤ xb.val
    · rw [residueTwoExpandIndex_of_above cut t hcut ⟨xb, xc⟩ xpump xabove] at hv
      by_cases ypump : cut ≤ yb.val ∧ yb.val < cut + 3
      · rw [residueTwoExpandIndex_of_pump cut t hcut ⟨yb, yc⟩ ypump] at hv
        change xb.val + 3 * t = yb.val + 3 * yc.val at hv
        have hyc := yc.isLt
        simp only [residueTwoPumpMultiplicity, if_pos ypump] at hyc
        omega
      ·
        by_cases yabove : cut + 3 ≤ yb.val
        · rw [residueTwoExpandIndex_of_above cut t hcut ⟨yb, yc⟩ ypump yabove] at hv
          change xb.val + 3 * t = yb.val + 3 * t at hv
          have hb : xb = yb := Fin.ext (by omega)
          subst yb
          have hxc := xc.isLt
          have hyc := yc.isLt
          simp only [residueTwoPumpMultiplicity, if_neg xpump] at hxc hyc
          have hc : xc = yc := Fin.ext (by omega)
          subst yc
          rfl
        · rw [residueTwoExpandIndex_of_below cut t hcut ⟨yb, yc⟩ ypump yabove] at hv
          change xb.val + 3 * t = yb.val at hv
          omega
    · rw [residueTwoExpandIndex_of_below cut t hcut ⟨xb, xc⟩ xpump xabove] at hv
      by_cases ypump : cut ≤ yb.val ∧ yb.val < cut + 3
      · rw [residueTwoExpandIndex_of_pump cut t hcut ⟨yb, yc⟩ ypump] at hv
        change xb.val = yb.val + 3 * yc.val at hv
        omega
      ·
        by_cases yabove : cut + 3 ≤ yb.val
        · rw [residueTwoExpandIndex_of_above cut t hcut ⟨yb, yc⟩ ypump yabove] at hv
          change xb.val = yb.val + 3 * t at hv
          omega
        · rw [residueTwoExpandIndex_of_below cut t hcut ⟨yb, yc⟩ ypump yabove] at hv
          change xb.val = yb.val at hv
          have hb : xb = yb := Fin.ext (by omega)
          subst yb
          have hxc := xc.isLt
          have hyc := yc.isLt
          simp only [residueTwoPumpMultiplicity, if_neg xpump] at hxc hyc
          have hc : xc = yc := Fin.ext (by omega)
          subst yc
          rfl

/-- Symbolic occurrences of U vertices after `t` affine width-three steps. -/
abbrev ResidueTwoAffineOccurrence (t : Nat) :=
  Σ r : Fin 17, Σ c : Fin 17,
    {_copies : Fin (residueTwoPumpMultiplicity 9 t r) ×
      Fin (residueTwoPumpMultiplicity 4 t c) // IsResidueTwoAffineBase r c}

def residueTwoAffineOccurrences (t : Nat) : Finset (ResidueTwoAffineOccurrence t) :=
  Finset.univ

/-- Map a symbolic occurrence to its vertex on the `(17+3t)` square. -/
def residueTwoAffineVertex (t : Nat)
    (x : ResidueTwoAffineOccurrence t) :
    GridVertex (17 + 3 * t) (17 + 3 * t) :=
  (residueTwoExpandIndex 9 t (by omega) ⟨x.1, x.2.2.val.1⟩,
    residueTwoExpandIndex 4 t (by omega) ⟨x.2.1, x.2.2.val.2⟩)

theorem residueTwoAffineVertex_injective (t : Nat) :
    Function.Injective (residueTwoAffineVertex t) := by
  intro x y h
  have hr := residueTwoExpandIndex_injective 9 t (by omega) (congrArg Prod.fst h)
  have hc := residueTwoExpandIndex_injective 4 t (by omega) (congrArg Prod.snd h)
  have hrb : x.1 = y.1 := congrArg ResidueTwoAffineIndex.base hr
  have hcb : x.2.1 = y.2.1 := congrArg ResidueTwoAffineIndex.base hc
  cases x with
  | mk xr xs =>
    cases y with
    | mk yr ys =>
      simp only at hrb
      subst yr
      cases xs with
      | mk xc xcopies =>
        cases ys with
        | mk yc ycopies =>
          simp only at hcb
          subst yc
          congr 2
          apply Subtype.ext
          apply Prod.ext
          · apply Fin.ext
            exact congrArg (fun z => z.copy.val) hr
          · apply Fin.ext
            exact congrArg (fun z => z.copy.val) hc

/-- The affine U pattern on side `3k+2`, written with `t=k-5`. -/
def uResidueTwoAffine (k : Nat) :
    Finset (GridVertex (3 * k + 2) (3 * k + 2)) :=
  if hk : 5 ≤ k then
    let castVertex : GridVertex (17 + 3 * (k - 5)) (17 + 3 * (k - 5)) →
        GridVertex (3 * k + 2) (3 * k + 2) := fun x =>
      (⟨x.1.val, by have := x.1.isLt; omega⟩,
        ⟨x.2.val, by have := x.2.isLt; omega⟩)
    (residueTwoAffineOccurrences (k - 5)).image
      (fun x => castVertex (residueTwoAffineVertex (k - 5) x))
  else ∅

set_option maxHeartbeats 800000 in
/-- The fixed base has 6 doubly-pumped, 54 singly-pumped, and 119 unpumped
U vertices.  These are coefficients of the symbolic recurrence, not checks of
generated boards. -/
theorem residueTwoAffine_weighted_base (t : Nat) :
    ∑ r : Fin 17, ∑ c : Fin 17,
      (if IsResidueTwoAffineBase r c then
        residueTwoPumpMultiplicity 9 t r * residueTwoPumpMultiplicity 4 t c
      else 0) = 6 * (t + 1) ^ 2 + 54 * (t + 1) + 119 := by
  simp [IsResidueTwoAffineBase, residueTwoAffineBaseRow,
    residueTwoPumpMultiplicity, Fin.sum_univ_succ]
  ring_nf

theorem residueTwoAffineOccurrences_card (t : Nat) :
    (residueTwoAffineOccurrences t).card =
      ∑ r : Fin 17, ∑ c : Fin 17,
        (if IsResidueTwoAffineBase r c then
          residueTwoPumpMultiplicity 9 t r * residueTwoPumpMultiplicity 4 t c
        else 0) := by
  classical
  simp only [residueTwoAffineOccurrences, Finset.card_univ, Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro c _
  by_cases h : IsResidueTwoAffineBase r c
  · simp [h]
  · simp [h]

/-- Exact cardinality of the affine residue-two U pattern. -/
theorem uResidueTwoAffine_card (k : Nat) (hk : 5 ≤ k) :
    (uResidueTwoAffine k).card = 6 * k ^ 2 + 6 * k - 1 := by
  classical
  simp only [uResidueTwoAffine, dif_pos hk]
  rw [Finset.card_image_of_injective _]
  · rw [residueTwoAffineOccurrences_card, residueTwoAffine_weighted_base]
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
    simp
    ring_nf
    omega
  · intro x y h
    apply residueTwoAffineVertex_injective (k - 5)
    apply Prod.ext <;> apply Fin.ext
    · exact congrArg (fun z => z.1.val) h
    · exact congrArg (fun z => z.2.val) h

/-- Each width-three pump adds exactly `12k+12` U vertices. -/
theorem uResidueTwoAffine_card_step (k : Nat) (hk : 5 ≤ k) :
    (uResidueTwoAffine (k + 1)).card =
      (uResidueTwoAffine k).card + (12 * k + 12) := by
  rw [uResidueTwoAffine_card (k + 1) (by omega), uResidueTwoAffine_card k hk]
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  ring_nf
  omega

end GridGraphs
