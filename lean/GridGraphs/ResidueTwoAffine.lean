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

/-- Embed a copy index through one affine step.  For a pumped coordinate the
last old copy is moved past the newly inserted copy; all earlier copies remain
fixed. -/
def residueTwoAffineCopyStep (cut t : Nat) (i : Fin 17)
    (j : Fin (residueTwoPumpMultiplicity cut t i)) :
    Fin (residueTwoPumpMultiplicity cut (t + 1) i) := by
  by_cases hpump : cut ≤ i.val ∧ i.val < cut + 3
  · refine ⟨if j.val = t then j.val + 1 else j.val, ?_⟩
    have hj := j.isLt
    simp only [residueTwoPumpMultiplicity, if_pos hpump] at hj ⊢
    split <;> omega
  · refine ⟨j.val, ?_⟩
    have hj := j.isLt
    simp only [residueTwoPumpMultiplicity, if_neg hpump] at hj ⊢
    exact hj

/-- Keep an old copy at the same copy number through a step.  On pumped base
coordinates this realizes the newly inserted block before the moved final old
copy. -/
def residueTwoAffineCopyKeep (cut t : Nat) (i : Fin 17)
    (j : Fin (residueTwoPumpMultiplicity cut t i)) :
    Fin (residueTwoPumpMultiplicity cut (t + 1) i) := by
  refine ⟨j.val, ?_⟩
  have hj := j.isLt
  unfold residueTwoPumpMultiplicity at hj ⊢
  split_ifs at hj ⊢ <;> omega

/-- Symbolic occurrences embed through one step by inserting a copy immediately
before the final old pumped block. -/
def residueTwoAffineOccurrenceStep (t : Nat) :
    ResidueTwoAffineOccurrence t → ResidueTwoAffineOccurrence (t + 1)
  | ⟨r, c, copies⟩ =>
      ⟨r, c, ⟨
        (residueTwoAffineCopyStep 9 t r copies.1.1,
          residueTwoAffineCopyStep 4 t c copies.1.2),
        copies.2⟩⟩

def residueTwoAffineOccurrenceKeep (t : Nat) :
    ResidueTwoAffineOccurrence t → ResidueTwoAffineOccurrence (t + 1)
  | ⟨r, c, copies⟩ =>
      ⟨r, c, ⟨
        (residueTwoAffineCopyKeep 9 t r copies.1.1,
          residueTwoAffineCopyKeep 4 t c copies.1.2),
        copies.2⟩⟩

/-- Step the row copy and retain the column copy through one affine step. -/
def residueTwoAffineOccurrenceStepKeep (t : Nat) :
    ResidueTwoAffineOccurrence t → ResidueTwoAffineOccurrence (t + 1)
  | ⟨r, c, copies⟩ =>
      ⟨r, c, ⟨
        (residueTwoAffineCopyStep 9 t r copies.1.1,
          residueTwoAffineCopyKeep 4 t c copies.1.2),
        copies.2⟩⟩

/-- Retain the row copy and step the column copy through one affine step. -/
def residueTwoAffineOccurrenceKeepStep (t : Nat) :
    ResidueTwoAffineOccurrence t → ResidueTwoAffineOccurrence (t + 1)
  | ⟨r, c, copies⟩ =>
      ⟨r, c, ⟨
        (residueTwoAffineCopyKeep 9 t r copies.1.1,
          residueTwoAffineCopyStep 4 t c copies.1.2),
        copies.2⟩⟩

@[simp] theorem residueTwoExpandIndex_copyStep (cut t : Nat)
    (hcut : cut + 3 ≤ 17) (i : Fin 17)
    (j : Fin (residueTwoPumpMultiplicity cut t i)) :
    (residueTwoExpandIndex cut (t + 1) hcut
      ⟨i, residueTwoAffineCopyStep cut t i j⟩).val =
        if cut + 3 * t ≤ (residueTwoExpandIndex cut t hcut ⟨i, j⟩).val then
          (residueTwoExpandIndex cut t hcut ⟨i, j⟩).val + 3
        else (residueTwoExpandIndex cut t hcut ⟨i, j⟩).val := by
  by_cases hpump : cut ≤ i.val ∧ i.val < cut + 3
  · rw [residueTwoExpandIndex_of_pump cut t hcut ⟨i, j⟩ hpump,
      residueTwoExpandIndex_of_pump cut (t + 1) hcut
        ⟨i, residueTwoAffineCopyStep cut t i j⟩ hpump]
    have hj := j.isLt
    simp only [residueTwoPumpMultiplicity, if_pos hpump] at hj
    simp only [residueTwoAffineCopyStep, dif_pos hpump]
    split_ifs <;> omega
  · by_cases habove : cut + 3 ≤ i.val
    · rw [residueTwoExpandIndex_of_above cut t hcut ⟨i, j⟩ hpump habove,
        residueTwoExpandIndex_of_above cut (t + 1) hcut
          ⟨i, residueTwoAffineCopyStep cut t i j⟩ hpump habove]
      change i.val + 3 * (t + 1) =
        if cut + 3 * t ≤ i.val + 3 * t then i.val + 3 * t + 3
        else i.val + 3 * t
      rw [if_pos (by omega)]
      omega
    · rw [residueTwoExpandIndex_of_below cut t hcut ⟨i, j⟩ hpump habove,
        residueTwoExpandIndex_of_below cut (t + 1) hcut
          ⟨i, residueTwoAffineCopyStep cut t i j⟩ hpump habove]
      change i.val = if cut + 3 * t ≤ i.val then i.val + 3 else i.val
      rw [if_neg (by omega)]

theorem residueTwoExpandIndex_copyStep_cast (cut t t' : Nat)
    (ht : t + 1 = t') (hcut : cut + 3 ≤ 17) (i : Fin 17)
    (j : Fin (residueTwoPumpMultiplicity cut t i)) :
    (residueTwoExpandIndex cut t' hcut
      ⟨i, Fin.cast
        (congrArg (fun s => residueTwoPumpMultiplicity cut s i) ht)
        (residueTwoAffineCopyStep cut t i j)⟩).val =
      (residueTwoExpandIndex cut (t + 1) hcut
        ⟨i, residueTwoAffineCopyStep cut t i j⟩).val := by
  by_cases hpump : cut ≤ i.val ∧ i.val < cut + 3
  · rw [residueTwoExpandIndex_of_pump cut t' hcut _ hpump,
      residueTwoExpandIndex_of_pump cut (t + 1) hcut _ hpump]
    simp
  · by_cases habove : cut + 3 ≤ i.val
    · rw [residueTwoExpandIndex_of_above cut t' hcut _ hpump habove,
        residueTwoExpandIndex_of_above cut (t + 1) hcut _ hpump habove]
      change i.val + 3 * t' = i.val + 3 * (t + 1)
      omega
    · rw [residueTwoExpandIndex_of_below cut t' hcut _ hpump habove,
        residueTwoExpandIndex_of_below cut (t + 1) hcut _ hpump habove]

@[simp] theorem residueTwoExpandIndex_copyKeep (cut t : Nat)
    (hcut : cut + 3 ≤ 17) (i : Fin 17)
    (j : Fin (residueTwoPumpMultiplicity cut t i)) :
    (residueTwoExpandIndex cut (t + 1) hcut
      ⟨i, residueTwoAffineCopyKeep cut t i j⟩).val =
        if cut + 3 + 3 * t ≤
            (residueTwoExpandIndex cut t hcut ⟨i, j⟩).val then
          (residueTwoExpandIndex cut t hcut ⟨i, j⟩).val + 3
        else (residueTwoExpandIndex cut t hcut ⟨i, j⟩).val := by
  by_cases hpump : cut ≤ i.val ∧ i.val < cut + 3
  · rw [residueTwoExpandIndex_of_pump cut t hcut ⟨i, j⟩ hpump,
      residueTwoExpandIndex_of_pump cut (t + 1) hcut
        ⟨i, residueTwoAffineCopyKeep cut t i j⟩ hpump]
    have hj := j.isLt
    simp only [residueTwoPumpMultiplicity, if_pos hpump] at hj
    simp only [residueTwoAffineCopyKeep]
    rw [if_neg (by omega)]
  · by_cases habove : cut + 3 ≤ i.val
    · rw [residueTwoExpandIndex_of_above cut t hcut ⟨i, j⟩ hpump habove,
        residueTwoExpandIndex_of_above cut (t + 1) hcut
          ⟨i, residueTwoAffineCopyKeep cut t i j⟩ hpump habove]
      change i.val + 3 * (t + 1) =
        if cut + 3 + 3 * t ≤ i.val + 3 * t then i.val + 3 * t + 3
        else i.val + 3 * t
      rw [if_pos (by omega)]
      omega
    · rw [residueTwoExpandIndex_of_below cut t hcut ⟨i, j⟩ hpump habove,
        residueTwoExpandIndex_of_below cut (t + 1) hcut
          ⟨i, residueTwoAffineCopyKeep cut t i j⟩ hpump habove]
      change i.val =
        if cut + 3 + 3 * t ≤ i.val then i.val + 3 else i.val
      rw [if_neg (by omega)]

theorem residueTwoExpandIndex_copyKeep_cast (cut t t' : Nat)
    (ht : t + 1 = t') (hcut : cut + 3 ≤ 17) (i : Fin 17)
    (j : Fin (residueTwoPumpMultiplicity cut t i)) :
    (residueTwoExpandIndex cut t' hcut
      ⟨i, Fin.cast
        (congrArg (fun s => residueTwoPumpMultiplicity cut s i) ht)
        (residueTwoAffineCopyKeep cut t i j)⟩).val =
      (residueTwoExpandIndex cut (t + 1) hcut
        ⟨i, residueTwoAffineCopyKeep cut t i j⟩).val := by
  by_cases hpump : cut ≤ i.val ∧ i.val < cut + 3
  · rw [residueTwoExpandIndex_of_pump cut t' hcut _ hpump,
      residueTwoExpandIndex_of_pump cut (t + 1) hcut _ hpump]
    simp
  · by_cases habove : cut + 3 ≤ i.val
    · rw [residueTwoExpandIndex_of_above cut t' hcut _ hpump habove,
        residueTwoExpandIndex_of_above cut (t + 1) hcut _ hpump habove]
      change i.val + 3 * t' = i.val + 3 * (t + 1)
      omega
    · rw [residueTwoExpandIndex_of_below cut t' hcut _ hpump habove,
        residueTwoExpandIndex_of_below cut (t + 1) hcut _ hpump habove]

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

@[simp] theorem residueTwoAffineVertex_occurrenceStep_fst (t : Nat)
    (x : ResidueTwoAffineOccurrence t) :
    (residueTwoAffineVertex (t + 1) (residueTwoAffineOccurrenceStep t x)).1.val =
      if 9 + 3 * t ≤ (residueTwoAffineVertex t x).1.val then
        (residueTwoAffineVertex t x).1.val + 3
      else (residueTwoAffineVertex t x).1.val := by
  cases x with
  | mk r rest =>
      cases rest with
      | mk c copies =>
          exact residueTwoExpandIndex_copyStep 9 t (by omega) r copies.1.1

@[simp] theorem residueTwoAffineVertex_occurrenceStep_snd (t : Nat)
    (x : ResidueTwoAffineOccurrence t) :
    (residueTwoAffineVertex (t + 1) (residueTwoAffineOccurrenceStep t x)).2.val =
      if 4 + 3 * t ≤ (residueTwoAffineVertex t x).2.val then
        (residueTwoAffineVertex t x).2.val + 3
      else (residueTwoAffineVertex t x).2.val := by
  cases x with
  | mk r rest =>
      cases rest with
      | mk c copies =>
          exact residueTwoExpandIndex_copyStep 4 t (by omega) c copies.1.2

@[simp] theorem residueTwoAffineVertex_occurrenceKeep_fst (t : Nat)
    (x : ResidueTwoAffineOccurrence t) :
    (residueTwoAffineVertex (t + 1) (residueTwoAffineOccurrenceKeep t x)).1.val =
      if 9 + 3 + 3 * t ≤ (residueTwoAffineVertex t x).1.val then
        (residueTwoAffineVertex t x).1.val + 3
      else (residueTwoAffineVertex t x).1.val := by
  cases x with
  | mk r rest =>
      cases rest with
      | mk c copies =>
          exact residueTwoExpandIndex_copyKeep 9 t (by omega) r copies.1.1

@[simp] theorem residueTwoAffineVertex_occurrenceKeep_snd (t : Nat)
    (x : ResidueTwoAffineOccurrence t) :
    (residueTwoAffineVertex (t + 1) (residueTwoAffineOccurrenceKeep t x)).2.val =
      if 4 + 3 + 3 * t ≤ (residueTwoAffineVertex t x).2.val then
        (residueTwoAffineVertex t x).2.val + 3
      else (residueTwoAffineVertex t x).2.val := by
  cases x with
  | mk r rest =>
      cases rest with
      | mk c copies =>
          exact residueTwoExpandIndex_copyKeep 4 t (by omega) c copies.1.2

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

/-- Physical vertex embedding for one affine step.  The new pumped block is
inserted immediately before the final old copy in each coordinate. -/
def residueTwoAffineStepVertex (k : Nat) :
    GridVertex (3 * k + 2) (3 * k + 2) →
      GridVertex (3 * (k + 1) + 2) (3 * (k + 1) + 2) := fun v =>
  (⟨if 3 * k - 6 ≤ v.1.val then v.1.val + 3 else v.1.val, by
      split <;> have := v.1.isLt <;> omega⟩,
    ⟨if 3 * k - 11 ≤ v.2.val then v.2.val + 3 else v.2.val, by
      split <;> have := v.2.isLt <;> omega⟩)

/-- Every old affine U vertex survives under the physical step embedding. -/
theorem residueTwoAffineStepVertex_mem (k : Nat) (hk : 5 ≤ k)
    {v : GridVertex (3 * k + 2) (3 * k + 2)}
    (hv : v ∈ uResidueTwoAffine k) :
    residueTwoAffineStepVertex k v ∈ uResidueTwoAffine (k + 1) := by
  classical
  simp only [uResidueTwoAffine, dif_pos hk,
    dif_pos (by omega : 5 ≤ k + 1), Finset.mem_image,
    residueTwoAffineOccurrences, Finset.mem_univ, true_and] at hv ⊢
  obtain ⟨x, hx⟩ := hv
  rcases x with ⟨r, c, copies⟩
  have ht : (k - 5) + 1 = (k + 1) - 5 := by omega
  let ir : Fin (residueTwoPumpMultiplicity 9 ((k + 1) - 5) r) :=
    Fin.cast (congrArg (fun t => residueTwoPumpMultiplicity 9 t r) ht)
      (residueTwoAffineCopyStep 9 (k - 5) r copies.1.1)
  let ic : Fin (residueTwoPumpMultiplicity 4 ((k + 1) - 5) c) :=
    Fin.cast (congrArg (fun t => residueTwoPumpMultiplicity 4 t c) ht)
      (residueTwoAffineCopyStep 4 (k - 5) c copies.1.2)
  let row := residueTwoExpandIndex 9 ((k + 1) - 5) (by omega)
    (⟨r, ir⟩ : ResidueTwoAffineIndex 9 ((k + 1) - 5))
  let col := residueTwoExpandIndex 4 ((k + 1) - 5) (by omega)
    (⟨c, ic⟩ : ResidueTwoAffineIndex 4 ((k + 1) - 5))
  have hrowOld :
      (residueTwoAffineVertex (k - 5) ⟨r, c, copies⟩).1.val = v.1.val :=
    congrArg (fun z => z.1.val) hx
  have hcolOld :
      (residueTwoAffineVertex (k - 5) ⟨r, c, copies⟩).2.val = v.2.val :=
    congrArg (fun z => z.2.val) hx
  have hrow : row.val =
      if 3 * k - 6 ≤ v.1.val then v.1.val + 3 else v.1.val := by
    have hs := residueTwoExpandIndex_copyStep 9 (k - 5) (by omega)
      r copies.1.1
    have hcast : row.val =
        (residueTwoExpandIndex 9 ((k - 5) + 1) (by omega)
          ⟨r, residueTwoAffineCopyStep 9 (k - 5) r copies.1.1⟩).val := by
      exact residueTwoExpandIndex_copyStep_cast 9 (k - 5) ((k + 1) - 5)
        ht (by omega) r copies.1.1
    change row.val = _
    change (residueTwoExpandIndex 9 (k - 5) (by omega)
      ⟨r, copies.1.1⟩).val = v.1.val at hrowOld
    rw [hcast, hs, hrowOld]
    have hcut : 9 + 3 * (k - 5) = 3 * k - 6 := by omega
    rw [hcut]
  have hcol : col.val =
      if 3 * k - 11 ≤ v.2.val then v.2.val + 3 else v.2.val := by
    have hs := residueTwoExpandIndex_copyStep 4 (k - 5) (by omega)
      c copies.1.2
    have hcast : col.val =
        (residueTwoExpandIndex 4 ((k - 5) + 1) (by omega)
          ⟨c, residueTwoAffineCopyStep 4 (k - 5) c copies.1.2⟩).val := by
      exact residueTwoExpandIndex_copyStep_cast 4 (k - 5) ((k + 1) - 5)
        ht (by omega) c copies.1.2
    change col.val = _
    change (residueTwoExpandIndex 4 (k - 5) (by omega)
      ⟨c, copies.1.2⟩).val = v.2.val at hcolOld
    rw [hcast, hs, hcolOld]
    have hcut : 4 + 3 * (k - 5) = 3 * k - 11 := by omega
    rw [hcut]
  let nextCopies :
      {p : Fin (residueTwoPumpMultiplicity 9 ((k + 1) - 5) r) ×
        Fin (residueTwoPumpMultiplicity 4 ((k + 1) - 5) c) //
          IsResidueTwoAffineBase r c} := ⟨(ir, ic), copies.2⟩
  let next : ResidueTwoAffineOccurrence ((k + 1) - 5) :=
    ⟨r, c, nextCopies⟩
  refine ⟨next, ?_⟩
  apply Prod.ext <;> apply Fin.ext
  · change row.val = _
    exact hrow
  · change col.val = _
    exact hcol

/-- Successor vertex obtained by retaining both copy numbers of an old affine
occurrence.  Coordinates beyond the final repeated blocks shift by three. -/
def residueTwoAffineKeepVertex (k : Nat) :
    GridVertex (3 * k + 2) (3 * k + 2) →
      GridVertex (3 * (k + 1) + 2) (3 * (k + 1) + 2) := fun v =>
  (⟨if 3 * k - 3 ≤ v.1.val then v.1.val + 3 else v.1.val, by
      split <;> have := v.1.isLt <;> omega⟩,
    ⟨if 3 * k - 8 ≤ v.2.val then v.2.val + 3 else v.2.val, by
      split <;> have := v.2.isLt <;> omega⟩)

/-- Keeping the copy numbers of any old affine U occurrence exposes a
successor U vertex, with the scalar coordinates from
`residueTwoExpandIndex_copyKeep`. -/
theorem residueTwoAffineKeepVertex_mem (k : Nat) (hk : 5 ≤ k)
    {v : GridVertex (3 * k + 2) (3 * k + 2)}
    (hv : v ∈ uResidueTwoAffine k) :
    residueTwoAffineKeepVertex k v ∈ uResidueTwoAffine (k + 1) := by
  classical
  simp only [uResidueTwoAffine, dif_pos hk,
    dif_pos (by omega : 5 ≤ k + 1), Finset.mem_image,
    residueTwoAffineOccurrences, Finset.mem_univ, true_and] at hv ⊢
  obtain ⟨x, hx⟩ := hv
  rcases x with ⟨r, c, copies⟩
  have ht : (k - 5) + 1 = (k + 1) - 5 := by omega
  let ir : Fin (residueTwoPumpMultiplicity 9 ((k + 1) - 5) r) :=
    Fin.cast (congrArg (fun t => residueTwoPumpMultiplicity 9 t r) ht)
      (residueTwoAffineCopyKeep 9 (k - 5) r copies.1.1)
  let ic : Fin (residueTwoPumpMultiplicity 4 ((k + 1) - 5) c) :=
    Fin.cast (congrArg (fun t => residueTwoPumpMultiplicity 4 t c) ht)
      (residueTwoAffineCopyKeep 4 (k - 5) c copies.1.2)
  let row := residueTwoExpandIndex 9 ((k + 1) - 5) (by omega)
    (⟨r, ir⟩ : ResidueTwoAffineIndex 9 ((k + 1) - 5))
  let col := residueTwoExpandIndex 4 ((k + 1) - 5) (by omega)
    (⟨c, ic⟩ : ResidueTwoAffineIndex 4 ((k + 1) - 5))
  have hrowOld :
      (residueTwoAffineVertex (k - 5) ⟨r, c, copies⟩).1.val = v.1.val :=
    congrArg (fun z => z.1.val) hx
  have hcolOld :
      (residueTwoAffineVertex (k - 5) ⟨r, c, copies⟩).2.val = v.2.val :=
    congrArg (fun z => z.2.val) hx
  have hrow : row.val =
      if 3 * k - 3 ≤ v.1.val then v.1.val + 3 else v.1.val := by
    have hs := residueTwoExpandIndex_copyKeep 9 (k - 5) (by omega)
      r copies.1.1
    have hcast : row.val =
        (residueTwoExpandIndex 9 ((k - 5) + 1) (by omega)
          ⟨r, residueTwoAffineCopyKeep 9 (k - 5) r copies.1.1⟩).val := by
      exact residueTwoExpandIndex_copyKeep_cast 9 (k - 5) ((k + 1) - 5)
        ht (by omega) r copies.1.1
    change row.val = _
    change (residueTwoExpandIndex 9 (k - 5) (by omega)
      ⟨r, copies.1.1⟩).val = v.1.val at hrowOld
    rw [hcast, hs, hrowOld]
    have hcut : 9 + 3 + 3 * (k - 5) = 3 * k - 3 := by omega
    rw [hcut]
  have hcol : col.val =
      if 3 * k - 8 ≤ v.2.val then v.2.val + 3 else v.2.val := by
    have hs := residueTwoExpandIndex_copyKeep 4 (k - 5) (by omega)
      c copies.1.2
    have hcast : col.val =
        (residueTwoExpandIndex 4 ((k - 5) + 1) (by omega)
          ⟨c, residueTwoAffineCopyKeep 4 (k - 5) c copies.1.2⟩).val := by
      exact residueTwoExpandIndex_copyKeep_cast 4 (k - 5) ((k + 1) - 5)
        ht (by omega) c copies.1.2
    change col.val = _
    change (residueTwoExpandIndex 4 (k - 5) (by omega)
      ⟨c, copies.1.2⟩).val = v.2.val at hcolOld
    rw [hcast, hs, hcolOld]
    have hcut : 4 + 3 + 3 * (k - 5) = 3 * k - 8 := by omega
    rw [hcut]
  let nextCopies :
      {p : Fin (residueTwoPumpMultiplicity 9 ((k + 1) - 5) r) ×
        Fin (residueTwoPumpMultiplicity 4 ((k + 1) - 5) c) //
          IsResidueTwoAffineBase r c} := ⟨(ir, ic), copies.2⟩
  let next : ResidueTwoAffineOccurrence ((k + 1) - 5) :=
    ⟨r, c, nextCopies⟩
  refine ⟨next, ?_⟩
  apply Prod.ext <;> apply Fin.ext
  · change row.val = _
    exact hrow
  · change col.val = _
    exact hcol

/-- Mixed successor embedding: row copy numbers step while column copy numbers
are retained. -/
def residueTwoAffineStepKeepVertex (k : Nat) :
    GridVertex (3 * k + 2) (3 * k + 2) →
      GridVertex (3 * (k + 1) + 2) (3 * (k + 1) + 2) := fun v =>
  (⟨if 3 * k - 6 ≤ v.1.val then v.1.val + 3 else v.1.val, by
      split <;> have := v.1.isLt <;> omega⟩,
    ⟨if 3 * k - 8 ≤ v.2.val then v.2.val + 3 else v.2.val, by
      split <;> have := v.2.isLt <;> omega⟩)

/-- Stepping rows and retaining columns sends every old affine U vertex to a
successor U vertex. -/
theorem residueTwoAffineStepKeepVertex_mem (k : Nat) (hk : 5 ≤ k)
    {v : GridVertex (3 * k + 2) (3 * k + 2)}
    (hv : v ∈ uResidueTwoAffine k) :
    residueTwoAffineStepKeepVertex k v ∈ uResidueTwoAffine (k + 1) := by
  classical
  simp only [uResidueTwoAffine, dif_pos hk,
    dif_pos (by omega : 5 ≤ k + 1), Finset.mem_image,
    residueTwoAffineOccurrences, Finset.mem_univ, true_and] at hv ⊢
  obtain ⟨x, hx⟩ := hv
  rcases x with ⟨r, c, copies⟩
  have ht : (k - 5) + 1 = (k + 1) - 5 := by omega
  let ir : Fin (residueTwoPumpMultiplicity 9 ((k + 1) - 5) r) :=
    Fin.cast (congrArg (fun t => residueTwoPumpMultiplicity 9 t r) ht)
      (residueTwoAffineCopyStep 9 (k - 5) r copies.1.1)
  let ic : Fin (residueTwoPumpMultiplicity 4 ((k + 1) - 5) c) :=
    Fin.cast (congrArg (fun t => residueTwoPumpMultiplicity 4 t c) ht)
      (residueTwoAffineCopyKeep 4 (k - 5) c copies.1.2)
  let row := residueTwoExpandIndex 9 ((k + 1) - 5) (by omega)
    (⟨r, ir⟩ : ResidueTwoAffineIndex 9 ((k + 1) - 5))
  let col := residueTwoExpandIndex 4 ((k + 1) - 5) (by omega)
    (⟨c, ic⟩ : ResidueTwoAffineIndex 4 ((k + 1) - 5))
  have hrowOld :
      (residueTwoAffineVertex (k - 5) ⟨r, c, copies⟩).1.val = v.1.val :=
    congrArg (fun z => z.1.val) hx
  have hcolOld :
      (residueTwoAffineVertex (k - 5) ⟨r, c, copies⟩).2.val = v.2.val :=
    congrArg (fun z => z.2.val) hx
  have hrow : row.val =
      if 3 * k - 6 ≤ v.1.val then v.1.val + 3 else v.1.val := by
    have hs := residueTwoExpandIndex_copyStep 9 (k - 5) (by omega)
      r copies.1.1
    have hcast : row.val =
        (residueTwoExpandIndex 9 ((k - 5) + 1) (by omega)
          ⟨r, residueTwoAffineCopyStep 9 (k - 5) r copies.1.1⟩).val := by
      exact residueTwoExpandIndex_copyStep_cast 9 (k - 5) ((k + 1) - 5)
        ht (by omega) r copies.1.1
    change row.val = _
    change (residueTwoExpandIndex 9 (k - 5) (by omega)
      ⟨r, copies.1.1⟩).val = v.1.val at hrowOld
    rw [hcast, hs, hrowOld]
    have hcut : 9 + 3 * (k - 5) = 3 * k - 6 := by omega
    rw [hcut]
  have hcol : col.val =
      if 3 * k - 8 ≤ v.2.val then v.2.val + 3 else v.2.val := by
    have hs := residueTwoExpandIndex_copyKeep 4 (k - 5) (by omega)
      c copies.1.2
    have hcast : col.val =
        (residueTwoExpandIndex 4 ((k - 5) + 1) (by omega)
          ⟨c, residueTwoAffineCopyKeep 4 (k - 5) c copies.1.2⟩).val := by
      exact residueTwoExpandIndex_copyKeep_cast 4 (k - 5) ((k + 1) - 5)
        ht (by omega) c copies.1.2
    change col.val = _
    change (residueTwoExpandIndex 4 (k - 5) (by omega)
      ⟨c, copies.1.2⟩).val = v.2.val at hcolOld
    rw [hcast, hs, hcolOld]
    have hcut : 4 + 3 + 3 * (k - 5) = 3 * k - 8 := by omega
    rw [hcut]
  let nextCopies :
      {p : Fin (residueTwoPumpMultiplicity 9 ((k + 1) - 5) r) ×
        Fin (residueTwoPumpMultiplicity 4 ((k + 1) - 5) c) //
          IsResidueTwoAffineBase r c} := ⟨(ir, ic), copies.2⟩
  let next : ResidueTwoAffineOccurrence ((k + 1) - 5) :=
    ⟨r, c, nextCopies⟩
  refine ⟨next, ?_⟩
  apply Prod.ext <;> apply Fin.ext
  · change row.val = _
    exact hrow
  · change col.val = _
    exact hcol

/-- Mixed successor embedding: row copy numbers are retained while column copy
numbers step. -/
def residueTwoAffineKeepStepVertex (k : Nat) :
    GridVertex (3 * k + 2) (3 * k + 2) →
      GridVertex (3 * (k + 1) + 2) (3 * (k + 1) + 2) := fun v =>
  (⟨if 3 * k - 3 ≤ v.1.val then v.1.val + 3 else v.1.val, by
      split <;> have := v.1.isLt <;> omega⟩,
    ⟨if 3 * k - 11 ≤ v.2.val then v.2.val + 3 else v.2.val, by
      split <;> have := v.2.isLt <;> omega⟩)

/-- Retaining rows and stepping columns sends every old affine U vertex to a
successor U vertex. -/
theorem residueTwoAffineKeepStepVertex_mem (k : Nat) (hk : 5 ≤ k)
    {v : GridVertex (3 * k + 2) (3 * k + 2)}
    (hv : v ∈ uResidueTwoAffine k) :
    residueTwoAffineKeepStepVertex k v ∈ uResidueTwoAffine (k + 1) := by
  classical
  simp only [uResidueTwoAffine, dif_pos hk,
    dif_pos (by omega : 5 ≤ k + 1), Finset.mem_image,
    residueTwoAffineOccurrences, Finset.mem_univ, true_and] at hv ⊢
  obtain ⟨x, hx⟩ := hv
  rcases x with ⟨r, c, copies⟩
  have ht : (k - 5) + 1 = (k + 1) - 5 := by omega
  let ir : Fin (residueTwoPumpMultiplicity 9 ((k + 1) - 5) r) :=
    Fin.cast (congrArg (fun t => residueTwoPumpMultiplicity 9 t r) ht)
      (residueTwoAffineCopyKeep 9 (k - 5) r copies.1.1)
  let ic : Fin (residueTwoPumpMultiplicity 4 ((k + 1) - 5) c) :=
    Fin.cast (congrArg (fun t => residueTwoPumpMultiplicity 4 t c) ht)
      (residueTwoAffineCopyStep 4 (k - 5) c copies.1.2)
  let row := residueTwoExpandIndex 9 ((k + 1) - 5) (by omega)
    (⟨r, ir⟩ : ResidueTwoAffineIndex 9 ((k + 1) - 5))
  let col := residueTwoExpandIndex 4 ((k + 1) - 5) (by omega)
    (⟨c, ic⟩ : ResidueTwoAffineIndex 4 ((k + 1) - 5))
  have hrowOld :
      (residueTwoAffineVertex (k - 5) ⟨r, c, copies⟩).1.val = v.1.val :=
    congrArg (fun z => z.1.val) hx
  have hcolOld :
      (residueTwoAffineVertex (k - 5) ⟨r, c, copies⟩).2.val = v.2.val :=
    congrArg (fun z => z.2.val) hx
  have hrow : row.val =
      if 3 * k - 3 ≤ v.1.val then v.1.val + 3 else v.1.val := by
    have hs := residueTwoExpandIndex_copyKeep 9 (k - 5) (by omega)
      r copies.1.1
    have hcast : row.val =
        (residueTwoExpandIndex 9 ((k - 5) + 1) (by omega)
          ⟨r, residueTwoAffineCopyKeep 9 (k - 5) r copies.1.1⟩).val := by
      exact residueTwoExpandIndex_copyKeep_cast 9 (k - 5) ((k + 1) - 5)
        ht (by omega) r copies.1.1
    change row.val = _
    change (residueTwoExpandIndex 9 (k - 5) (by omega)
      ⟨r, copies.1.1⟩).val = v.1.val at hrowOld
    rw [hcast, hs, hrowOld]
    have hcut : 9 + 3 + 3 * (k - 5) = 3 * k - 3 := by omega
    rw [hcut]
  have hcol : col.val =
      if 3 * k - 11 ≤ v.2.val then v.2.val + 3 else v.2.val := by
    have hs := residueTwoExpandIndex_copyStep 4 (k - 5) (by omega)
      c copies.1.2
    have hcast : col.val =
        (residueTwoExpandIndex 4 ((k - 5) + 1) (by omega)
          ⟨c, residueTwoAffineCopyStep 4 (k - 5) c copies.1.2⟩).val := by
      exact residueTwoExpandIndex_copyStep_cast 4 (k - 5) ((k + 1) - 5)
        ht (by omega) c copies.1.2
    change col.val = _
    change (residueTwoExpandIndex 4 (k - 5) (by omega)
      ⟨c, copies.1.2⟩).val = v.2.val at hcolOld
    rw [hcast, hs, hcolOld]
    have hcut : 4 + 3 * (k - 5) = 3 * k - 11 := by omega
    rw [hcut]
  let nextCopies :
      {p : Fin (residueTwoPumpMultiplicity 9 ((k + 1) - 5) r) ×
        Fin (residueTwoPumpMultiplicity 4 ((k + 1) - 5) c) //
          IsResidueTwoAffineBase r c} := ⟨(ir, ic), copies.2⟩
  let next : ResidueTwoAffineOccurrence ((k + 1) - 5) :=
    ⟨r, c, nextCopies⟩
  refine ⟨next, ?_⟩
  apply Prod.ext <;> apply Fin.ext
  · change row.val = _
    exact hrow
  · change col.val = _
    exact hcol

/-- Introduce a symbolic base occurrence directly into the affine pattern.
This is the coordinate-facing API used by uniform successor geometry proofs. -/
theorem residueTwoAffine_expanded_mem
    (k : Nat) (hk : 5 ≤ k)
    (r c : Fin 17)
    (ir : Fin (residueTwoPumpMultiplicity 9 (k - 5) r))
    (ic : Fin (residueTwoPumpMultiplicity 4 (k - 5) c))
    (hbase : IsResidueTwoAffineBase r c) :
    let row := residueTwoExpandIndex 9 (k - 5) (by omega)
      (⟨r, ir⟩ : ResidueTwoAffineIndex 9 (k - 5))
    let col := residueTwoExpandIndex 4 (k - 5) (by omega)
      (⟨c, ic⟩ : ResidueTwoAffineIndex 4 (k - 5))
    ((⟨row.val, by have := row.isLt; omega⟩,
      ⟨col.val, by have := col.isLt; omega⟩) :
        GridVertex (3 * k + 2) (3 * k + 2)) ∈ uResidueTwoAffine k := by
  classical
  simp only [uResidueTwoAffine, dif_pos hk, Finset.mem_image,
    residueTwoAffineOccurrences, Finset.mem_univ, true_and]
  let copies :
      {p : Fin (residueTwoPumpMultiplicity 9 (k - 5) r) ×
        Fin (residueTwoPumpMultiplicity 4 (k - 5) c) //
          IsResidueTwoAffineBase r c} :=
    ⟨(ir, ic), hbase⟩
  let x : ResidueTwoAffineOccurrence (k - 5) := ⟨r, c, copies⟩
  exact ⟨x, by
    apply Prod.ext <;> apply Fin.ext <;>
      simp [x, copies, residueTwoAffineVertex]⟩

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
