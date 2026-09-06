import GridGraphs.ResidueTwoAffine
import GridGraphs.FiniteDiagonalTwenty

/-!
# The exact-cost residue-two affine family

This family pumps the explicit twenty-by-twenty certificate in rows 5--7 and
columns 11--13.  Unlike the seventeen-based affine family, its cardinality has
the exact linear coefficient required by the stable residue-two bound.
-/

namespace GridGraphs

open Finset

/-- Rows of the twenty-by-twenty exact base. -/
def residueTwoExactBaseRow : Nat → Finset Nat
  | 0 => [1].toFinset
  | 1 => [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19].toFinset
  | 2 => [1, 2, 3, 4, 6, 7, 9, 10, 12, 13, 15, 16, 18, 19].toFinset
  | 3 => [1, 2, 4, 6, 7, 9, 10, 12, 13, 15, 16, 17, 18].toFinset
  | 4 => [1, 2, 4, 5, 6, 7, 9, 10, 12, 13, 14, 15, 17, 18].toFinset
  | 5 => [1, 2, 4, 5, 7, 9, 10, 11, 12, 14, 15, 17, 18].toFinset
  | 6 | 7 => [1, 2, 4, 5, 7, 8, 9, 11, 12, 14, 15, 17, 18].toFinset
  | 8 => [1, 2, 4, 5, 6, 7, 9, 11, 12, 14, 15, 17, 18].toFinset
  | 9 => [1, 2, 4, 6, 7, 8, 9, 11, 12, 14, 15, 17, 18].toFinset
  | 10 | 11 | 13 | 17 => [1, 2, 4, 5, 6, 8, 9, 11, 12, 14, 15, 17, 18].toFinset
  | 12 => [1, 2, 4, 6, 8, 9, 11, 12, 14, 15, 17, 18].toFinset
  | 14 | 16 => [1, 2, 3, 4, 6, 7, 8, 9, 11, 12, 14, 15, 17, 18].toFinset
  | 15 => [1, 3, 4, 6, 7, 9, 11, 12, 14, 15, 17, 18].toFinset
  | 18 => [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18].toFinset
  | 19 => [1, 18].toFinset
  | _ => ∅

/-- Membership in the explicit exact base. -/
def IsResidueTwoExactBase (r c : Fin 20) : Prop :=
  c.val ∈ residueTwoExactBaseRow r.val

instance (r c : Fin 20) : Decidable (IsResidueTwoExactBase r c) := by
  unfold IsResidueTwoExactBase
  infer_instance

/-- Multiplicity of a coordinate in the exact twenty-based pump. -/
def residueTwoExactMultiplicity (cut t : Nat) (i : Fin 20) : Nat :=
  if cut ≤ i.val ∧ i.val < cut + 3 then t + 1 else 1

/-- A base coordinate together with its selected copy. -/
structure ResidueTwoExactIndex (cut t : Nat) where
  base : Fin 20
  copy : Fin (residueTwoExactMultiplicity cut t base)
  deriving DecidableEq, Fintype

/-- Expand a base coordinate into the board enlarged by `3t`. -/
def residueTwoExactExpandIndex (cut t : Nat) (hcut : cut + 3 ≤ 20)
    (x : ResidueTwoExactIndex cut t) : Fin (20 + 3 * t) :=
  if hpump : cut ≤ x.base.val ∧ x.base.val < cut + 3 then
    ⟨x.base.val + 3 * x.copy.val, by
      have hc := x.copy.isLt
      simp only [residueTwoExactMultiplicity, if_pos hpump] at hc
      omega⟩
  else if habove : cut + 3 ≤ x.base.val then
    ⟨x.base.val + 3 * t, by have := x.base.isLt; omega⟩
  else
    ⟨x.base.val, by omega⟩

@[simp] theorem residueTwoExactExpandIndex_of_pump (cut t : Nat)
    (hcut : cut + 3 ≤ 20) (x : ResidueTwoExactIndex cut t)
    (h : cut ≤ x.base.val ∧ x.base.val < cut + 3) :
    (residueTwoExactExpandIndex cut t hcut x).val =
      x.base.val + 3 * x.copy.val := by
  simp [residueTwoExactExpandIndex, h]

@[simp] theorem residueTwoExactExpandIndex_of_above (cut t : Nat)
    (hcut : cut + 3 ≤ 20) (x : ResidueTwoExactIndex cut t)
    (hp : ¬(cut ≤ x.base.val ∧ x.base.val < cut + 3))
    (h : cut + 3 ≤ x.base.val) :
    (residueTwoExactExpandIndex cut t hcut x).val = x.base.val + 3 * t := by
  simp [residueTwoExactExpandIndex, hp, h]

@[simp] theorem residueTwoExactExpandIndex_of_below (cut t : Nat)
    (hcut : cut + 3 ≤ 20) (x : ResidueTwoExactIndex cut t)
    (hp : ¬(cut ≤ x.base.val ∧ x.base.val < cut + 3))
    (h : ¬cut + 3 ≤ x.base.val) :
    (residueTwoExactExpandIndex cut t hcut x).val = x.base.val := by
  simp [residueTwoExactExpandIndex, hp, h]

/-- Different symbolic copies expand to different coordinates. -/
theorem residueTwoExactExpandIndex_injective (cut t : Nat)
    (hcut : cut + 3 ≤ 20) :
    Function.Injective (residueTwoExactExpandIndex cut t hcut) := by
  rintro ⟨xb, xc⟩ ⟨yb, yc⟩ h
  have hv := congrArg Fin.val h
  by_cases xpump : cut ≤ xb.val ∧ xb.val < cut + 3
  · rw [residueTwoExactExpandIndex_of_pump cut t hcut ⟨xb, xc⟩ xpump] at hv
    by_cases ypump : cut ≤ yb.val ∧ yb.val < cut + 3
    · rw [residueTwoExactExpandIndex_of_pump cut t hcut ⟨yb, yc⟩ ypump] at hv
      change xb.val + 3 * xc.val = yb.val + 3 * yc.val at hv
      have hxc := xc.isLt
      have hyc := yc.isLt
      simp only [residueTwoExactMultiplicity, if_pos xpump] at hxc
      simp only [residueTwoExactMultiplicity, if_pos ypump] at hyc
      have hb : xb = yb := Fin.ext (by omega)
      subst yb
      have hc : xc = yc := Fin.ext (by omega)
      subst yc
      rfl
    · by_cases yabove : cut + 3 ≤ yb.val
      · rw [residueTwoExactExpandIndex_of_above cut t hcut ⟨yb, yc⟩ ypump yabove] at hv
        change xb.val + 3 * xc.val = yb.val + 3 * t at hv
        have hxc := xc.isLt
        simp only [residueTwoExactMultiplicity, if_pos xpump] at hxc
        omega
      · rw [residueTwoExactExpandIndex_of_below cut t hcut ⟨yb, yc⟩ ypump yabove] at hv
        change xb.val + 3 * xc.val = yb.val at hv
        omega
  · by_cases xabove : cut + 3 ≤ xb.val
    · rw [residueTwoExactExpandIndex_of_above cut t hcut ⟨xb, xc⟩ xpump xabove] at hv
      by_cases ypump : cut ≤ yb.val ∧ yb.val < cut + 3
      · rw [residueTwoExactExpandIndex_of_pump cut t hcut ⟨yb, yc⟩ ypump] at hv
        change xb.val + 3 * t = yb.val + 3 * yc.val at hv
        have hyc := yc.isLt
        simp only [residueTwoExactMultiplicity, if_pos ypump] at hyc
        omega
      · by_cases yabove : cut + 3 ≤ yb.val
        · rw [residueTwoExactExpandIndex_of_above cut t hcut ⟨yb, yc⟩ ypump yabove] at hv
          change xb.val + 3 * t = yb.val + 3 * t at hv
          have hb : xb = yb := Fin.ext (by omega)
          subst yb
          have hxc := xc.isLt
          have hyc := yc.isLt
          simp only [residueTwoExactMultiplicity, if_neg xpump] at hxc hyc
          have hc : xc = yc := Fin.ext (by omega)
          subst yc
          rfl
        · rw [residueTwoExactExpandIndex_of_below cut t hcut ⟨yb, yc⟩ ypump yabove] at hv
          change xb.val + 3 * t = yb.val at hv
          omega
    · rw [residueTwoExactExpandIndex_of_below cut t hcut ⟨xb, xc⟩ xpump xabove] at hv
      by_cases ypump : cut ≤ yb.val ∧ yb.val < cut + 3
      · rw [residueTwoExactExpandIndex_of_pump cut t hcut ⟨yb, yc⟩ ypump] at hv
        change xb.val = yb.val + 3 * yc.val at hv
        omega
      · by_cases yabove : cut + 3 ≤ yb.val
        · rw [residueTwoExactExpandIndex_of_above cut t hcut ⟨yb, yc⟩ ypump yabove] at hv
          change xb.val = yb.val + 3 * t at hv
          omega
        · rw [residueTwoExactExpandIndex_of_below cut t hcut ⟨yb, yc⟩ ypump yabove] at hv
          change xb.val = yb.val at hv
          have hb : xb = yb := Fin.ext (by omega)
          subst yb
          have hxc := xc.isLt
          have hyc := yc.isLt
          simp only [residueTwoExactMultiplicity, if_neg xpump] at hxc hyc
          have hc : xc = yc := Fin.ext (by omega)
          subst yc
          rfl

/-- Symbolic U occurrences after `t` exact-cost pumps. -/
abbrev ResidueTwoExactOccurrence (t : Nat) :=
  Σ r : Fin 20, Σ c : Fin 20,
    {_copies : Fin (residueTwoExactMultiplicity 5 t r) ×
      Fin (residueTwoExactMultiplicity 11 t c) // IsResidueTwoExactBase r c}

def residueTwoExactOccurrences (t : Nat) : Finset (ResidueTwoExactOccurrence t) :=
  Finset.univ

/-- Map a symbolic occurrence to the enlarged square. -/
def residueTwoExactVertex (t : Nat) (x : ResidueTwoExactOccurrence t) :
    GridVertex (20 + 3 * t) (20 + 3 * t) :=
  (residueTwoExactExpandIndex 5 t (by omega) ⟨x.1, x.2.2.val.1⟩,
    residueTwoExactExpandIndex 11 t (by omega) ⟨x.2.1, x.2.2.val.2⟩)

theorem residueTwoExactVertex_injective (t : Nat) :
    Function.Injective (residueTwoExactVertex t) := by
  intro x y h
  have hr := residueTwoExactExpandIndex_injective 5 t (by omega)
    (congrArg Prod.fst h)
  have hc := residueTwoExactExpandIndex_injective 11 t (by omega)
    (congrArg Prod.snd h)
  cases x with
  | mk xr xs =>
    cases y with
    | mk yr ys =>
      have hrb : xr = yr := congrArg ResidueTwoExactIndex.base hr
      subst yr
      cases xs with
      | mk xc xcopies =>
        cases ys with
        | mk yc ycopies =>
          have hcb : xc = yc := congrArg ResidueTwoExactIndex.base hc
          subst yc
          congr 2
          apply Subtype.ext
          apply Prod.ext
          · apply Fin.ext
            exact congrArg (fun z => z.copy.val) hr
          · apply Fin.ext
            exact congrArg (fun z => z.copy.val) hc

/-- The exact-cost pattern on side `3k+2`, based at `k=6`. -/
def uResidueTwoExact (k : Nat) :
    Finset (GridVertex (3 * k + 2) (3 * k + 2)) :=
  if hk : 6 ≤ k then
    let castVertex : GridVertex (20 + 3 * (k - 6)) (20 + 3 * (k - 6)) →
        GridVertex (3 * k + 2) (3 * k + 2) := fun x =>
      (⟨x.1.val, by have := x.1.isLt; omega⟩,
        ⟨x.2.val, by have := x.2.isLt; omega⟩)
    (residueTwoExactOccurrences (k - 6)).image
      (fun x => castVertex (residueTwoExactVertex (k - 6) x))
  else ∅

/-- The exact base predicate as a finset. -/
private def residueTwoExactBase : Finset (GridVertex 20 20) :=
  Finset.univ.filter fun v => IsResidueTwoExactBase v.1 v.2

private theorem uResidueTwoExact_six_eq_base :
    uResidueTwoExact 6 = residueTwoExactBase := by
  classical
  ext v
  simp only [uResidueTwoExact, dif_pos (by omega : 6 ≤ 6), Finset.mem_image,
    residueTwoExactOccurrences, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, hx⟩
    have hr : x.1 = v.1 := Fin.ext (by
      have h := congrArg (fun z => z.1.val) hx
      have hcopy : x.2.2.val.1.val = 0 := by
        have hlt := x.2.2.val.1.isLt
        by_cases hp : 5 ≤ x.1.val ∧ x.1.val < 5 + 3
        · simp only [Nat.sub_self, residueTwoExactMultiplicity, if_pos hp] at hlt
          omega
        · simp only [Nat.sub_self, residueTwoExactMultiplicity, if_neg hp] at hlt
          omega
      simpa [residueTwoExactVertex, residueTwoExactExpandIndex,
        residueTwoExactMultiplicity, hcopy] using h)
    have hc : x.2.1 = v.2 := Fin.ext (by
      have h := congrArg (fun z => z.2.val) hx
      have hcopy : x.2.2.val.2.val = 0 := by
        have hlt := x.2.2.val.2.isLt
        by_cases hp : 11 ≤ x.2.1.val ∧ x.2.1.val < 11 + 3
        · simp only [Nat.sub_self, residueTwoExactMultiplicity, if_pos hp] at hlt
          omega
        · simp only [Nat.sub_self, residueTwoExactMultiplicity, if_neg hp] at hlt
          omega
      simpa [residueTwoExactVertex, residueTwoExactExpandIndex,
        residueTwoExactMultiplicity, hcopy] using h)
    have hvbase : v = (x.1, x.2.1) := Prod.ext hr.symm hc.symm
    rw [hvbase]
    simpa [residueTwoExactBase] using x.2.2.property
  · intro hv
    have hbase : IsResidueTwoExactBase v.1 v.2 := by
      simpa [residueTwoExactBase] using hv
    let copies :
        {p : Fin (residueTwoExactMultiplicity 5 0 v.1) ×
          Fin (residueTwoExactMultiplicity 11 0 v.2) //
          IsResidueTwoExactBase v.1 v.2} :=
      ⟨(⟨0, by simp [residueTwoExactMultiplicity]⟩,
        ⟨0, by simp [residueTwoExactMultiplicity]⟩), hbase⟩
    let x : ResidueTwoExactOccurrence 0 := ⟨v.1, v.2, copies⟩
    refine ⟨x, ?_⟩
    apply Prod.ext <;> apply Fin.ext <;>
      simp [x, copies, residueTwoExactVertex, residueTwoExactExpandIndex]

set_option maxRecDepth 100000 in
private theorem residueTwoExactBase_eq_finiteU20 :
    residueTwoExactBase = finiteU20 := by rfl

/-- At zero pumping, the exact symbolic pattern is the explicit twenty by
twenty construction. -/
theorem uResidueTwoExact_six : uResidueTwoExact 6 = finiteU20 :=
  uResidueTwoExact_six_eq_base.trans residueTwoExactBase_eq_finiteU20

set_option maxHeartbeats 1000000 in
/-- The twenty-base decomposes into 6 doubly carried, 65 singly carried,
and 179 fixed U vertices. -/
theorem residueTwoExact_weighted_base (t : Nat) :
    ∑ r : Fin 20, ∑ c : Fin 20,
      (if IsResidueTwoExactBase r c then
        residueTwoExactMultiplicity 5 t r * residueTwoExactMultiplicity 11 t c
      else 0) = 6 * (t + 1) ^ 2 + 65 * (t + 1) + 179 := by
  norm_num only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ,
    IsResidueTwoExactBase, residueTwoExactBaseRow, List.mem_toFinset,
    List.mem_cons, List.not_mem_nil, residueTwoExactMultiplicity,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff,
    and_self, and_false, false_and, or_true, true_or, or_false, false_or,
    if_true, if_false, Nat.mul_one, Nat.one_mul, Nat.add_zero]
  ring_nf

theorem residueTwoExactOccurrences_card (t : Nat) :
    (residueTwoExactOccurrences t).card =
      ∑ r : Fin 20, ∑ c : Fin 20,
        (if IsResidueTwoExactBase r c then
          residueTwoExactMultiplicity 5 t r * residueTwoExactMultiplicity 11 t c
        else 0) := by
  classical
  simp only [residueTwoExactOccurrences, Finset.card_univ, Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro c _
  by_cases h : IsResidueTwoExactBase r c <;> simp [h]

/-- Exact U count needed by the residue-two tail. -/
theorem uResidueTwoExact_card (k : Nat) (hk : 6 ≤ k) :
    (uResidueTwoExact k).card = 6 * k ^ 2 + 5 * k + 4 := by
  classical
  simp only [uResidueTwoExact, dif_pos hk]
  rw [Finset.card_image_of_injective _]
  · rw [residueTwoExactOccurrences_card, residueTwoExact_weighted_base]
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
    simp
    ring_nf
  · intro x y h
    apply residueTwoExactVertex_injective (k - 6)
    apply Prod.ext <;> apply Fin.ext
    · exact congrArg (fun z => z.1.val) h
    · exact congrArg (fun z => z.2.val) h

/-- One exact pump costs `12k+11` U vertices. -/
theorem uResidueTwoExact_card_step (k : Nat) (hk : 6 ≤ k) :
    (uResidueTwoExact (k + 1)).card =
      (uResidueTwoExact k).card + (12 * k + 11) := by
  rw [uResidueTwoExact_card (k + 1) (by omega), uResidueTwoExact_card k hk]
  ring

/-- Two exact pumps cost `24k+34` U vertices. -/
theorem uResidueTwoExact_card_two_step (k : Nat) (hk : 6 ≤ k) :
    (uResidueTwoExact (k + 2)).card =
      (uResidueTwoExact k).card + (24 * k + 34) := by
  rw [uResidueTwoExact_card (k + 2) (by omega), uResidueTwoExact_card k hk]
  ring

/-- Exact complement count of the new family. -/
theorem uResidueTwoExact_compl_card (k : Nat) (hk : 6 ≤ k) :
    ((Finset.univ : Finset (GridVertex (3 * k + 2) (3 * k + 2))) \
      uResidueTwoExact k).card = 3 * k ^ 2 + 7 * k := by
  rw [Finset.card_sdiff, Finset.inter_univ, uResidueTwoExact_card k hk]
  have htotal :
      Fintype.card (GridVertex (3 * k + 2) (3 * k + 2)) =
        (3 * k + 2) * (3 * k + 2) := by
    unfold GridVertex
    simp
  rw [Finset.card_univ, htotal]
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  ring_nf
  omega

/-- The existing twenty-by-twenty ranked certificate realizes the exact-cost
base value, independently of the symbolic representation above. -/
theorem residueTwoExact_base_le_maxPreserved :
    3 * 6 ^ 2 + 7 * 6 ≤ maxPreserved (3 * 6 + 2) (3 * 6 + 2) := by
  norm_num
  exact oneHundredFifty_le_maxPreserved_twenty_twenty

end GridGraphs
