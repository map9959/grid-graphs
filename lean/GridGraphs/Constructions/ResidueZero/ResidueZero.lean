import Mathlib
import GridGraphs.Core.Defs

/-!
# The residue-zero phase construction

This file encodes the rows from `analysis/PHASE_PATTERN.md`.  The recursive
word is represented by `phaseRowsFrom`; all of its rows are interpreted at the
current width.  The set `uResidueZero` is constructed as the injective image of
the slots in its phase rows and four cap rows.  This presentation makes the
cardinality calculation independent of any graph-theoretic argument.
-/

namespace GridGraphs

/-- An ordinary phase row `R_a` or a seam phase row `S_a`. -/
inductive PhaseRow where
  | ordinary (a : Nat)
  | seam (a : Nat)
  deriving DecidableEq, Repr

/-- The base word `B_7`. -/
def phaseRowsBase : List PhaseRow :=
  [.ordinary 4, .ordinary 3, .ordinary 2, .seam 2,
   .ordinary 1, .ordinary 0, .seam 0, .ordinary 0,
   .seam 1, .ordinary 1, .ordinary 2, .seam 3,
   .ordinary 3, .seam 4, .ordinary 4, .ordinary 5,
   .ordinary 6]

/-- `phaseRowsFrom t` is `B_(7+t)`.  Every recursive step uses the rows at the
new width, as required by `B_(k+1) = R_(k-2) S_(k-2) B_k R_k`. -/
def phaseRowsFrom : Nat → List PhaseRow
  | 0 => phaseRowsBase
  | t + 1 =>
      [.ordinary (t + 5), .seam (t + 5)] ++ phaseRowsFrom t ++
        [.ordinary (t + 7)]

/-- The interior phase word `B_k`; it is empty outside its intended range. -/
def phaseRows (k : Nat) : List PhaseRow :=
  if 7 ≤ k then phaseRowsFrom (k - 7) else []

def PhaseRow.parameter : PhaseRow → Nat
  | .ordinary a => a
  | .seam a => a

@[simp] theorem phaseRowsFrom_length (t : Nat) :
    (phaseRowsFrom t).length = 17 + 3 * t := by
  induction t with
  | zero => decide
  | succ t ih => simp [phaseRowsFrom, ih]; omega

theorem phaseRows_length (k : Nat) (hk : 7 ≤ k) :
    (phaseRows k).length = 3 * k - 4 := by
  simp [phaseRows, hk, phaseRowsFrom_length]
  omega

/-- Every parameter occurring in `B_(7+t)` is below its current `k`. -/
theorem phaseRowsFrom_parameter_lt (t : Nat) (row : PhaseRow)
    (hrow : row ∈ phaseRowsFrom t) :
    row.parameter < 7 + t := by
  induction t with
  | zero =>
      simp [phaseRowsFrom, phaseRowsBase] at hrow
      rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [PhaseRow.parameter]
  | succ t ih =>
      rcases List.mem_append.mp hrow with hmain | htail
      · rcases List.mem_append.mp hmain with hprefix | hprev
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hprefix
          rcases hprefix with rfl | hprefix
          · simp [PhaseRow.parameter]; omega
          · rcases hprefix with rfl | hfalse
            · simp [PhaseRow.parameter]; omega
        · have := ih hprev
          omega
      · simp only [List.mem_singleton] at htail
        subst row
        simp [PhaseRow.parameter]
        omega

theorem phaseRows_parameter_lt (k : Nat) (hk : 7 ≤ k) (row : PhaseRow)
    (hrow : row ∈ phaseRows k) :
    row.parameter < k := by
  have h := phaseRowsFrom_parameter_lt (k - 7) row (by simpa [phaseRows, hk] using hrow)
  have hk' : 7 + (k - 7) = k := by omega
  omega

/-- Number of U-slots in a phase row. -/
def phaseSlotCount (k : Nat) : PhaseRow → Nat
  | .ordinary _ => 2 * k
  | .seam _ => 2 * k - 1

/-- Sum of the phase-row sizes, with every old row interpreted at width `3k`. -/
theorem phaseRowsFrom_slot_sum (k t : Nat) (hk : 1 ≤ k) :
    ((phaseRowsFrom t).map (phaseSlotCount k)).sum =
      (12 + 2 * t) * (2 * k) + (5 + t) * (2 * k - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hsub : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  induction t with
  | zero =>
      simp only [phaseRowsFrom, phaseRowsBase, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, phaseSlotCount, Nat.mul_zero, Nat.add_zero]
      rw [hsub]
      ring
  | succ t ih =>
      simp only [phaseRowsFrom, List.map_append, List.map_cons, List.map_nil,
        List.sum_append, List.sum_cons, List.sum_nil, phaseSlotCount, ih, Nat.add_zero]
      rw [hsub]
      ring

theorem phaseRows_slot_sum (k : Nat) (hk : 7 ≤ k) :
    ((phaseRows k).map (phaseSlotCount k)).sum = 6 * k ^ 2 - 9 * k + 2 := by
  rw [phaseRows, if_pos hk, phaseRowsFrom_slot_sum k (k - 7) (by omega)]
  have hord : 12 + 2 * (k - 7) = 2 * k - 2 := by omega
  have hseam : 5 + (k - 7) = k - 2 := by omega
  rw [hord, hseam]
  obtain ⟨t, rfl⟩ : ∃ t, k = 7 + t := ⟨k - 7, by omega⟩
  have h₁ : 2 * (7 + t) - 2 = 12 + 2 * t := by omega
  have h₂ : 2 * (7 + t) - 1 = 13 + 2 * t := by omega
  have h₃ : 7 + t - 2 = 5 + t := by omega
  have h₄ : 6 * (7 + t) ^ 2 - 9 * (7 + t) + 2 =
      233 + 75 * t + 6 * t ^ 2 := by
    ring_nf
    omega
  rw [h₁, h₂, h₃, h₄]
  ring

/-- The finite slots occupied by U in one phase row. -/
abbrev PhaseSlot (k : Nat) (row : PhaseRow) := Fin (phaseSlotCount k row)

instance (k : Nat) (row : PhaseRow) : Fintype (PhaseSlot k row) := by
  unfold PhaseSlot
  infer_instance

/-- Column occupied by a phase-row slot.  The three branches enumerate,
respectively, columns congruent to 1, the left columns congruent to 2, and the
right columns congruent to 0. -/
def phaseColumn (k : Nat) (row : PhaseRow) (j : PhaseSlot k row) : Nat :=
  match row with
  | .ordinary a =>
      if j.val < k then 3 * j.val + 1
      else if j.val < k + a + 1 then 3 * (j.val - k) + 2
      else 3 * (j.val - k)
  | .seam a =>
      if j.val < k then 3 * j.val + 1
      else if j.val < k + a then 3 * (j.val - k) + 2
      else 3 * (j.val - k + 1)

theorem phaseColumn_lt {k : Nat} {row : PhaseRow} (hrow : row.parameter < k)
    (j : PhaseSlot k row) : phaseColumn k row j < 3 * k := by
  have hj := j.isLt
  cases row with
  | ordinary a =>
      simp [PhaseRow.parameter] at hrow
      change j.val < 2 * k at hj
      by_cases h1 : j.val < k
      · simp [phaseColumn, h1]; omega
      · by_cases h2 : j.val < k + a + 1
        · simp [phaseColumn, h1, h2]; omega
        · simp [phaseColumn, h1, h2]; omega
  | seam a =>
      simp [PhaseRow.parameter] at hrow
      change j.val < 2 * k - 1 at hj
      by_cases h1 : j.val < k
      · simp [phaseColumn, h1]; omega
      · by_cases h2 : j.val < k + a
        · simp [phaseColumn, h1, h2]; omega
        · simp [phaseColumn, h1, h2]; omega

theorem phaseColumn_injective {k : Nat} (row : PhaseRow)
    (hrow : row.parameter < k) :
    Function.Injective (phaseColumn k row) := by
  intro x y hxy
  apply Fin.ext
  cases row with
  | ordinary a =>
      unfold phaseColumn at hxy
      by_cases hx : x.val < k <;> by_cases hy : y.val < k
      · simp [hx, hy] at hxy; omega
      · simp [hx, hy] at hxy
        split at hxy <;> omega
      · simp [hx, hy] at hxy
        split at hxy <;> omega
      · simp only [if_neg hx, if_neg hy] at hxy
        by_cases hx2 : x.val < k + a + 1 <;>
          by_cases hy2 : y.val < k + a + 1 <;>
          simp [hx2, hy2] at hxy <;> omega
  | seam a =>
      unfold phaseColumn at hxy
      by_cases hx : x.val < k <;> by_cases hy : y.val < k
      · simp [hx, hy] at hxy; omega
      · simp [hx, hy] at hxy
        split at hxy <;> omega
      · simp [hx, hy] at hxy
        split at hxy <;> omega
      · simp only [if_neg hx, if_neg hy] at hxy
        by_cases hx2 : x.val < k + a <;> by_cases hy2 : y.val < k + a <;>
          simp [hx2, hy2] at hxy <;> omega

/-- Indices of all vertices in the construction. -/
abbrev ResidueZeroIndex (k : Nat) :=
  Fin (3 * k) ⊕
    Fin (3 * k - 1) ⊕
      Fin 1 ⊕
        (Σ i : Fin (phaseRows k).length, PhaseSlot k ((phaseRows k).get i))

instance (k : Nat) : Fintype (ResidueZeroIndex k) := by
  unfold ResidueZeroIndex
  infer_instance

/-- Place the row slots into the `3k × 3k` square.  The first three summands
are the all-U row, `.U^(3k-1)`, and `.U.^(3k-2)`; the sigma summand is `B_k`.
The initial empty row contributes no index. -/
def residueZeroVertex (k : Nat) (hk : 7 ≤ k) :
    ResidueZeroIndex k → GridVertex (3 * k) (3 * k)
  | .inl c => (⟨1, by omega⟩, c)
  | .inr (.inl c) => (⟨3 * k - 2, by omega⟩, ⟨c.val + 1, by omega⟩)
  | .inr (.inr (.inl _)) => (⟨3 * k - 1, by omega⟩, ⟨1, by omega⟩)
  | .inr (.inr (.inr ⟨i, j⟩)) =>
      (⟨i.val + 2, by
          have hi := i.isLt
          have hlen := phaseRows_length k hk
          omega⟩,
       ⟨phaseColumn k ((phaseRows k).get i) j, by
          have hm := List.get_mem (phaseRows k) i
          have hp := phaseRows_parameter_lt k hk _ hm
          exact phaseColumn_lt hp j⟩)

theorem residueZeroVertex_injective (k : Nat) (hk : 7 ≤ k) :
    Function.Injective (residueZeroVertex k hk) := by
  intro x y hxy
  have hrow := congrArg (fun v => v.1.val) hxy
  rcases x with c | x
  · rcases y with d | y
    · apply congrArg Sum.inl
      apply Fin.ext
      simpa [residueZeroVertex] using congrArg (fun v => v.2.val) hxy
    · rcases y with d | y
      · simp [residueZeroVertex] at hrow; omega
      · rcases y with d | y
        · simp [residueZeroVertex] at hrow; omega
        · rcases y with ⟨j, y⟩
          have hj := j.isLt
          have hlen := phaseRows_length k hk
          simp [residueZeroVertex] at hrow
  · rcases x with c | x
    · rcases y with d | y
      · simp [residueZeroVertex] at hrow; omega
      · rcases y with d | y
        · apply congrArg Sum.inr
          apply congrArg Sum.inl
          apply Fin.ext
          simpa [residueZeroVertex] using congrArg (fun v => v.2.val) hxy
        · rcases y with d | y
          · simp [residueZeroVertex] at hrow; omega
          · rcases y with ⟨j, y⟩
            have hj := j.isLt
            have hlen := phaseRows_length k hk
            simp [residueZeroVertex] at hrow
            omega
    · rcases x with c | x
      · rcases y with d | y
        · simp [residueZeroVertex] at hrow; omega
        · rcases y with d | y
          · simp [residueZeroVertex] at hrow; omega
          · rcases y with d | y
            · apply congrArg Sum.inr
              apply congrArg Sum.inr
              apply congrArg Sum.inl
              exact Subsingleton.elim _ _
            · rcases y with ⟨j, y⟩
              have hj := j.isLt
              have hlen := phaseRows_length k hk
              simp [residueZeroVertex] at hrow
              omega
      · rcases x with ⟨i, x⟩
        have hi := i.isLt
        have hlen := phaseRows_length k hk
        rcases y with d | y
        · simp [residueZeroVertex] at hrow
        · rcases y with d | y
          · simp [residueZeroVertex] at hrow; omega
          · rcases y with d | y
            · simp [residueZeroVertex] at hrow; omega
            · rcases y with ⟨j, y⟩
              have hij : i = j := Fin.ext (by simpa [residueZeroVertex] using hrow)
              subst j
              have hp := phaseRows_parameter_lt k hk _ (List.get_mem (phaseRows k) i)
              have hcol : phaseColumn k ((phaseRows k).get i) x =
                  phaseColumn k ((phaseRows k).get i) y := by
                simpa [residueZeroVertex] using congrArg (fun v => v.2.val) hxy
              have hslot : x = y := phaseColumn_injective _ hp hcol
              subst y
              rfl

/-- The complete residue-zero U-set on the `3k × 3k` square. -/
def uResidueZero (k : Nat) (hk : 7 ≤ k) :
    Finset (GridVertex (3 * k) (3 * k)) :=
  Finset.univ.image (residueZeroVertex k hk)

/-- The residue-zero phase construction has the target cardinality. -/
theorem uResidueZero_card (k : Nat) (hk : 7 ≤ k) :
    (uResidueZero k hk).card = 6 * k ^ 2 - 3 * k + 2 := by
  rw [uResidueZero, Finset.card_image_of_injective _ (residueZeroVertex_injective k hk)]
  simp only [Finset.card_univ]
  unfold ResidueZeroIndex
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_sigma, PhaseSlot]
  rw [show (∑ i : Fin (phaseRows k).length,
      phaseSlotCount k ((phaseRows k).get i)) =
      ((phaseRows k).map (phaseSlotCount k)).sum by
        exact Fin.sum_univ_fun_getElem (phaseRows k) (phaseSlotCount k)]
  rw [phaseRows_slot_sum k hk]
  obtain ⟨t, rfl⟩ : ∃ t, k = 7 + t := ⟨k - 7, by omega⟩
  ring_nf
  omega

end GridGraphs
