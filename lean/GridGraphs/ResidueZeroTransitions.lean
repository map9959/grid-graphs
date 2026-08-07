import GridGraphs.ResidueZeroDual

/-!
# Local transitions in the residue-zero phase word

This file records the column images of ordinary rows `R_a` and seam rows
`S_a`.  It then packages the horizontal runs and the common columns used when
two consecutive rows are attached in the dual frontier argument.
-/

namespace GridGraphs

open SimpleGraph

/-- A column occupied by a slot of a phase row. -/
def PhaseOccupied (k : Nat) (row : PhaseRow) (c : Nat) : Prop :=
  ∃ j : PhaseSlot k row, phaseColumn k row j = c

/-- The exact image of an ordinary row `R_a`. -/
theorem phaseOccupied_ordinary_iff {k a c : Nat} (_ha : a < k) :
    PhaseOccupied k (.ordinary a) c ↔
      (∃ q < k, c = 3 * q + 1) ∨
      (∃ q < k, q ≤ a ∧ c = 3 * q + 2) ∨
      (∃ q < k, a < q ∧ c = 3 * q) := by
  constructor
  · rintro ⟨j, rfl⟩
    have hj : j.val < 2 * k := j.isLt
    by_cases h₁ : j.val < k
    · exact Or.inl ⟨j.val, h₁, by simp [phaseColumn, h₁]⟩
    · by_cases h₂ : j.val < k + a + 1
      · exact Or.inr (Or.inl ⟨j.val - k, by omega, by omega,
          by simp [phaseColumn, h₁, h₂]⟩)
      · exact Or.inr (Or.inr ⟨j.val - k, by omega, by omega,
          by simp [phaseColumn, h₁, h₂]⟩)
  · rintro (⟨q, hq, rfl⟩ | ⟨q, hq, hqa, rfl⟩ | ⟨q, hq, haq, rfl⟩)
    · exact ⟨⟨q, by simp [phaseSlotCount]; omega⟩, by
        simp [phaseColumn, hq]⟩
    · exact ⟨⟨k + q, by simp [phaseSlotCount]; omega⟩, by
        simp [phaseColumn, show ¬k + q < k by omega,
          show k + q < k + a + 1 by omega]⟩
    · exact ⟨⟨k + q, by simp [phaseSlotCount]; omega⟩, by
        simp [phaseColumn, show ¬k + q < k by omega,
          show ¬k + q < k + a + 1 by omega]⟩

/-- The exact image of a seam row `S_a`; compared with `R_a`, its pivot
column `3a+2` is absent. -/
theorem phaseOccupied_seam_iff {k a c : Nat} (ha : a < k) :
    PhaseOccupied k (.seam a) c ↔
      (∃ q < k, c = 3 * q + 1) ∨
      (∃ q < k, q < a ∧ c = 3 * q + 2) ∨
      (∃ q < k, a < q ∧ c = 3 * q) := by
  constructor
  · rintro ⟨j, rfl⟩
    have hj : j.val < 2 * k - 1 := j.isLt
    by_cases h₁ : j.val < k
    · exact Or.inl ⟨j.val, h₁, by simp [phaseColumn, h₁]⟩
    · by_cases h₂ : j.val < k + a
      · exact Or.inr (Or.inl ⟨j.val - k, by omega, by omega,
          by simp [phaseColumn, h₁, h₂]⟩)
      · refine Or.inr (Or.inr ⟨j.val - k + 1, ?_, by omega, ?_⟩)
        · omega
        · simp [phaseColumn, h₁, h₂]
  · rintro (⟨q, hq, rfl⟩ | ⟨q, hq, hqa, rfl⟩ | ⟨q, hq, haq, rfl⟩)
    · exact ⟨⟨q, by simp [phaseSlotCount]; omega⟩, by
        simp [phaseColumn, hq]⟩
    · exact ⟨⟨k + q, by simp [phaseSlotCount]; omega⟩, by
        simp [phaseColumn, show ¬k + q < k by omega,
          show k + q < k + a by omega]⟩
    · exact ⟨⟨k + (q - 1), by simp [phaseSlotCount]; omega⟩, by
        simp [phaseColumn, show ¬k + (q - 1) < k by omega,
          show ¬k + (q - 1) < k + a by omega]
        omega⟩

/-- Every phase row contains the full residue-one backbone. -/
theorem phaseOccupied_backbone {k q : Nat} {row : PhaseRow}
    (hq : q < k) : PhaseOccupied k row (3 * q + 1) := by
  cases row with
  | ordinary a =>
      exact ⟨⟨q, by simp [phaseSlotCount]; omega⟩, by simp [phaseColumn, hq]⟩
  | seam a =>
      -- The backbone does not depend on the parameter, even outside valid rows.
      exact ⟨⟨q, by simp [phaseSlotCount]; omega⟩, by simp [phaseColumn, hq]⟩

/-- The left horizontal `UU` runs in an ordinary row. -/
theorem ordinary_left_run {k a q : Nat} (ha : a < k) (hq : q < k) (hqa : q ≤ a) :
    PhaseOccupied k (.ordinary a) (3 * q + 1) ∧
      PhaseOccupied k (.ordinary a) (3 * q + 2) := by
  constructor
  · exact (phaseOccupied_ordinary_iff ha).2 (Or.inl ⟨q, hq, rfl⟩)
  · exact (phaseOccupied_ordinary_iff ha).2 (Or.inr (Or.inl ⟨q, hq, hqa, rfl⟩))

/-- The right horizontal `UU` runs in an ordinary row. -/
theorem ordinary_right_run {k a q : Nat} (ha : a < k) (hq : q < k) (haq : a < q) :
    PhaseOccupied k (.ordinary a) (3 * q) ∧
      PhaseOccupied k (.ordinary a) (3 * q + 1) := by
  constructor
  · exact (phaseOccupied_ordinary_iff ha).2 (Or.inr (Or.inr ⟨q, hq, haq, rfl⟩))
  · exact (phaseOccupied_ordinary_iff ha).2 (Or.inl ⟨q, hq, rfl⟩)

/-- The left horizontal `UU` runs in a seam row stop before its pivot. -/
theorem seam_left_run {k a q : Nat} (ha : a < k) (hq : q < k) (hqa : q < a) :
    PhaseOccupied k (.seam a) (3 * q + 1) ∧
      PhaseOccupied k (.seam a) (3 * q + 2) := by
  constructor
  · exact (phaseOccupied_seam_iff ha).2 (Or.inl ⟨q, hq, rfl⟩)
  · exact (phaseOccupied_seam_iff ha).2 (Or.inr (Or.inl ⟨q, hq, hqa, rfl⟩))

/-- The right horizontal `UU` runs in a seam row start after its pivot. -/
theorem seam_right_run {k a q : Nat} (ha : a < k) (hq : q < k) (haq : a < q) :
    PhaseOccupied k (.seam a) (3 * q) ∧
      PhaseOccupied k (.seam a) (3 * q + 1) := by
  constructor
  · exact (phaseOccupied_seam_iff ha).2 (Or.inr (Or.inr ⟨q, hq, haq, rfl⟩))
  · exact (phaseOccupied_seam_iff ha).2 (Or.inl ⟨q, hq, rfl⟩)

/-- Two rows have a common occupied column. -/
def CommonPhaseColumn (k : Nat) (top bottom : PhaseRow) (c : Nat) : Prop :=
  PhaseOccupied k top c ∧ PhaseOccupied k bottom c

/-- Every pair of valid phase rows shares every backbone column. -/
theorem commonPhaseColumn_backbone {k q : Nat} {top bottom : PhaseRow}
    (hq : q < k) : CommonPhaseColumn k top bottom (3 * q + 1) := by
  constructor <;> exact phaseOccupied_backbone hq

/-- Common side columns for the transition `R_a / R_(a-1)`. -/
theorem common_ordinary_ordinary_pred {k a q : Nat} (ha : a < k) (ha0 : 0 < a)
    (hq : q < k) :
    (q < a → CommonPhaseColumn k (.ordinary a) (.ordinary (a - 1)) (3 * q + 2)) ∧
    (a < q → CommonPhaseColumn k (.ordinary a) (.ordinary (a - 1)) (3 * q)) := by
  constructor
  · intro hqa
    constructor
    · exact (phaseOccupied_ordinary_iff ha).2
        (Or.inr (Or.inl ⟨q, hq, by omega, rfl⟩))
    · exact (phaseOccupied_ordinary_iff (by omega : a - 1 < k)).2
        (Or.inr (Or.inl ⟨q, hq, by omega, rfl⟩))
  · intro haq
    constructor
    · exact (phaseOccupied_ordinary_iff ha).2
        (Or.inr (Or.inr ⟨q, hq, haq, rfl⟩))
    · exact (phaseOccupied_ordinary_iff (by omega : a - 1 < k)).2
        (Or.inr (Or.inr ⟨q, hq, by omega, rfl⟩))

/-- Common side columns for the transition `R_a / R_(a+1)`. -/
theorem common_ordinary_ordinary_succ {k a q : Nat} (ha : a + 1 < k) (hq : q < k) :
    (q ≤ a → CommonPhaseColumn k (.ordinary a) (.ordinary (a + 1)) (3 * q + 2)) ∧
    (a + 1 < q → CommonPhaseColumn k (.ordinary a) (.ordinary (a + 1)) (3 * q)) := by
  constructor
  · intro hqa
    constructor
    · exact (phaseOccupied_ordinary_iff (by omega : a < k)).2
        (Or.inr (Or.inl ⟨q, hq, hqa, rfl⟩))
    · exact (phaseOccupied_ordinary_iff ha).2
        (Or.inr (Or.inl ⟨q, hq, by omega, rfl⟩))
  · intro haq
    constructor
    · exact (phaseOccupied_ordinary_iff (by omega : a < k)).2
        (Or.inr (Or.inr ⟨q, hq, by omega, rfl⟩))
    · exact (phaseOccupied_ordinary_iff ha).2
        (Or.inr (Or.inr ⟨q, hq, haq, rfl⟩))

/-- `S_a` is columnwise contained in `R_a`. -/
theorem common_ordinary_seam_same {k a c : Nat} (ha : a < k)
    (hc : PhaseOccupied k (.seam a) c) :
    CommonPhaseColumn k (.ordinary a) (.seam a) c := by
  refine ⟨?_, hc⟩
  rw [phaseOccupied_seam_iff ha] at hc
  rw [phaseOccupied_ordinary_iff ha]
  rcases hc with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨h.choose, h.choose_spec.1, by omega, h.choose_spec.2.2⟩)
  · exact Or.inr (Or.inr h)

/-- `S_(a+1)` is columnwise contained in `R_a`. -/
theorem common_ordinary_seam_succ {k a c : Nat} (ha : a + 1 < k)
    (hc : PhaseOccupied k (.seam (a + 1)) c) :
    CommonPhaseColumn k (.ordinary a) (.seam (a + 1)) c := by
  refine ⟨?_, hc⟩
  rw [phaseOccupied_seam_iff ha] at hc
  rw [phaseOccupied_ordinary_iff (by omega : a < k)]
  rcases hc with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨h.choose, h.choose_spec.1, by omega, h.choose_spec.2.2⟩)
  · exact Or.inr (Or.inr ⟨h.choose, h.choose_spec.1, by omega, h.choose_spec.2.2⟩)

/-- `S_a` is columnwise contained in `R_(a-1)` when `a > 0`. -/
theorem common_seam_ordinary_pred {k a c : Nat} (ha : a < k) (ha0 : 0 < a)
    (hc : PhaseOccupied k (.seam a) c) :
    CommonPhaseColumn k (.seam a) (.ordinary (a - 1)) c := by
  refine ⟨hc, ?_⟩
  rw [phaseOccupied_seam_iff ha] at hc
  rw [phaseOccupied_ordinary_iff (by omega : a - 1 < k)]
  rcases hc with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨h.choose, h.choose_spec.1, by omega, h.choose_spec.2.2⟩)
  · exact Or.inr (Or.inr ⟨h.choose, h.choose_spec.1, by omega, h.choose_spec.2.2⟩)

/-- The reversed same-parameter transition `S_a / R_a`. -/
theorem common_seam_ordinary_same {k a c : Nat} (ha : a < k)
    (hc : PhaseOccupied k (.seam a) c) :
    CommonPhaseColumn k (.seam a) (.ordinary a) c := by
  have h := common_ordinary_seam_same ha hc
  exact ⟨h.2, h.1⟩

/-- A shared interior column in consecutive phase rows attaches the two dual
frontiers on either side of that column. -/
theorem consecutive_phase_common_column_dual_adj (k : Nat) (hk : 7 ≤ k)
    (i : Nat) (hi : i + 1 < (phaseRows k).length) (c : Nat)
    (hc0 : 0 < c) (hc : c < 3 * k - 1)
    (hcommon : CommonPhaseColumn k ((phaseRows k)[i]'(by omega))
      ((phaseRows k)[i + 1]'hi) c) :
    (uuDualGraph (uResidueZero k hk)).Adj
      (.cell ⟨i + 2, by rw [phaseRows_length k hk] at hi; omega⟩ ⟨c - 1, by omega⟩)
      (.cell ⟨i + 2, by rw [phaseRows_length k hk] at hi; omega⟩ ⟨c, hc⟩) := by
  have hir : i + 2 < 3 * k - 1 := by
    have hlen := phaseRows_length k hk
    omega
  rcases hcommon with ⟨⟨jt, hjt⟩, ⟨jb, hjb⟩⟩
  refine vertical_uu_dual_cells_adj (U := uResidueZero k hk)
    (r := i + 2) (c := c) hir hc0 hc ?_ ?_
  · simpa [hjt] using phase_vertex_mem_uResidueZero k hk
      ⟨i, by omega⟩ jt
  · simpa [hjb] using phase_vertex_mem_uResidueZero k hk
      ⟨i + 1, hi⟩ jb

end GridGraphs
