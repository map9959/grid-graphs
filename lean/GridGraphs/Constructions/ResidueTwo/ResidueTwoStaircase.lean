import GridGraphs.Constructions.BoundaryFive.BoundaryFiveConstruction

/-! # The improved residue-two staircase

Actual ambient centers from Section 8 of `analysis/BOUNDARY_FIVE_PEELING.md`.
Only placement, center disjointness and counting are proved here, not forest
or attachment properties, and no optimality assertion is made.
-/

namespace GridGraphs.ResidueTwoStaircase

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

abbrev Vertex (s : ℕ) := GridVertex (3 * s + 5) (3 * s + 5)

/-- A closed horizontal interval, in ambient zero-based coordinates. -/
def interval (s r a b : ℕ) : Finset (Vertex s) :=
  univ.filter fun v => v.1.val = r ∧ a ≤ v.2.val ∧ v.2.val ≤ b

@[simp] theorem mem_interval {s r a b : ℕ} {v : Vertex s} :
    v ∈ interval s r a b ↔ v.1.val = r ∧ a ≤ v.2.val ∧ v.2.val ≤ b := by
  simp [interval]

theorem interval_card {s r a b : ℕ} (hr : r < 3 * s + 5)
    (hb : b < 3 * s + 5) : (interval s r a b).card = b + 1 - a := by
  rw [← Nat.card_Icc]
  apply card_bij (fun v _ => v.2.val)
  · intro v hv
    exact mem_Icc.mpr (mem_interval.mp hv).2
  · intro v hv w hw he
    apply Prod.ext
    · apply Fin.ext
      exact (mem_interval.mp hv).1.trans (mem_interval.mp hw).1.symm
    · exact Fin.ext he
  · intro c hc
    have hc' := mem_Icc.mp hc
    exact ⟨(⟨r, hr⟩, ⟨c, by omega⟩), mem_interval.mpr ⟨rfl, hc'⟩, rfl⟩

def z (s : ℕ) : Vertex s := (⟨2, by omega⟩, ⟨2, by omega⟩)

def R (s : ℕ) (j : Fin s) : Finset (Vertex s) :=
  interval s (3 * j.val + 3) (j.val + 4) (3 * s + 2)

def L (s : ℕ) (j : Fin (s - 1)) : Finset (Vertex s) :=
  interval s (3 * j.val + 5) 2 (j.val + 3)

/-- Singleton bottom-boundary pieces. -/
def B (s : ℕ) (t : Fin ((s + 3) / 4)) : Finset (Vertex s) :=
  interval s (3 * s + 2) (s + 2 - 4 * t.val) (s + 2 - 4 * t.val)

/-- Singleton penultimate-row pieces, later glued to the last left interval. -/
def P (s : ℕ) (t : Fin ((s + 1) / 4)) : Finset (Vertex s) :=
  interval s (3 * s + 1) (s - 4 * t.val) (s - 4 * t.val)

abbrev Index (s : ℕ) :=
  Unit ⊕ Fin s ⊕ Fin (s - 1) ⊕ Fin ((s + 3) / 4) ⊕ Fin ((s + 1) / 4)

def piece (s : ℕ) : Index s → Finset (Vertex s)
  | .inl _ => {z s}
  | .inr (.inl j) => R s j
  | .inr (.inr (.inl j)) => L s j
  | .inr (.inr (.inr (.inl t))) => B s t
  | .inr (.inr (.inr (.inr t))) => P s t

def A (s : ℕ) : Finset (Vertex s) := univ.biUnion (piece s)

@[simp] theorem mem_A {s : ℕ} {v : Vertex s} :
    v ∈ A s ↔ v = z s ∨ (∃ j, v ∈ R s j) ∨ (∃ j, v ∈ L s j) ∨
      (∃ t, v ∈ B s t) ∨ (∃ t, v ∈ P s t) := by
  simp [A, Index, piece]

theorem R_card {s : ℕ} (j : Fin s) : (R s j).card = 3 * s - j.val - 1 := by
  rw [R, interval_card (by have := j.isLt; omega) (by omega)]
  omega

theorem L_card {s : ℕ} (j : Fin (s - 1)) : (L s j).card = j.val + 2 := by
  rw [L, interval_card (by have := j.isLt; omega) (by have := j.isLt; omega)]
  omega

theorem B_card {s : ℕ} (t : Fin ((s + 3) / 4)) : (B s t).card = 1 := by
  rw [B, interval_card (by omega) (by omega)]
  omega

theorem P_card {s : ℕ} (t : Fin ((s + 1) / 4)) : (P s t).card = 1 := by
  rw [P, interval_card (by omega) (by omega)]
  omega

/-- Distinct indexed pieces have disjoint centers (not necessarily disjoint supports). -/
theorem piece_disjoint {s : ℕ} (hs : 2 ≤ s) :
    Pairwise (fun i k => Disjoint (piece s i) (piece s k)) := by
  intro i k hik
  apply disjoint_left.mpr
  intro v hi hk
  rcases i with u | j | j | t | t <;>
    rcases k with w | l | l | q | q <;>
    simp only [piece, R, L, B, P, mem_interval, mem_singleton,
      Prod.ext_iff, Fin.ext_iff, z] at hi hk
  all_goals simp only [ne_eq, Sum.inl.injEq, Sum.inr.injEq, Fin.ext_iff] at hik
  all_goals first | exact hik trivial | omega

theorem piece_subset_Deep {s : ℕ} (hs : 2 ≤ s) (i : Index s) :
    (↑(piece s i) : Set (Vertex s)) ⊆ BoundaryFiveConstruction.Deep (3 * s + 5) := by
  intro v hv
  rcases i with u | j | j | t | t <;>
    simp only [piece, R, L, B, P, mem_coe, mem_interval, mem_singleton,
      Prod.ext_iff, Fin.ext_iff, z] at hv <;>
    dsimp [BoundaryFiveConstruction.Deep] <;> omega

theorem A_subset_Deep {s : ℕ} (hs : 2 ≤ s) :
    (↑(A s) : Set (Vertex s)) ⊆ BoundaryFiveConstruction.Deep (3 * s + 5) := by
  intro v hv
  obtain ⟨i, _, hi⟩ := mem_biUnion.mp hv
  exact piece_subset_Deep hs i hi

/-- Subtraction-free count of all right intervals. -/
theorem R_sum_card (s : ℕ) :
    2 * (∑ j : Fin s, (R s j).card) + s = 5 * s ^ 2 := by
  have he : (∑ j : Fin s, ((R s j).card + j.val + 1)) = 3 * s * s := by
    calc
      _ = ∑ _j : Fin s, 3 * s := by
        apply sum_congr rfl
        intro j _
        rw [R_card]
        have := j.isLt
        omega
      _ = _ := by simp; ring
  simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, smul_eq_mul,
    mul_one] at he
  have hj := sum_range_id_mul_two s
  rw [← Fin.sum_univ_eq_sum_range] at hj
  have hsub : s * (s - 1) + s = s ^ 2 := by
    cases s with
    | zero => simp
    | succ s => simp; ring
  nlinarith

/-- Subtraction-free count of all left intervals. -/
theorem L_sum_card {s : ℕ} (hs : 2 ≤ s) :
    2 * (∑ j : Fin (s - 1), (L s j).card) + 2 = s ^ 2 + s := by
  simp only [L_card, sum_add_distrib, sum_const, card_univ, Fintype.card_fin,
    smul_eq_mul]
  have hj := sum_range_id_mul_two (s - 1)
  rw [← Fin.sum_univ_eq_sum_range] at hj
  have h1 : s - 1 + 1 = s := by omega
  have h2 : s - 1 - 1 + 2 = s := by omega
  nlinarith

theorem baseline_card {s : ℕ} (hs : 2 ≤ s) :
    1 + (∑ j : Fin s, (R s j).card) +
      (∑ j : Fin (s - 1), (L s j).card) = 3 * s ^ 2 := by
  have hr := R_sum_card s
  have hl := L_sum_card hs
  omega

theorem B_sum_card (s : ℕ) :
    (∑ t : Fin ((s + 3) / 4), (B s t).card) = (s + 3) / 4 := by
  simp [B_card]

theorem P_sum_card (s : ℕ) :
    (∑ t : Fin ((s + 1) / 4), (P s t).card) = (s + 1) / 4 := by
  simp [P_card]

theorem added_count (s : ℕ) : (s + 3) / 4 + (s + 1) / 4 = (s + 1) / 2 := by
  omega

/-- Exact cardinality of the improved family, not an optimality statement. -/
theorem A_card {s : ℕ} (hs : 2 ≤ s) :
    (A s).card = 3 * s ^ 2 + (s + 1) / 2 := by
  have hc : (A s).card = 1 + (∑ j : Fin s, (R s j).card) +
      (∑ j : Fin (s - 1), (L s j).card) + (s + 3) / 4 + (s + 1) / 4 := by
    rw [A, card_biUnion (fun i _ k _ hik => piece_disjoint hs hik)]
    simp [Index, Fintype.sum_sum_type, piece, B_card, P_card]
    omega
  have hr := R_sum_card s
  have hl := L_sum_card hs
  have ha := added_count s
  omega

end

end GridGraphs.ResidueTwoStaircase
