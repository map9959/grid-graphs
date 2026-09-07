import Mathlib

/-!
# Rod-labelled missing triples

The deficit is the cardinality of the actual complement of each occupied
coordinate set. Blocks assigned to different recipients are never identified.
Blocks assigned to one recipient are disjoint by three-spacing of the
opposite axes. The tie-break assigns a pair to its horizontal recipient
whenever that recipient misses the block, and to the vertical one otherwise.
No independent per-pair deficit inequality is assumed.
-/

namespace GridGraphs.BoundaryFive.Rootless

open Finset

def ThreeSpaced {ι : Type*} (S : Finset ι) (axis : ι → Nat) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, i ≠ j → axis i + 3 ≤ axis j ∨ axis j + 3 ≤ axis i

/-- Exact count of disjoint physical triples inside one recipient's holes. -/
theorem missing_triples_local {ι : Type*} [DecidableEq ι]
    (m : Nat) (S : Finset ι) (axis : ι → Nat) (occupied : Finset Nat)
    (hocc : occupied ⊆ range m) (hspace : ThreeSpaced S axis)
    (haxis : ∀ i ∈ S, 1 ≤ axis i ∧ axis i + 1 < m)
    (hmiss : ∀ i ∈ S, Disjoint (Icc (axis i - 1) (axis i + 1)) occupied) :
    3 * S.card ≤ m - occupied.card := by
  have hdisj : (↑S : Set ι).Pairwise (fun i j =>
      Disjoint (Icc (axis i - 1) (axis i + 1)) (Icc (axis j - 1) (axis j + 1))) := by
    intro i hi j hj hne
    apply disjoint_left.mpr
    intro x hx hy
    have h := hspace i hi j hj hne
    have hx' := mem_Icc.mp hx
    have hy' := mem_Icc.mp hy
    omega
  have hsub : S.biUnion (fun i => Icc (axis i - 1) (axis i + 1)) ⊆
      range m \ occupied := by
    intro x hx
    obtain ⟨i, hi, hx⟩ := mem_biUnion.mp hx
    have ha := haxis i hi
    have hx' := mem_Icc.mp hx
    exact mem_sdiff.mpr ⟨mem_range.mpr (by omega),
      fun ho => disjoint_left.mp (hmiss i hi) hx ho⟩
  have hc : (S.biUnion (fun i => Icc (axis i - 1) (axis i + 1))).card = 3 * S.card := by
    rw [card_biUnion hdisj]
    calc
      _ = ∑ _i ∈ S, 3 := sum_congr rfl (fun i hi => by
        have ha := haxis i hi
        rw [Nat.card_Icc]
        omega)
      _ = _ := by simp [Nat.mul_comm]
  have h := card_le_card hsub
  rw [hc, card_sdiff_of_subset hocc, card_range] at h
  exact h

/-- Charge each perpendicular pair once, to a recipient missing the entire
three-position block. The two sums count rod-labelled slots, not their union
in the ambient square. Occupied sets need not themselves be intervals. -/
theorem missing_triples_bound {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (m : Nat) (H : Finset ι) (V : Finset κ)
    (row : ι → Nat) (col : κ → Nat)
    (horizontal : ι → Finset Nat) (vertical : κ → Finset Nat)
    (hH : ∀ i ∈ H, horizontal i ⊆ range m)
    (hV : ∀ j ∈ V, vertical j ⊆ range m)
    (hsH : ThreeSpaced H row) (hsV : ThreeSpaced V col)
    (haH : ∀ i ∈ H, 1 ≤ row i ∧ row i + 1 < m)
    (haV : ∀ j ∈ V, 1 ≤ col j ∧ col j + 1 < m)
    (hpair : ∀ i ∈ H, ∀ j ∈ V,
      Disjoint (Icc (col j - 1) (col j + 1)) (horizontal i) ∨
      Disjoint (Icc (row i - 1) (row i + 1)) (vertical j)) :
    3 * H.card * V.card ≤
      H.sum (fun i => m - (horizontal i).card) + V.sum (fun j => m - (vertical j).card) := by
  classical
  let P := fun i j => Disjoint (Icc (col j - 1) (col j + 1)) (horizontal i)
  let A := fun i => V.filter (P i)
  let B := fun j => H.filter (fun i => ¬ P i j)
  have hh (i : ι) (hi : i ∈ H) : 3 * (A i).card ≤ m - (horizontal i).card := by
    apply missing_triples_local m (A i) col (horizontal i) (hH i hi)
    · intro j hj l hl hne
      exact hsV j (mem_filter.mp hj).1 l (mem_filter.mp hl).1 hne
    · intro j hj
      exact haV j (mem_filter.mp hj).1
    · intro j hj
      exact (mem_filter.mp hj).2
  have hv (j : κ) (hj : j ∈ V) : 3 * (B j).card ≤ m - (vertical j).card := by
    apply missing_triples_local m (B j) row (vertical j) (hV j hj)
    · intro i hi l hl hne
      exact hsH i (mem_filter.mp hi).1 l (mem_filter.mp hl).1 hne
    · intro i hi
      exact haH i (mem_filter.mp hi).1
    · intro i hi
      exact (hpair i (mem_filter.mp hi).1 j hj).resolve_left (mem_filter.mp hi).2
  have hcount : (∑ i ∈ H, (A i).card) + (∑ j ∈ V, (B j).card) = H.card * V.card := by
    simp only [A, B, card_filter]
    rw [sum_comm (s := V), ← sum_add_distrib]
    calc
      _ = ∑ _i ∈ H, ∑ _j ∈ V, 1 := by
        apply sum_congr rfl
        intro i _
        rw [← sum_add_distrib]
        apply sum_congr rfl
        intro j _
        by_cases h : P i j <;> simp [h]
      _ = _ := by simp
  have hh' := sum_le_sum hh
  have hv' := sum_le_sum hv
  rw [← mul_sum] at hh' hv'
  nlinarith

end GridGraphs.BoundaryFive.Rootless
