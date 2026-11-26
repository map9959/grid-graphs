import Mathlib

namespace GridGraphs.OrderedSeamTariff

/-- Maximum additional charge from disjoint adjacent pairs among the
first n rows. No assumption on the number of events in the word. -/
def bill (extra : Nat → Nat) : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n+2 => max (bill extra (n+1)) (bill extra n + extra n)

theorem disjoint_charge (extra slack : Nat → Nat)
    (edge : ∀ j, extra j ≤ slack j + slack (j+1)) (n : Nat) :
    bill extra n ≤ ∑ j ∈ Finset.range n, slack j := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _|(_|m)
    · simp [bill]
    · simp [bill]
    · have a := ih (m+1) (by omega)
      have b := ih m (by omega)
      have c := edge m
      rw [bill, max_le_iff, Finset.sum_range_succ]
      constructor
      · omega
      · rw [Finset.sum_range_succ]
        omega

theorem packet_tariff (skip extra slack : Nat → Nat)
    (edge : ∀ j, extra j ≤ slack j + slack (j+1)) (n : Nat) :
    (∑ j ∈ Finset.range n, skip j) + bill extra n ≤
      ∑ j ∈ Finset.range n, (skip j + slack j) := by
  rw [Finset.sum_add_distrib]
  exact Nat.add_le_add_left (disjoint_charge extra slack edge n) _

theorem overlap_sum (r : Nat → Nat) (n : Nat) :
    (∑ j ∈ Finset.range n, (r j + r (j+1))) + r 0 =
      2*(∑ j ∈ Finset.range n, r j) + r n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    omega

/-- With the two outer rows charged once more, each row pays twice. -/
theorem cross_tariff (price r : Nat → Nat) (n : Nat)
    (bands : (∑ j ∈ Finset.range n, price j) ≤
      (∑ j ∈ Finset.range n, (r j+r (j+1))) + r 0 + r n) :
    (∑ j ∈ Finset.range n, price j) ≤ 2*(∑ j ∈ Finset.range (n+1), r j) := by
  rw [overlap_sum] at bands
  rw [Finset.sum_range_succ]
  omega

end GridGraphs.OrderedSeamTariff
