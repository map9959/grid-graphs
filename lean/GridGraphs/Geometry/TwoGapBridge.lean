import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lean.Elab.Tactic.Omega

/-! The contraction step in the two-gap frame exchange. The grid and
DRAT arguments establishing the hypotheses are separate. -/
namespace GridGraphs.TwoGapBridge

/-- Each component in the crop has one or two boundary teeth. Counting
edges in the contracted tree leaves exactly one two-tooth component. -/
theorem unique_bridge {α : Type*} [DecidableEq α] (s : Finset α)
    (deg : α → Nat) (h : ∀ x ∈ s, deg x = 1 ∨ deg x = 2)
    (edges : ∑ x ∈ s, deg x = s.card + 1) :
    (s.filter (fun x => deg x = 2)).card = 1 := by
  have count (u : Finset α) (hu : ∀ x ∈ u, deg x = 1 ∨ deg x = 2) :
      ∑ x ∈ u, deg x = u.card + (u.filter (fun x => deg x = 2)).card := by
    induction u using Finset.induction_on with
    | empty => simp
    | @insert a u ha ih =>
      have h' := ih (fun x hx => hu x (Finset.mem_insert_of_mem hx))
      have hn : a ∉ u.filter (fun x => deg x = 2) := fun hx => ha (Finset.mem_filter.mp hx).1
      rcases hu a (Finset.mem_insert_self a u) with h1 | h2
      · simp [Finset.sum_insert, ha, Finset.filter_insert, h1, h']
        omega
      · simp [Finset.sum_insert, ha, Finset.filter_insert, h2, h', hn]
        omega
  have := count s h
  omega

end GridGraphs.TwoGapBridge
