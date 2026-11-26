import Mathlib

namespace GridGraphs.BulkAxis

/-- A finite interval of a track inherits every forward-closed mask test. -/
theorem forward {α : Type*} (w : Nat → α) (bound : Nat) (P : α → Prop)
    (step : ∀ i < bound, P (w i) → P (w (i+1))) {a b : Nat}
    (hab : a ≤ b) (hb : b ≤ bound) (ha : P (w a)) : P (w b) := by
  induction b, hab using Nat.le_induction with
  | base => exact ha
  | succ b h ih => exact step b (by omega) (ih (by omega))

/-- The backward track test is independent of the forward test. -/
theorem backward {α : Type*} (w : Nat → α) (bound : Nat) (P : α → Prop)
    (step : ∀ i < bound, P (w (i+1)) → P (w i)) {a b : Nat}
    (hab : a ≤ b) (hb : b ≤ bound) (h : P (w b)) : P (w a) := by
  induction b, hab using Nat.le_induction with
  | base => exact h
  | succ b _ ih => exact ih (by omega) (step b (by omega) h)

theorem along {α : Type*} (w : Nat → α) (bound : Nat) (F B : α → Prop)
    (fwd : ∀ i < bound, F (w i) → F (w (i+1)))
    (bwd : ∀ i < bound, B (w (i+1)) → B (w i)) {a b : Nat}
    (ha : a ≤ bound) (hb : b ≤ bound) (sf : F (w a)) (sb : B (w a)) :
    F (w b) ∨ B (w b) := by
  rcases le_total a b with h|h
  · exact Or.inl (forward w bound F fwd h hb sf)
  · exact Or.inr (backward w bound B bwd h ha sb)

/-- The geometric gluing step: the tile at the crossing would belong to
two disjoint mask families. Rows and columns may have different lengths. -/
theorem no_cross {α : Type*} (tile : Nat → Nat → α) (height width : Nat)
    (vertical horizontal row col : α → Prop)
    (rows : ∀ i ≤ height, ∀ a ≤ width, vertical (tile i a) →
            ∀ j ≤ width, row (tile i j))
    (cols : ∀ j ≤ width, ∀ b ≤ height, horizontal (tile b j) →
            ∀ i ≤ height, col (tile i j))
    (disjoint : ∀ m, row m → col m → False)
    {i a b j : Nat} (hi : i ≤ height) (ha : a ≤ width)
    (hb : b ≤ height) (hj : j ≤ width) (hv : vertical (tile i a)) :
    ¬horizontal (tile b j) := fun hh =>
  disjoint _ (rows i hi a ha hv j hj) (cols j hj b hb hh i hi)

end GridGraphs.BulkAxis
