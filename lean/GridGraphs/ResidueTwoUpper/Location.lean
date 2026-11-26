import Mathlib

/-! Physical location types of the repeating residue-two overlap dual.
The local reductions below are for all widths, independent of any LP
feasibility assumption or symmetry of the given forest. -/

namespace GridGraphs.ResidueTwoUpper.Location

def axis (s d i : Nat) : Nat :=
  if i < d then i else if s ≤ i+d then 2*d+3+i-s else d+(i-d)%3

/-- Project a physical coordinate to an occurrence of its fine type at
the base side. Keep far coordinates against the far boundary. -/
def rep (s d i : Nat) : Nat :=
  if i < d then i else if s ≤ i+d then 2*d+8+i-s else d+(i-d)%3

local macro "locations" : tactic =>
  `(tactic| (simp only [axis,rep]; split_ifs <;> omega))

theorem rep_valid {d t i : Nat} (hi : i < 2*d+8+3*t) :
    rep (2*d+8+3*t) d i < 2*d+8 := by locations

theorem fine_matches {d t i : Nat} (hi : i < 2*d+8+3*t) :
    axis (2*d+8+3*t) d i = axis (2*d+8) d (rep (2*d+8+3*t) d i) := by locations

theorem reflected_fine_matches {d t i : Nat} (hi : i < 2*d+8+3*t) :
    axis (2*d+8+3*t) d (2*d+8+3*t-1-i) =
      axis (2*d+8) d (2*d+8-1-rep (2*d+8+3*t) d i) := by locations

/-- Same-board signed offsets −1,0,+1 (coded 0,1,2) give identical
coarse keys and identical boundary-incidence decisions at the base. -/
theorem neighbor_matches {d t i o : Nat} (hd : 5 ≤ d) (hi : i < 2*d+8+3*t)
    (ho : o ≤ 2) :
    let b := rep (2*d+8+3*t) d i
    (1 ≤ i+o ∧ i+o < 2*d+8+3*t+1 ↔ 1 ≤ b+o ∧ b+o < 2*d+8+1) ∧
    axis (2*d+8+3*t) 2 (i+o-1) = axis (2*d+8) 2 (b+o-1) := by
  dsimp only
  locations

/-- Patch origins covering a fixed physical star. -/
theorem cover_matches {t i a : Nat} (hi : i < 20+3*t) (ha : a ≤ 2) :
    let b := rep (20+3*t) 6 i
    (a ≤ i ∧ i-a < 18+3*t ↔ a ≤ b ∧ b-a < 18) ∧
    axis (18+3*t) 2 (i-a) = axis 18 2 (b-a) := by dsimp only; locations

/-- Star positions inside a fixed physical patch. -/
theorem inner_matches {t i a : Nat} (hi : i < 18+3*t) (ha : a ≤ 2) :
    axis (20+3*t) 2 (i+a) = axis 20 2 (rep (18+3*t) 5 i+a) := by locations

end GridGraphs.ResidueTwoUpper.Location
