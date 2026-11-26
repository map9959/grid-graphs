import Mathlib

namespace GridGraphs.NorthFanLines

/-- Marks in the right part of the fan, in tile (i,j) and subtile
coordinates (a,b). Before the collision the columns used below and
their neighbors lie strictly east of the left three transition tiles. -/
def mark (q i j a b : Int) : Prop :=
  (0 ≤ a ∧ a ≤ 2 ∧ 0 ≤ b ∧ b ≤ 2) ∧
  ((j=0 ∧ ((i≤q-2 ∧ a=1 ∧ 1≤b) ∨ (i=q-1 ∧ a=1 ∧ b=1) ∨
           (i=q ∧ a=0 ∧ b=2) ∨ (q < i ∧ a=0 ∧ 1≤b))) ∨
   (0 < j ∧ ((q-i-3*j≥2 ∧ a=1) ∨
     (q-i-3*j=1 ∧ a=1 ∧ b≤1) ∨
     (q-i-3*j=0 ∧ ((a=0 ∧ b=2) ∨ (a=1 ∧ b=0))) ∨
     (q-i-3*j= -1 ∧ a=0 ∧ 1≤b) ∨
     (q-i-3*j≤ -2 ∧ a=0))))

theorem straight (q u j b : Int) (hu : u ≤ q) (hj : 0 ≤ j)
    (hb : 0 ≤ b ∧ b ≤ 2) :
    mark q u j 0 b ↔ q-u+2 ≤ 3*j+b := by unfold mark; omega

/-- The physical forced stars of this line cannot touch any other
mark's star: stars meet only at Manhattan distance at most two. -/
theorem isolated (q u i j a b z : Int) (hu : u≤q)
    (born : q-u+2 ≤ z) (marked : mark q i j a b)
    (near : |3*i+a-3*u| + |3*j+b-z| ≤ 2) :
    3*i+a=3*u ∧ q-u+2 ≤ 3*j+b := by
  unfold mark at marked
  rcases le_total 0 (3*i+a-3*u) with hx|hx <;>
    rcases le_total 0 (3*j+b-z) with hy|hy <;>
    simp only [abs_of_nonneg, abs_of_nonpos, hx, hy] at near <;> omega

end GridGraphs.NorthFanLines
