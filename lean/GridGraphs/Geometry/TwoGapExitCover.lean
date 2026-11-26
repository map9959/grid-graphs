import Mathlib

namespace GridGraphs.TwoGapExitCover

/-- Retaining the first/last sixteen coordinates suffices for the depth
14 axis test, the depth-six stencil, and the boundary/root bits. -/
def tag (n x : Int) : Int × Int × Int :=
  (min x 16, min (n-1-x) 16, x % 3)

theorem flat (n d u : Int) (chart : n % 3 = 2) (hl : 60 ≤ d) (hr : 60 ≤ n-1-d)
    (phase : d % 3 = 2) (u₀ : -45 ≤ u) (u₁ : u ≤ 45) :
    tag n (d+u) = tag 329 (164+u) := by
  have h : d ≥ 62 := by omega
  -- On this progression both corner distances have residue 2. At the
  -- right endpoint we need the same two-site margin as at the left.
  have hh : n - 1 - d ≥ 62 := by omega
  unfold tag
  rw [min_eq_right (show 16 ≤ d+u by omega),
      min_eq_right (show 16 ≤ n-1-(d+u) by omega),
      min_eq_right (show 16 ≤ 164+u by omega),
      min_eq_right (show 16 ≤ 329-1-(164+u) by omega)]
  congr 2; omega

theorem left (t u : Int) (ht : t ≥ 0) (hu : u ≤ 151) :
    tag (329+42*t) u = tag 329 u := by
  unfold tag
  rw [min_eq_right (show 16 ≤ 329+42*t-1-u by omega),
      min_eq_right (show 16 ≤ 329-1-u by omega)]

theorem right (t u : Int) (ht : t ≥ 0) (hu : u ≤ 151) :
    tag (329+42*t) (328+42*t-u) = tag 329 (328-u) := by
  unfold tag
  rw [min_eq_right (show 16 ≤ 328+42*t-u by omega),
      min_eq_right (show 16 ≤ 328-u by omega)]
  rw [show 329+42*t-1-(328+42*t-u) = u by omega,
      show 329-1-(328-u) = u by omega,
      show (328+42*t-u) % 3 = (328-u) % 3 by omega]

/-- After exclusion of the two end ranges these and only these distances
remain arithmetically possible. This does not assert realizability. -/
theorem remaining (t d : Nat) :
    (d % 3 = 2 ∧ 104 < d ∧ d + 104 < 328 + 42*t) ↔
    ∃ j : Nat, j < 39 + 14*t ∧ d = 107 + 3*j := by
  constructor
  · intro h
    exact ⟨(d-107)/3, by omega, by omega⟩
  · rintro ⟨j,hj,rfl⟩
    omega

/-- The larger NW exit windows (including a two-site halo) use only
these coordinate tags; reflection is done on the physical board. -/
theorem left413 (t u : Int) (ht : 0 ≤ t) (hu : u ≤ 374) :
    tag (413+42*t) u = tag 413 u := by
  unfold tag
  rw [min_eq_right (show 16 ≤ 413+42*t-1-u by omega),
      min_eq_right (show 16 ≤ 413-1-u by omega)]

theorem remaining413 (t d : Nat) :
    (d % 3 = 2 ∧ 305 < d ∧ d + 305 < 412 + 42*t) ↔
    ∃ j : Nat, j < 14*t-67 ∧ d = 308 + 3*j := by
  constructor
  · intro h
    exact ⟨(d-308)/3, by omega, by omega⟩
  · rintro ⟨j,hj,rfl⟩
    omega

/-- The surviving projected endpoint at 182 can be pushed arbitrarily
far from *both* corners, without violating the end-range test. -/
theorem projected_split (j k : Nat) :
    let u := 3+j
    let v := 2+k
    let n := 413+42*(u+v)
    let d := 182+42*u
    d = 308+42*j ∧ n-1-d = 314+42*k := by
  dsimp
  omega

end GridGraphs.TwoGapExitCover
