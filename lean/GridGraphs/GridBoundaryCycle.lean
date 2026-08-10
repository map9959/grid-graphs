import GridGraphs.LinearWaste

/-!
# The boundary cycle of a rectangular grid

This module numbers the boundary vertices clockwise, beginning at the
top-left corner.  The four corners occur exactly once.
-/

namespace GridGraphs

/-- Number of vertices on the boundary of an `m x n` grid.  The intended API
uses this with `m, n >= 2`. -/
def gridBoundaryLength (m n : Nat) : Nat := 2 * m + 2 * n - 4

/-- A position in the clockwise boundary numbering. -/
abbrev GridBoundaryPosition (m n : Nat) := Fin (gridBoundaryLength m n)

@[simp] theorem gridBoundaryLength_pos {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n) :
    0 < gridBoundaryLength m n := by
  unfold gridBoundaryLength
  omega

/-- The clockwise boundary vertex at a given position.  Numbering starts at
`(0, 0)`, travels along the top side, and then around the rectangle. -/
def gridBoundaryVertex {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i : GridBoundaryPosition m n) : GridVertex m n :=
  if htop : i.val < n then
    (⟨0, by omega⟩, ⟨i.val, htop⟩)
  else if hright : i.val < n + m - 1 then
    (⟨i.val - n + 1, by omega⟩, ⟨n - 1, by omega⟩)
  else if hbottom : i.val < m + 2 * n - 2 then
    (⟨m - 1, by omega⟩, ⟨m + 2 * n - 3 - i.val, by omega⟩)
  else
    (⟨gridBoundaryLength m n - i.val, by
      unfold gridBoundaryLength at *
      omega⟩, ⟨0, by omega⟩)

/-- The numerical inverse of `gridBoundaryVertex`. -/
def gridBoundaryIndex {m n : Nat} (v : GridVertex m n) : Nat :=
  if v.1.val = 0 then v.2.val
  else if v.2.val + 1 = n then n + v.1.val - 1
  else if v.1.val + 1 = m then m + 2 * n - 3 - v.2.val
  else gridBoundaryLength m n - v.1.val

@[simp] theorem gridBoundaryIndex_vertex {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i : GridBoundaryPosition m n) :
    gridBoundaryIndex (gridBoundaryVertex hm hn i) = i.val := by
  unfold gridBoundaryIndex gridBoundaryVertex gridBoundaryLength
  split_ifs <;> simp_all <;> omega

/-- Distinct boundary positions name distinct vertices. -/
theorem gridBoundaryVertex_injective {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n) :
    Function.Injective (gridBoundaryVertex hm hn) := by
  intro i j hij
  apply Fin.ext
  rw [← gridBoundaryIndex_vertex hm hn i,
    ← gridBoundaryIndex_vertex hm hn j, hij]

/-- Every numbered perimeter vertex lies on the grid boundary. -/
theorem gridBoundaryVertex_isBoundary {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i : GridBoundaryPosition m n) :
    IsGridBoundary (gridBoundaryVertex hm hn i) := by
  unfold gridBoundaryVertex IsGridBoundary
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr (Or.inr (Or.inr (by simp; omega)))
    · split
      · exact Or.inr (Or.inl (by simp; omega))
      · exact Or.inr (Or.inr (Or.inl rfl))

/-- Every boundary vertex occurs in the clockwise numbering. -/
theorem exists_gridBoundaryPosition {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (v : GridVertex m n) (hv : IsGridBoundary v) :
    ∃ i : GridBoundaryPosition m n, gridBoundaryVertex hm hn i = v := by
  unfold IsGridBoundary at hv
  by_cases htop : v.1.val = 0
  · refine ⟨⟨v.2.val, ?_⟩, ?_⟩
    · unfold gridBoundaryLength
      omega
    · unfold gridBoundaryVertex
      rw [dif_pos (by simpa using v.2.isLt)]
      apply Prod.ext <;> apply Fin.ext <;> simp_all
  by_cases hright : v.2.val + 1 = n
  · refine ⟨⟨n + v.1.val - 1, ?_⟩, ?_⟩
    · unfold gridBoundaryLength
      omega
    · unfold gridBoundaryVertex
      rw [dif_neg (by simp; omega), dif_pos (by simp; omega)]
      apply Prod.ext <;> apply Fin.ext <;> simp_all <;> omega
  by_cases hbottom : v.1.val + 1 = m
  · refine ⟨⟨m + 2 * n - 3 - v.2.val, ?_⟩, ?_⟩
    · unfold gridBoundaryLength
      omega
    · unfold gridBoundaryVertex
      rw [dif_neg (by simp; omega), dif_neg (by simp; omega),
        dif_pos (by simp; omega)]
      apply Prod.ext <;> apply Fin.ext <;> simp_all <;> omega
  · have hleft : v.2.val = 0 := by
      rcases hv with h | h | h | h
      · exact absurd h htop
      · exact absurd h hbottom
      · exact h
      · exact absurd h hright
    refine ⟨⟨gridBoundaryLength m n - v.1.val, ?_⟩, ?_⟩
    · unfold gridBoundaryLength
      omega
    · unfold gridBoundaryVertex
      rw [dif_neg (by simp [gridBoundaryLength]; omega),
        dif_neg (by simp [gridBoundaryLength]; omega),
        dif_neg (by simp [gridBoundaryLength]; omega)]
      apply Prod.ext <;> apply Fin.ext <;> simp_all [gridBoundaryLength] <;> omega

/-- The range of the clockwise map is exactly the rectangular boundary. -/
theorem mem_range_gridBoundaryVertex_iff {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (v : GridVertex m n) :
    v ∈ Set.range (gridBoundaryVertex hm hn) ↔ IsGridBoundary v := by
  constructor
  · rintro ⟨i, rfl⟩
    exact gridBoundaryVertex_isBoundary hm hn i
  · exact exists_gridBoundaryPosition hm hn v

/-- Boundary positions are equivalent to boundary vertices. -/
noncomputable def gridBoundaryEquiv {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n) :
    GridBoundaryPosition m n ≃ {v : GridVertex m n // IsGridBoundary v} :=
  Equiv.ofBijective
    (fun i => ⟨gridBoundaryVertex hm hn i,
      gridBoundaryVertex_isBoundary hm hn i⟩)
    ⟨fun _ _ h => gridBoundaryVertex_injective hm hn (congrArg Subtype.val h),
      by
        rintro ⟨v, hv⟩
        obtain ⟨i, rfl⟩ := exists_gridBoundaryPosition hm hn v hv
        exact ⟨i, rfl⟩⟩

private theorem gridBoundaryVertex_top {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i : GridBoundaryPosition m n) (hi : i.val < n) :
    gridBoundaryVertex hm hn i = (⟨0, by omega⟩, ⟨i.val, hi⟩) := by
  simp [gridBoundaryVertex, hi]

private theorem gridBoundaryVertex_right {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i : GridBoundaryPosition m n) (htop : ¬i.val < n)
    (hi : i.val < n + m - 1) :
    gridBoundaryVertex hm hn i =
      (⟨i.val - n + 1, by omega⟩, ⟨n - 1, by omega⟩) := by
  simp [gridBoundaryVertex, htop, hi]

private theorem gridBoundaryVertex_bottom {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i : GridBoundaryPosition m n) (hright : ¬i.val < n + m - 1)
    (hi : i.val < m + 2 * n - 2) :
    gridBoundaryVertex hm hn i =
      (⟨m - 1, by omega⟩, ⟨m + 2 * n - 3 - i.val, by omega⟩) := by
  have htop : ¬i.val < n := by omega
  simp [gridBoundaryVertex, htop, hright, hi]

private theorem gridBoundaryVertex_left {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i : GridBoundaryPosition m n) (hi : ¬i.val < m + 2 * n - 2) :
    gridBoundaryVertex hm hn i =
      (⟨gridBoundaryLength m n - i.val, by
        unfold gridBoundaryLength at *
        omega⟩, ⟨0, by omega⟩) := by
  have htop : ¬i.val < n := by omega
  have hright : ¬i.val < n + m - 1 := by omega
  simp [gridBoundaryVertex, htop, hright, hi]

/-- The next position in the clockwise boundary numbering. -/
def gridBoundarySucc {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i : GridBoundaryPosition m n) : GridBoundaryPosition m n :=
  ⟨(i.val + 1) % gridBoundaryLength m n,
    Nat.mod_lt _ (gridBoundaryLength_pos hm hn)⟩

/-- Consecutive clockwise positions are adjacent, including the wrap from the
last position back to the top-left corner. -/
theorem gridBoundaryVertex_succ_adj {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (i : GridBoundaryPosition m n) :
    (gridGraph m n).Adj (gridBoundaryVertex hm hn i)
      (gridBoundaryVertex hm hn (gridBoundarySucc hm hn i)) := by
  by_cases hi : i.val + 1 < gridBoundaryLength m n
  · let j := gridBoundarySucc hm hn i
    have hval : j.val = i.val + 1 := by
      dsimp [j, gridBoundarySucc]
      exact Nat.mod_eq_of_lt hi
    change (gridGraph m n).Adj (gridBoundaryVertex hm hn i)
      (gridBoundaryVertex hm hn j)
    by_cases htop : i.val < n
    · by_cases hnext : i.val + 1 < n
      · rw [gridBoundaryVertex_top hm hn i htop,
          gridBoundaryVertex_top hm hn j (by rw [hval]; exact hnext)]
        exact Or.inl ⟨rfl, Or.inl (by simp; omega)⟩
      · rw [gridBoundaryVertex_top hm hn i htop,
          gridBoundaryVertex_right hm hn j (by rw [hval]; exact hnext)
            (by rw [hval]; omega)]
        exact Or.inr ⟨by apply Fin.ext; simp; omega, Or.inl (by simp; omega)⟩
    · by_cases hright : i.val < n + m - 1
      · by_cases hnext : i.val + 1 < n + m - 1
        · rw [gridBoundaryVertex_right hm hn i htop hright,
            gridBoundaryVertex_right hm hn j (by rw [hval]; omega)
              (by rw [hval]; exact hnext)]
          exact Or.inr ⟨rfl, Or.inl (by simp; omega)⟩
        · rw [gridBoundaryVertex_right hm hn i htop hright,
            gridBoundaryVertex_bottom hm hn j (by rw [hval]; exact hnext)
              (by rw [hval]; omega)]
          exact Or.inl ⟨by apply Fin.ext; simp; omega, Or.inr (by simp; omega)⟩
      · by_cases hbottom : i.val < m + 2 * n - 2
        · by_cases hnext : i.val + 1 < m + 2 * n - 2
          · rw [gridBoundaryVertex_bottom hm hn i hright hbottom,
              gridBoundaryVertex_bottom hm hn j (by rw [hval]; omega)
                (by rw [hval]; exact hnext)]
            exact Or.inl ⟨rfl, Or.inr (by simp; omega)⟩
          · rw [gridBoundaryVertex_bottom hm hn i hright hbottom,
              gridBoundaryVertex_left hm hn j (by rw [hval]; exact hnext)]
            exact Or.inr ⟨by
                apply Fin.ext
                change m + 2 * n - 3 - i.val = 0
                omega,
              Or.inr (by
                change gridBoundaryLength m n - j.val + 1 = m - 1
                unfold gridBoundaryLength
                omega)⟩
        · rw [gridBoundaryVertex_left hm hn i hbottom,
            gridBoundaryVertex_left hm hn j (by rw [hval]; omega)]
          exact Or.inr ⟨by apply Fin.ext; rfl, Or.inr (by simp; omega)⟩
  · have hilast : i.val + 1 = gridBoundaryLength m n := by omega
    let j := gridBoundarySucc hm hn i
    have hval : j.val = 0 := by
      dsimp [j, gridBoundarySucc]
      rw [hilast, Nat.mod_self]
    change (gridGraph m n).Adj (gridBoundaryVertex hm hn i)
      (gridBoundaryVertex hm hn j)
    have hiV : gridBoundaryVertex hm hn i =
        (⟨1, by omega⟩, ⟨0, by omega⟩) := by
      have hshape : gridBoundaryLength m n =
          (m + 2 * n - 2) + (m - 2) := by
        unfold gridBoundaryLength
        omega
      have hilast' : i.val + 1 = (m + 2 * n - 2) + (m - 2) :=
        hilast.trans hshape
      unfold gridBoundaryVertex
      split_ifs <;> apply Prod.ext <;> apply Fin.ext <;>
        simp_all [gridBoundaryLength] <;> omega
    have hzV : gridBoundaryVertex hm hn j =
        (⟨0, by omega⟩, ⟨0, by omega⟩) := by
      rw [gridBoundaryVertex_top hm hn _ (by rw [hval]; omega)]
      apply Prod.ext <;> apply Fin.ext <;> simp [hval]
    rw [hiV, hzV]
    exact Or.inr ⟨rfl, Or.inr rfl⟩

/-! Small helpers for placing endpoints in cyclic order. -/

/-- Move forward by `d` positions in a nonempty finite cycle. -/
def cyclicOffset {k : Nat} (hk : 0 < k) (i : Fin k) (d : Nat) : Fin k :=
  ⟨(i.val + d) % k, Nat.mod_lt _ hk⟩

/-- Four distinct cyclic positions encountered in the displayed order after
starting at `a`. -/
def CyclicOrder4 {k : Nat} (hk : 0 < k) (a b c d : Fin k) : Prop :=
  ∃ p q r : Nat, 0 < p ∧ 0 < q ∧ 0 < r ∧ p + q + r < k ∧
    b = cyclicOffset hk a p ∧
    c = cyclicOffset hk a (p + q) ∧
    d = cyclicOffset hk a (p + q + r)

/-- The pairs `(a, b)` and `(c, d)` alternate around a finite cycle. -/
def CyclicallyAlternating {k : Nat} (hk : 0 < k) (a b c d : Fin k) : Prop :=
  CyclicOrder4 hk a c b d ∨ CyclicOrder4 hk a d b c

end GridGraphs
