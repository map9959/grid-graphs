import GridGraphs.Accounting.BoundaryFiveBudget

namespace GridGraphs.BoundarySix

open Finset SimpleGraph

def Corner {n : Nat} (v : GridVertex n n) : Prop :=
  (v.1.val = 0 ∨ v.1.val + 1 = n) ∧ (v.2.val = 0 ∨ v.2.val + 1 = n)

def Near {n : Nat} (v : GridVertex n n) : Prop :=
  ((v.1.val = 0 ∨ v.1.val + 1 = n) ∧ (v.2.val = 1 ∨ v.2.val + 2 = n)) ∨
  ((v.2.val = 0 ∨ v.2.val + 1 = n) ∧ (v.1.val = 1 ∨ v.1.val + 2 = n))

def Second {n : Nat} (v : GridVertex n n) : Prop :=
  ((v.1.val = 0 ∨ v.1.val + 1 = n) ∧ (v.2.val = 2 ∨ v.2.val + 3 = n)) ∨
  ((v.2.val = 0 ∨ v.2.val + 1 = n) ∧ (v.1.val = 2 ∨ v.1.val + 3 = n))

def Gap {n : Nat} (x y : GridVertex n n) : Prop :=
  (x.1.val = y.1.val ∧ (x.1.val = 0 ∨ x.1.val + 1 = n) ∧
    (x.2.val + 2 = y.2.val ∨ y.2.val + 2 = x.2.val)) ∨
  (x.2.val = y.2.val ∧ (x.2.val = 0 ∨ x.2.val + 1 = n) ∧
    (x.1.val + 2 = y.1.val ∨ y.1.val + 2 = x.1.val))

theorem gap_symm {n : Nat} {x y : GridVertex n n} (h : Gap x y) : Gap y x := by
  unfold Gap at *
  omega

theorem near_not_gap {n : Nat} (hn : 9 ≤ n) {x y : GridVertex n n}
    (hx : Near x) (hy : Near y) : ¬ Gap x y := by
  unfold Near Gap at *
  omega

theorem corner_not_gap_near {n : Nat} (hn : 9 ≤ n) {x y : GridVertex n n}
    (hx : Corner x) (hy : Near y) : ¬ Gap x y := by
  unfold Corner Near Gap at *
  omega

theorem second_not_gap_near {n : Nat} (hn : 9 ≤ n) {x y : GridVertex n n}
    (hx : Second x) (hy : Near y) : ¬ Gap x y := by
  unfold Second Near Gap at *
  omega

theorem near_gap_unique {n : Nat} (hn : 9 ≤ n) {v x y : GridVertex n n}
    (hx : Near x) (hy : Near y) (hvx : Gap v x) (hvy : Gap v y) : x = y := by
  apply Prod.ext <;> apply Fin.ext
  all_goals unfold Near Gap at *; omega

theorem neighbor_near {n : Nat} (hn : 9 ≤ n) {u q : GridVertex n n}
    (hu : IsGridBoundary u) (hq : Near q) (h : (gridGraph n n).Adj u q) :
    Corner u ∨ Second u := by
  simp only [gridGraph, adjacent, Fin.ext_iff] at h
  unfold IsGridBoundary Near Corner Second at *
  omega

theorem second_gap_excludes_near {n : Nat} (hn : 9 ≤ n) {u v q : GridVertex n n}
    (hu : Second u) (hv : ¬ Corner v) (hq : Near q) (huv : Gap u v) :
    ¬ Gap v q := by
  unfold Second Corner Near Gap at *
  omega

theorem adjacent_gap_near_exclusive {n : Nat} (hn : 9 ≤ n)
    {u v q r : GridVertex n n} (h : (gridGraph n n).Adj u v)
    (hq : Near q) (hr : Near r) (huq : Gap u q) : ¬ Gap v r := by
  simp only [gridGraph, adjacent, Fin.ext_iff] at h
  unfold Near Gap at *
  omega

end GridGraphs.BoundarySix
