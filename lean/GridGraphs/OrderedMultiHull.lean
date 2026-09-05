import Mathlib.Data.Fintype.Fin

/-!
# Ordered multi-hull depth

Laminarity alone does not bound the number of occurrence hulls crossing one
frontier cut.  This module records the elementary obstruction independently of
any particular frontier encoding.
-/

namespace GridGraphs

open Finset

/-- A nonempty interval of positions in a linearly ordered frontier. -/
structure OrderedHull where
  left : Nat
  right : Nat
  left_lt_right : left < right

/-- A hull is active at a cut when it has occurrences on both sides. -/
def OrderedHull.CrossesCut (h : OrderedHull) (cut : Nat) : Prop :=
  h.left ≤ cut ∧ cut < h.right

/-- Two hulls are laminar when they are disjoint or one contains the other. -/
def OrderedHull.Laminar (h g : OrderedHull) : Prop :=
  h.right ≤ g.left ∨ g.right ≤ h.left ∨
    (h.left ≤ g.left ∧ g.right ≤ h.right) ∨
    (g.left ≤ h.left ∧ h.right ≤ g.right)

/-- Number of occurrence hulls simultaneously active at one cut. -/
noncomputable def orderedHullDepth {I : Type*} [Fintype I]
    (hulls : I → OrderedHull) (cut : Nat) : Nat := by
  classical
  exact (Finset.univ.filter fun i => (hulls i).CrossesCut cut).card

/-- `k` properly nested hulls around the middle cut. -/
def concentricOrderedHull (k : Nat) (i : Fin k) : OrderedHull where
  left := i.val
  right := 2 * k - i.val
  left_lt_right := by have := i.isLt; omega

/-- The concentric family is pairwise laminar. -/
theorem concentricOrderedHull_laminar (k : Nat) (i j : Fin k) :
    (concentricOrderedHull k i).Laminar (concentricOrderedHull k j) := by
  by_cases hij : i.val ≤ j.val
  · right
    right
    left
    refine ⟨hij, ?_⟩
    change 2 * k - j.val ≤ 2 * k - i.val
    omega
  · right
    right
    right
    refine ⟨?_, ?_⟩
    · change j.val ≤ i.val
      omega
    change 2 * k - i.val ≤ 2 * k - j.val
    omega

/-- Every concentric hull crosses the middle cut. -/
theorem concentricOrderedHull_crosses_middle (k : Nat) (i : Fin k) :
    (concentricOrderedHull k i).CrossesCut k := by
  have := i.isLt
  simp only [OrderedHull.CrossesCut, concentricOrderedHull]
  omega

/-- Laminar ordered hull families have unbounded simultaneous depth. -/
theorem orderedHullDepth_concentric (k : Nat) :
    orderedHullDepth (concentricOrderedHull k) k = k := by
  classical
  rw [orderedHullDepth]
  have hall :
      (Finset.univ.filter fun i : Fin k =>
        (concentricOrderedHull k i).CrossesCut k) = Finset.univ := by
    ext i
    simp [concentricOrderedHull_crosses_middle]
  rw [hall, Finset.card_univ, Fintype.card_fin]

end GridGraphs
