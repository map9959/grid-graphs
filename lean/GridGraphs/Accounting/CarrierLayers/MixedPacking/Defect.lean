import GridGraphs.Accounting.CarrierLayers.MixedPacking.Rectangle

/-! # One-edge exceptions to rectangular packing

These are separate orientation interfaces, not an allowance of one exception
of each kind. Geometry must identify the boundary edge or the last-step column
and account for every physical edge. No W3 classification is assumed here.
-/

namespace GridGraphs.CarrierLayers.MixedPacking

open Finset

/-- Two scheduled interior rows plus at most one unscheduled boundary edge.
The boundary edge may lie on row H; no interior shadow premise is used for it. -/
theorem two_interior_rods_plus_boundary_edge (Q H r0 r1 : Nat) (hH : 13 ≤ H)
    (hlo : 2 ≤ r0) (hr : r0 ≤ r1) (hhi : r1 < H)
    (E0 E1 Ebottom : Finset Nat) (V : Nat → Finset Nat) (hb : Ebottom.card ≤ 1)
    (hE0 : E0 ⊆ Icc 2 (3 * Q + 1)) (hE1 : E1 ⊆ Icc 2 (3 * Q + 1))
    (hgeom : r1 ≤ r0 + 2 → Disjoint E0 E1)
    (hV : ∀ t ∈ Icc 1 (H - 1), Spaced (V t) ∧ V t ⊆ Icc 3 (3 * Q + 1))
    (hs0 : ∀ t ∈ Icc 1 (H - 1), t ∈ Icc (r0 - 2) (r0 + 1) →
      ∀ v ∈ V t, ∀ x ∈ E0, v + 1 < x ∨ x + 2 < v)
    (hs1 : ∀ t ∈ Icc 1 (H - 1), t ∈ Icc (r1 - 2) (r1 + 1) →
      ∀ v ∈ V t, ∀ x ∈ E1, v + 1 < x ∨ x + 2 < v) :
    E0.card + E1.card + Ebottom.card + (Icc 1 (H - 1)).sum (fun t => (V t).card) ≤
      Q * (H - 1) + 1 := by
  have h := rectangular_three_rod_edge_bound Q H r0 r1 r1 hH hlo hr (le_refl _) hhi
    E0 E1 ∅ V hE0 hE1 (empty_subset _) hgeom
    (fun _ => disjoint_empty_right _) (fun _ => disjoint_empty_right _) hV hs0 hs1 (by simp)
  simp only [card_empty] at h
  omega

/-- Remove only the designated column at the last valid vertical step. -/
def eraseLastVertical (H c : Nat) (V : Nat → Finset Nat) (t : Nat) : Finset Nat :=
  if t = H - 1 then (V t).erase c else V t

/-- Restoring the erased column costs at most one in the entire sum, not
one per step. The statement also holds when the column was absent. -/
theorem sum_vertical_le_eraseLast_add_one (H c : Nat) (V : Nat → Finset Nat) :
    (Icc 1 (H - 1)).sum (fun t => (V t).card) ≤
      (Icc 1 (H - 1)).sum (fun t => (eraseLastVertical H c V t).card) + 1 := by
  have hp : ∀ t ∈ Icc 1 (H - 1), (V t).card ≤
      (eraseLastVertical H c V t).card + (if t = H - 1 then 1 else 0) := by
    intro t _
    by_cases ht : t = H - 1
    · simp only [eraseLastVertical, if_pos ht]
      by_cases hc : c ∈ V t
      · rw [card_erase_of_mem hc]
        omega
      · simp [hc]
    · simp [eraseLastVertical, ht]
  have hsum := sum_le_sum hp
  rw [sum_add_distrib] at hsum
  have hind : (Icc 1 (H - 1)).sum (fun t => if t = H - 1 then 1 else 0) ≤ 1 := by
    simp only [sum_ite_eq']
    split_ifs <;> omega
  omega

/-- Three interior rods with one possibly ineligible vertical column at
the last step. Spacing, eligibility and shadows apply to the erased sets;
the conclusion counts all original vertical edges. -/
theorem rectangle_one_bad_vertical_edge (Q H r0 r1 r2 c : Nat) (hH : 13 ≤ H)
    (hlo : 2 ≤ r0) (hr01 : r0 ≤ r1) (hr12 : r1 ≤ r2) (hhi : r2 < H)
    (E0 E1 E2 : Finset Nat) (V : Nat → Finset Nat)
    (hE0 : E0 ⊆ Icc 2 (3 * Q + 1)) (hE1 : E1 ⊆ Icc 2 (3 * Q + 1))
    (hE2 : E2 ⊆ Icc 2 (3 * Q + 1))
    (hg01 : r1 ≤ r0 + 2 → Disjoint E0 E1) (hg02 : r2 ≤ r0 + 2 → Disjoint E0 E2)
    (hg12 : r2 ≤ r1 + 2 → Disjoint E1 E2)
    (hV : ∀ t ∈ Icc 1 (H - 1), Spaced (eraseLastVertical H c V t) ∧
      eraseLastVertical H c V t ⊆ Icc 3 (3 * Q + 1))
    (hs0 : ∀ t ∈ Icc 1 (H - 1), t ∈ Icc (r0 - 2) (r0 + 1) →
      ∀ v ∈ eraseLastVertical H c V t, ∀ x ∈ E0, v + 1 < x ∨ x + 2 < v)
    (hs1 : ∀ t ∈ Icc 1 (H - 1), t ∈ Icc (r1 - 2) (r1 + 1) →
      ∀ v ∈ eraseLastVertical H c V t, ∀ x ∈ E1, v + 1 < x ∨ x + 2 < v)
    (hs2 : ∀ t ∈ Icc 1 (H - 1), t ∈ Icc (r2 - 2) (r2 + 1) →
      ∀ v ∈ eraseLastVertical H c V t, ∀ x ∈ E2, v + 1 < x ∨ x + 2 < v) :
    E0.card + E1.card + E2.card + (Icc 1 (H - 1)).sum (fun t => (V t).card) ≤
      Q * (H - 1) + 1 := by
  have h := rectangular_three_rod_edge_bound Q H r0 r1 r2 hH hlo hr01 hr12 hhi
    E0 E1 E2 (eraseLastVertical H c V) hE0 hE1 hE2 hg01 hg02 hg12 hV hs0 hs1 hs2
  have hv := sum_vertical_le_eraseLast_add_one H c V
  omega

end GridGraphs.CarrierLayers.MixedPacking
