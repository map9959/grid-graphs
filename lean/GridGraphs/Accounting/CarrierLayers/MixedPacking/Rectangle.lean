import GridGraphs.Accounting.CarrierLayers.MixedPacking.Capacity

/-!
# Height-independent mixed packing

The rectangle has H rows, steps [1,H-1], eligible vertical columns [3,3Q+1],
and horizontal edge left columns [2,3Q+1]. Height and width are independent.
In the proposed enlarged W2 strip, use H=3k and Q=k-1, with physical row+1
as the row coordinate. This file does not derive the W2 strip geometry,
carrier count, or pure/nonpure partition.
-/

namespace GridGraphs.CarrierLayers.MixedPacking

open Finset

/-- Three interior horizontal edge sets are paid by actual vertical deficit
in an independently sized rectangle. Empty edge sets allow fewer rods.
No lower bound on Q is needed; H >= 13 is the schedule hypothesis. -/
theorem rectangular_three_rod_deficit (Q H r0 r1 r2 : Nat) (hH : 13 ≤ H)
    (hlo : 2 ≤ r0) (hr01 : r0 ≤ r1) (hr12 : r1 ≤ r2) (hhi : r2 < H)
    (E0 E1 E2 : Finset Nat) (V : Nat → Finset Nat)
    (hE0 : E0 ⊆ Icc 2 (3 * Q + 1)) (hE1 : E1 ⊆ Icc 2 (3 * Q + 1))
    (hE2 : E2 ⊆ Icc 2 (3 * Q + 1))
    (hgeom01 : r1 ≤ r0 + 2 → Disjoint E0 E1)
    (hgeom02 : r2 ≤ r0 + 2 → Disjoint E0 E2)
    (hgeom12 : r2 ≤ r1 + 2 → Disjoint E1 E2)
    (hV : ∀ t ∈ Icc 1 (H - 1), Spaced (V t) ∧ V t ⊆ Icc 3 (3 * Q + 1))
    (hshadow0 : ∀ t ∈ Icc 1 (H - 1), t ∈ Icc (r0 - 2) (r0 + 1) →
      ∀ v ∈ V t, ∀ x ∈ E0, v + 1 < x ∨ x + 2 < v)
    (hshadow1 : ∀ t ∈ Icc 1 (H - 1), t ∈ Icc (r1 - 2) (r1 + 1) →
      ∀ v ∈ V t, ∀ x ∈ E1, v + 1 < x ∨ x + 2 < v)
    (hshadow2 : ∀ t ∈ Icc 1 (H - 1), t ∈ Icc (r2 - 2) (r2 + 1) →
      ∀ v ∈ V t, ∀ x ∈ E2, v + 1 < x ∨ x + 2 < v) :
    E0.card + E1.card + E2.card ≤ (Icc 1 (H - 1)).sum (fun t => Q - (V t).card) := by
  obtain ⟨T0, T1, T2, hT0, hT1, hT2, hd01, hd02, hd12⟩ :=
    three_rod_schedule H r0 r1 r2 hH hlo hr01 hr12 hhi
  have hcompat (r : Nat) (E T : Finset Nat)
      (hE : E ⊆ Icc 2 (3 * Q + 1)) (hT : T ⊆ Icc (r - 2) (r + 1))
      (hshadow : ∀ t ∈ Icc 1 (H - 1), t ∈ Icc (r - 2) (r + 1) →
        ∀ v ∈ V t, ∀ x ∈ E, v + 1 < x ∨ x + 2 < v) :
      ∀ t ∈ Icc 1 (H - 1), EdgeCompatible Q (V t) (if t ∈ T then E else ∅) := by
    intro t ht
    obtain ⟨hs, hv⟩ := hV t ht
    split_ifs with hm
    · exact ⟨hs, hv, hE, hshadow t ht (hT hm)⟩
    · exact ⟨hs, hv, empty_subset _, by simp⟩
  have hdisjoint (r s : Nat) (E F T U : Finset Nat)
      (hg : s ≤ r + 2 → Disjoint E F) (hd : r + 3 ≤ s → Disjoint T U) :
      ∀ t ∈ T, t ∈ U → Disjoint E F := by
    intro t ht hu
    by_cases hnear : s ≤ r + 2
    · exact hg hnear
    · exact (disjoint_left.mp (hd (by omega)) ht hu).elim
  exact scheduled_edge_charge Q (Icc 1 (H - 1)) T0 T1 T2 E0 E1 E2 V
    hT0.1 hT1.1 hT2.1 hT0.2.2 hT1.2.2 hT2.2.2
    (hcompat r0 E0 T0 hE0 hT0.2.1 hshadow0)
    (hcompat r1 E1 T1 hE1 hT1.2.1 hshadow1)
    (hcompat r2 E2 T2 hE2 hT2.2.1 hshadow2)
    (hdisjoint r0 r1 E0 E1 T0 T1 hgeom01 hd01)
    (hdisjoint r0 r2 E0 E2 T0 T2 hgeom02 hd02)
    (hdisjoint r1 r2 E1 E2 T1 T2 hgeom12 hd12)

/-- Total horizontal plus vertical FF edges in the rectangle are at most
Q(H-1). Every valid step is included, including both boundary steps. -/
theorem rectangular_three_rod_edge_bound (Q H r0 r1 r2 : Nat) (hH : 13 ≤ H)
    (hlo : 2 ≤ r0) (hr01 : r0 ≤ r1) (hr12 : r1 ≤ r2) (hhi : r2 < H)
    (E0 E1 E2 : Finset Nat) (V : Nat → Finset Nat)
    (hE0 : E0 ⊆ Icc 2 (3 * Q + 1)) (hE1 : E1 ⊆ Icc 2 (3 * Q + 1))
    (hE2 : E2 ⊆ Icc 2 (3 * Q + 1))
    (hgeom01 : r1 ≤ r0 + 2 → Disjoint E0 E1)
    (hgeom02 : r2 ≤ r0 + 2 → Disjoint E0 E2)
    (hgeom12 : r2 ≤ r1 + 2 → Disjoint E1 E2)
    (hV : ∀ t ∈ Icc 1 (H - 1), Spaced (V t) ∧ V t ⊆ Icc 3 (3 * Q + 1))
    (hshadow0 : ∀ t ∈ Icc 1 (H - 1), t ∈ Icc (r0 - 2) (r0 + 1) →
      ∀ v ∈ V t, ∀ x ∈ E0, v + 1 < x ∨ x + 2 < v)
    (hshadow1 : ∀ t ∈ Icc 1 (H - 1), t ∈ Icc (r1 - 2) (r1 + 1) →
      ∀ v ∈ V t, ∀ x ∈ E1, v + 1 < x ∨ x + 2 < v)
    (hshadow2 : ∀ t ∈ Icc 1 (H - 1), t ∈ Icc (r2 - 2) (r2 + 1) →
      ∀ v ∈ V t, ∀ x ∈ E2, v + 1 < x ∨ x + 2 < v) :
    E0.card + E1.card + E2.card + (Icc 1 (H - 1)).sum (fun t => (V t).card) ≤
      Q * (H - 1) := by
  have hd := rectangular_three_rod_deficit Q H r0 r1 r2 hH hlo hr01 hr12 hhi
    E0 E1 E2 V hE0 hE1 hE2 hgeom01 hgeom02 hgeom12 hV hshadow0 hshadow1 hshadow2
  have hcap : ∀ t ∈ Icc 1 (H - 1), (V t).card ≤ Q := by
    intro t ht
    have hc := interval_capacity (V t) 3 (3 * Q + 1) (hV t ht).2 (hV t ht).1
    omega
  have hledger :
      (Icc 1 (H - 1)).sum (fun t => (V t).card) +
        (Icc 1 (H - 1)).sum (fun t => Q - (V t).card) = Q * (H - 1) := by
    rw [← sum_add_distrib]
    calc
      _ = (Icc 1 (H - 1)).sum (fun _ => Q) := by
        apply sum_congr rfl
        intro t ht
        have := hcap t ht
        omega
      _ = _ := by simp [Nat.card_Icc, Nat.mul_comm]
  omega

end GridGraphs.CarrierLayers.MixedPacking
