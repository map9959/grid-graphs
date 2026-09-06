import GridGraphs.Accounting.ComponentAttachmentLedger
import GridGraphs.Accounting.PerimeterWaste

/-!
# Phase obstruction for the universal component rank

The tree-component bridge transfers the mod-three cotree identity to the
four-side component rank.  Together with the omitted-perimeter-edge floor,
this excludes rank four in every phase and rank five outside residue one.
-/

namespace GridGraphs

open Finset SimpleGraph

set_option maxHeartbeats 800000

/-- The four-side component rank retains the cotree's mod-three phase. -/
theorem fourSideComponentRank_cotree_mod_three {n : Nat} (hn : 3 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T) :
    (fourSideComponentRank n (supportFinset (gridGraph n n \ T)) + D n n) % 3 = 2 := by
  have hrank := fourSideComponentRank_cotree_support_eq_incidenceWaste_add_two hn hT
  have hmod := square_cotree_incidenceWaste_mod_three (by omega : 2 ≤ n) hT
  omega

/-- Component-resolved strengthening of the constant rank floor: rank four is
impossible for a square grid spanning tree in every side-length phase. -/
theorem five_le_fourSideComponentRank_cotree {n : Nat} (hn : 3 ≤ n)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T) :
    5 ≤ fourSideComponentRank n (supportFinset (gridGraph n n \ T)) := by
  let R := fourSideComponentRank n (supportFinset (gridGraph n n \ T))
  change 5 ≤ R
  have hfour : 4 ≤ R := by
    have hrank := fourSideComponentRank_cotree_support_eq_incidenceWaste_add_two hn hT
    have htwo := two_le_square_cotree_incidenceWaste (by omega : 2 ≤ n) hT
    change R = incidenceWaste (gridGraph n n \ T) + 2 at hrank
    omega
  have hphase := fourSideComponentRank_cotree_mod_three hn hT
  change (R + D n n) % 3 = 2 at hphase
  have hn_decomp : n % 3 + 3 * (n / 3) = n := Nat.mod_add_div n 3
  have hnmod : n % 3 < 3 := Nat.mod_lt n (by omega)
  interval_cases hres : n % 3
  · have hD : D n n % 3 = 2 := by
      have hnm1 : (n - 1) % 3 = 2 := by omega
      simp [D, Nat.mul_mod, hnm1]
    rw [Nat.add_mod, hD] at hphase
    omega
  · have hD : D n n % 3 = 0 := by
      have hnm1 : (n - 1) % 3 = 0 := by omega
      simp [D, Nat.mul_mod, hnm1]
    rw [Nat.add_mod, hD] at hphase
    omega
  · have hD : D n n % 3 = 2 := by
      have hnm1 : (n - 1) % 3 = 1 := by omega
      simp [D, Nat.mul_mod, hnm1]
    rw [Nat.add_mod, hD] at hphase
    omega

/-- In the zero and two phases, the same component/congruence obstruction
excludes rank five as well. -/
theorem six_le_fourSideComponentRank_cotree_of_mod_ne_one {n : Nat}
    (hn : 3 ≤ n) (hnphase : n % 3 ≠ 1)
    {T : SimpleGraph (GridVertex n n)} [DecidableRel T.Adj]
    (hT : IsSpanningSubtree (gridGraph n n) T) :
    6 ≤ fourSideComponentRank n (supportFinset (gridGraph n n \ T)) := by
  let R := fourSideComponentRank n (supportFinset (gridGraph n n \ T))
  change 6 ≤ R
  have hfive : 5 ≤ R := by
    simpa only [R] using five_le_fourSideComponentRank_cotree hn hT
  have hphase := fourSideComponentRank_cotree_mod_three hn hT
  change (R + D n n) % 3 = 2 at hphase
  have hn_decomp : n % 3 + 3 * (n / 3) = n := Nat.mod_add_div n 3
  have hnmod : n % 3 < 3 := Nat.mod_lt n (by omega)
  interval_cases hres : n % 3
  · have hD : D n n % 3 = 2 := by
      have hnm1 : (n - 1) % 3 = 2 := by omega
      simp [D, Nat.mul_mod, hnm1]
    rw [Nat.add_mod, hD] at hphase
    omega
  · exact (hnphase rfl).elim
  · have hD : D n n % 3 = 2 := by
      have hnm1 : (n - 1) % 3 = 1 := by omega
      simp [D, Nat.mul_mod, hnm1]
    rw [Nat.add_mod, hD] at hphase
    omega

end GridGraphs
