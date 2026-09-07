import GridGraphs.Accounting.BoundaryFive.Rootless.Geometry

/-!
# Reciprocal-root exclusion on the actual deep square

This proves a deep-square exclusion, not the ambient boundary-five reduction.
The hypotheses are acyclicity, actual boundary-root uniqueness, k actual
induced components, and two opposite-side roots in the same row. No assumed
lengths, deficits, carrier inventory, or ambient c=1 premise occur.
-/

namespace GridGraphs.BoundaryFive.Rootless

open Finset SimpleGraph

/-- The reciprocal pair saves m against the strict (m-1)-per-carrier
baseline. No charge from the other two corner roots is needed. -/
theorem reciprocal_card_bound {m : Nat} (hm : 2 ≤ m)
    (F : Finset (GridVertex m m))
    (hacyc : (forcedEdgeGraph (gridGraph m m) (↑F : Set _)).IsAcyclic)
    (hroot : UniqueBoundaryRoots (m := m) (↑F : Set _))
    (u v : (↑F : Set (GridVertex m m)))
    (hu0 : u.1.2.val = 0) (hvm : v.1.2.val + 1 = m)
    (hrow : u.1.1 = v.1.1) :
    F.card + m ≤ (m - 1) *
      Fintype.card ((gridGraph m m).induce (↑F : Set _)).ConnectedComponent := by
  classical
  let G := (gridGraph m m).induce (↑F : Set _)
  let C := G.connectedComponentMk u
  let D := G.connectedComponentMk v
  obtain ⟨hne, hpair⟩ := reciprocal_component_cap hm hacyc hroot C D u v
    (by simp [C, G, ConnectedComponent.mem_supp_iff])
    (by simp [D, G, ConnectedComponent.mem_supp_iff]) hu0 hvm hrow
  simp only [Set.ncard_eq_toFinset_card'] at hpair
  let S : Finset G.ConnectedComponent := {C, D}
  have hScard : S.card = 2 := card_pair hne
  have hSmass : (∑ E ∈ S, E.supp.toFinset.card) ≤ m - 2 := by
    simpa [S, hne] using hpair
  have hcover : (univ.biUnion fun E : G.ConnectedComponent => E.supp.toFinset) =
      (univ : Finset (↑F : Set (GridVertex m m))) := by
    ext w
    simp [ConnectedComponent.mem_supp_iff]
  have htotal : F.card = ∑ E : G.ConnectedComponent, E.supp.toFinset.card := by
    have hd : (↑(univ : Finset G.ConnectedComponent) : Set G.ConnectedComponent).Pairwise
        (fun C D => Disjoint C.supp.toFinset D.supp.toFinset) := by
      intro C _ D _ hne
      simpa using pairwise_disjoint_supp_connectedComponent G hne
    rw [← card_biUnion hd, hcover]
    simp
  have hrest : (∑ E ∈ univ \ S, E.supp.toFinset.card) ≤
      (m - 1) * (Fintype.card G.ConnectedComponent - 2) := by
    calc
      _ ≤ ∑ _E ∈ univ \ S, (m - 1) := sum_le_sum (fun E _ => by
        simpa only [Set.ncard_eq_toFinset_card'] using strict_carrier_cap hm hacyc hroot E)
      _ = _ := by simp [card_sdiff_of_subset (subset_univ S), hScard, Nat.mul_comm]
  have hsplit := sum_sdiff (subset_univ S)
    (f := fun E : G.ConnectedComponent => E.supp.toFinset.card)
  rw [← htotal] at hsplit
  have htwo : 2 ≤ Fintype.card G.ConnectedComponent := by
    have := card_le_card (subset_univ S)
    simpa only [hScard, card_univ] using this
  have hmul := congrArg (fun q => (m - 1) * q) (Nat.sub_add_cancel htwo)
  have hm1 : m - 1 + 1 = m := by omega
  have hm2 : m - 2 + 2 = m := by omega
  change F.card + m ≤ (m - 1) * Fintype.card G.ConnectedComponent
  nlinarith

/-- At m=3k-2 and q=k, a reciprocal pair lies strictly below even the
stable ambient target after adding the exact outer mass 12k-1. In particular
it cannot attain the current k=1 mod 3 endpoint. -/
theorem reciprocal_below_stable {k : Nat} (hk : 2 ≤ k)
    (F : Finset (GridVertex (3 * k - 2) (3 * k - 2)))
    (hacyc : (forcedEdgeGraph (gridGraph (3 * k - 2) (3 * k - 2))
      (↑F : Set _)).IsAcyclic)
    (hroot : UniqueBoundaryRoots (m := 3 * k - 2) (↑F : Set _))
    (hq : Fintype.card ((gridGraph (3 * k - 2) (3 * k - 2)).induce
      (↑F : Set _)).ConnectedComponent = k)
    (u v : (↑F : Set (GridVertex (3 * k - 2) (3 * k - 2))))
    (hu0 : u.1.2.val = 0) (hvm : v.1.2.val + 1 = 3 * k - 2)
    (hrow : u.1.1 = v.1.1) :
    F.card + (12 * k - 1) < 3 * k ^ 2 + 7 * k := by
  have h := reciprocal_card_bound (by omega) F hacyc hroot u v hu0 hvm hrow
  rw [hq] at h
  have hm : 3 * k - 2 + 2 = 3 * k := by omega
  have hm' : 3 * k - 2 - 1 + 3 = 3 * k := by omega
  have ho : 12 * k - 1 + 1 = 12 * k := by omega
  nlinarith

/-- The directed four-cycle has no reciprocal edge exactly when all arrows
are clockwise or all are counterclockwise. This is a 16-case finite check,
not a grid search or a claim that either cyclic pattern is feasible. -/
theorem no_reciprocal_iff_cyclic (d : Fin 4 → Bool) :
    (∀ i : Fin 4, ¬ (d i = true ∧ d (i + 1) = false)) ↔
      (∀ i, d i = true) ∨ (∀ i, d i = false) := by
  revert d
  decide

end GridGraphs.BoundaryFive.Rootless
